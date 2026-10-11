//===================================================================== //
// TIMING COMPARISON:
//
//      R = 2  POWER-RESIDUE PRF
//      R = 4  POWER-RESIDUE PRF
//      R = 8  POWER-RESIDUE PRF
//
// SAME:
//      p, h, d, coset, secret
//
// IMPORTANT OPTIMISATIONS:
//
//  1. Search B directly in
//
//         h = B*m + tail
//
//     minimizing
//
//         m + tail + rho*B.
//
//     This avoids a huge tail.
//
//  2. Blocked product trees.
//
//  3. One Q0 table only.
//
//  4. NO Q1 table.
//
//     C1 is evaluated by Horner only on the surviving bucket.
//
//  5. zeta^ell is obtained from a tiny lookup table.
//
//  6. All transcript statistics are generated algebraically by default.
//     Set UseRealOracle := true for actual h-query simulation.
// ===================================================================== //

RR := RealField(12);

///////////////////////////////////////////////////////////////////////////
// PARAMETERS
///////////////////////////////////////////////////////////////////////////

p := 2^40 - 87;
assert IsPrime(p);

Fp := GF(p);
g := PrimitiveElement(Fp);

h := 10269667;

assert (p-1) mod h eq 0;

d := (p-1) div h;

assert d eq 107064;
assert d mod 8 eq 0;

omega := g^h;
Hgen := g^d;

assert Order(omega) eq d;
assert Order(Hgen) eq h;

cosetIndex := 1;

secretExponent := Random(1,p-1); secretExponent;
secret := g^secretExponent;

trueEll := secretExponent mod d;

assert secret^h eq omega^trueEll;

///////////////////////////////////////////////////////////////////////////
// OPTIONS
///////////////////////////////////////////////////////////////////////////

// false = use exact identities to generate transcript statistics.
//
// true = perform all h oracle evaluations independently for R=2,4,8.
//
// WARNING: true means about 30 million simulated oracle evaluations.
UseRealOracle := false;

// Product/evaluation leaf size.
LeafSize := 32;

// Search number of full BSGS blocks B in [1..MaxBlocks].
MaxBlocks := 100;

P<X> := PolynomialRing(Fp);


///////////////////////////////////////////////////////////////////////////
// TIMING
///////////////////////////////////////////////////////////////////////////

procedure PrintTime(label,t)
    printf "%-42o : %o seconds\n",label,RR!t;
end procedure;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 1. OPTIMAL BLOCK CHOICE
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////
//
// Instead of:
//
//     m ~ sqrt(h*rho)
//
// followed by floor(h/m),
// which can produce a huge tail,
// search directly over B:
//
//     m    = floor(h/B)
//     tail = h-B*m.
//
// Model:
//
//     m + tail + rho*B.
//
// This gives for the present parameters:
//
//   R=2 : B=14, m=733547, tail=9
//   R=4 : B=20, m=513483, tail=7
//   R=8 : B=28, m=366773, tail=23
//
///////////////////////////////////////////////////////////////////////////

function SelectOptimalBlock(h,rho,MaxBlocks)

    bestCost := 10^30;
    bestB := 0;
    bestM := 0;
    bestTail := 0;

    for B in [1..MaxBlocks] do

        m := h div B;

        if m eq 0 then
            continue;
        end if;

        tail := h-B*m;

        cost :=
            m
            +
            tail
            +
            rho*B;

        if cost lt bestCost then

            bestCost := cost;
            bestB := B;
            bestM := m;
            bestTail := tail;

        end if;

    end for;

    return
        bestM,
        bestB,
        bestTail,
        bestCost;

end function;


///////////////////////////////////////////////////////////////////////////
// Show selected parameters immediately.
///////////////////////////////////////////////////////////////////////////

print "============================================================";
print "OPTIMAL BSGS PARAMETERS";
print "============================================================";

for R in [2,4,8] do

    rho := d div R;

    m,B,tail,cost :=
        SelectOptimalBlock(
            h,
            rho,
            MaxBlocks
        );

    print "";
    print "R =",R;
    print "rho =",rho;
    print "B =",B;
    print "m =",m;
    print "tail =",tail;
    print "model cost =",cost;

    assert h eq B*m+tail;

end for;

print "";


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 2. CONSECUTIVE PRODUCT -- BLOCKED
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function ConsecutiveProductPolynomial(
    PR,start,n,LeafSize
)

    X := PR.1;

    if n eq 0 then
        return PR!1;
    end if;

    Leaves := [];

    numberLeaves :=
        Ceiling(n/LeafSize);

    for b in [0..numberLeaves-1] do

        lo := b*LeafSize;
        hi := Minimum(n-1,lo+LeafSize-1);

        f := PR!1;

        for i in [lo..hi] do
            f *:= X + Fp!(start+i);
        end for;

        Append(~Leaves,f);

    end for;

    Level := Leaves;

    while #Level gt 1 do

        Next := [];

        i := 1;

        while i le #Level do

            if i lt #Level then

                Append(
                    ~Next,
                    Level[i]*Level[i+1]
                );

            else

                Append(
                    ~Next,
                    Level[i]
                );

            end if;

            i +:= 2;

        end while;

        Level := Next;

    end while;

    return Level[1];

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 3. BLOCKED PRODUCT TREE
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function BuildPointProductTree(
    PR,
    Points,
    LeafSize
)

    X := PR.1;

    n := #Points;
    assert n gt 0;

    Leaves := [];

    numberLeaves :=
        Ceiling(n/LeafSize);

    for b in [0..numberLeaves-1] do

        lo := b*LeafSize+1;
        hi := Minimum(n,lo+LeafSize-1);

        f := PR!1;

        for i in [lo..hi] do
            f *:= X-Points[i];
        end for;

        Append(~Leaves,f);

    end for;

    Tree := [Leaves];
    Level := Leaves;

    while #Level gt 1 do

        Next := [];

        i := 1;

        while i le #Level do

            if i lt #Level then

                Append(
                    ~Next,
                    Level[i]*Level[i+1]
                );

            else

                Append(
                    ~Next,
                    Level[i]
                );

            end if;

            i +:= 2;

        end while;

        Append(~Tree,Next);

        Level := Next;

    end while;

    return Tree;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 4. EVALUATE WITH PRODUCT TREE
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function EvaluateWithProductTree(
    f,
    Points,
    Tree,
    LeafSize
)

    n := #Points;

    numberLevels := #Tree;

    root :=
        Tree[numberLevels][1];

    if Degree(f) lt Degree(root) then

        RemLevel := [f];

    else

        RemLevel := [f mod root];

    end if;


    ///////////////////////////////////////////////////////////////////////
    // Descend remainder tree
    ///////////////////////////////////////////////////////////////////////

    if numberLevels gt 1 then

        for lev in Reverse([1..numberLevels-1]) do

            ChildPolys :=
                Tree[lev];

            NewRem := [];

            for i in [1..#ChildPolys] do

                parentIndex :=
                    (i+1) div 2;

                parentRem :=
                    RemLevel[parentIndex];

                childPoly :=
                    ChildPolys[i];

                if Degree(parentRem)
                   lt Degree(childPoly)
                then

                    rr := parentRem;

                else

                    rr :=
                        parentRem mod childPoly;

                end if;

                Append(~NewRem,rr);

            end for;

            RemLevel := NewRem;

        end for;

    end if;


    ///////////////////////////////////////////////////////////////////////
    // Evaluate inside each small leaf.
    ///////////////////////////////////////////////////////////////////////

    Values :=
        [Fp!0 : i in [1..n]];

    numberLeaves :=
        #RemLevel;

    for b in [0..numberLeaves-1] do

        lo := b*LeafSize+1;
        hi := Minimum(n,lo+LeafSize-1);

        rr :=
            RemLevel[b+1];

        for i in [lo..hi] do

            Values[i] :=
                Evaluate(
                    rr,
                    Points[i]
                );

        end for;

    end for;

    return Values;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 5. BATCH INVERSION
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function BatchInverse(values)

    n := #values;

    if n eq 0 then
        return [];
    end if;

    assert &and[
        x ne 0 : x in values
    ];

    prefix :=
        [Fp!1 : i in [1..n]];

    prefix[1] :=
        values[1];

    for i in [2..n] do

        prefix[i] :=
            prefix[i-1]*values[i];

    end for;

    inverses :=
        [Fp!0 : i in [1..n]];

    running :=
        1/prefix[n];

    for i in [n..2 by -1] do

        inverses[i] :=
            running*prefix[i-1];

        running *:=
            values[i];

    end for;

    inverses[1] :=
        running;

    return inverses;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 6. HORNER
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function HornerEvaluate(coefficients,x)

    value :=
        coefficients[#coefficients];

    for i in [#coefficients-1..1 by -1] do

        value :=
            value*x
            +
            coefficients[i];

    end for;

    return value;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 7. EXCEPTIONAL BRANCH
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function DeltaBranch(j,ell,h,d)

    if IsEven(h) then

        return
            ((ell-j) mod d eq 0)
            select 1
            else 0;

    end if;

    return
        ((ell+d div 2-j) mod d eq 0)
        select 1
        else 0;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 8. COEFFICIENT CONSTRUCTION FOR ONE R
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////
//
// M_R = (p-1)/R = rho*h
//
// Need:
//
//      A_q = binom(M_R,qh)
//
//      C0_R(T)
//        = h sum A_q T^q.
//
// and
//
//      C1_R(T)
//        = h sum binom(M_R,qh-1)T^q.
//
// Block products:
//
//      V_q
//       = prod_{i=1}^h(qh+i)
//       = P_h(qh+1).
//
///////////////////////////////////////////////////////////////////////////

function BuildCoefficientsOptimised(R)

    assert d mod R eq 0;

    rho :=
        d div R;

    M :=
        (p-1) div R;

    assert M eq rho*h;


    ///////////////////////////////////////////////////////////////////////
    // OPTIMAL BLOCK CHOICE
    ///////////////////////////////////////////////////////////////////////

    m,B,tail,modelCost :=
        SelectOptimalBlock(
            h,
            rho,
            MaxBlocks
        );

    assert h eq B*m+tail;


    ///////////////////////////////////////////////////////////////////////
    // Build baby polynomial
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    Pm :=
        ConsecutiveProductPolynomial(
            P,
            0,
            m,
            LeafSize
        );

    timePm :=
        Cputime(t0);

    assert Degree(Pm) eq m;


    ///////////////////////////////////////////////////////////////////////
    // Tiny tail
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    Ptail :=
        ConsecutiveProductPolynomial(
            P,
            0,
            tail,
            LeafSize
        );

    timeTail :=
        Cputime(t0);


    ///////////////////////////////////////////////////////////////////////
    // BSGS evaluation points
    //
    // rho * B points
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    MainPoints := [];

    for q in [0..rho-1] do

        base :=
            q*h+1;

        for b in [0..B-1] do

            Append(
                ~MainPoints,
                Fp!(
                    base+b*m
                )
            );

        end for;

    end for;

    timePoints :=
        Cputime(t0);

    assert #MainPoints eq rho*B;


    ///////////////////////////////////////////////////////////////////////
    // Product tree
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    MainTree :=
        BuildPointProductTree(
            P,
            MainPoints,
            LeafSize
        );

    timeTree :=
        Cputime(t0);


    ///////////////////////////////////////////////////////////////////////
    // Global multipoint evaluation
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    MainValues :=
        EvaluateWithProductTree(
            Pm,
            MainPoints,
            MainTree,
            LeafSize
        );

    timeEval :=
        Cputime(t0);

    assert #MainValues
           eq #MainPoints;


    ///////////////////////////////////////////////////////////////////////
    // Recover V_q
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    V :=
        [Fp!0 : q in [0..rho-1]];

    for q in [0..rho-1] do

        value :=
            Fp!1;

        offset :=
            q*B;

        for b in [0..B-1] do

            value *:=
                MainValues[
                    offset+b+1
                ];

        end for;

        if tail gt 0 then

            tailPoint :=
                Fp!(
                    q*h
                    + 1
                    + B*m
                );

            value *:=
                Evaluate(
                    Ptail,
                    tailPoint
                );

        end if;

        assert value ne 0;

        V[q+1] :=
            value;

    end for;

    timeV :=
        Cputime(t0);


    ///////////////////////////////////////////////////////////////////////
    // Batch invert V
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    Vinv :=
        BatchInverse(V);

    timeInv :=
        Cputime(t0);


    ///////////////////////////////////////////////////////////////////////
    // A_q recurrence
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    A :=
        [Fp!0 : q in [0..rho]];

    A[1] :=
        Fp!1;

    for q in [0..rho-1] do

        A[q+2] :=
            A[q+1]
            *
            V[rho-q]
            *
            Vinv[q+1];

    end for;

    assert A[rho+1] eq 1;

    timeA :=
        Cputime(t0);


    ///////////////////////////////////////////////////////////////////////
    // C0
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    C0 :=
        [
            Fp!h*A[q+1]
            :
            q in [0..rho]
        ];

    timeC0 :=
        Cputime(t0);


    ///////////////////////////////////////////////////////////////////////
    // C1
    ///////////////////////////////////////////////////////////////////////

    t0 := Cputime();

    C1 :=
        [Fp!0 : q in [0..rho]];

    denominators :=
        [
            Fp!(M-q*h+1)
            :
            q in [1..rho]
        ];

    inverseDenominators :=
        BatchInverse(
            denominators
        );

    for q in [1..rho] do

        C1[q+1] :=
            Fp!h
            *
            Fp!(q*h)
            *
            A[q+1]
            *
            inverseDenominators[q];

    end for;

    timeC1 :=
        Cputime(t0);


    ///////////////////////////////////////////////////////////////////////
    // Total coefficient time
    ///////////////////////////////////////////////////////////////////////

    coeffTotal :=
        timePm
        +
        timeTail
        +
        timePoints
        +
        timeTree
        +
        timeEval
        +
        timeV
        +
        timeInv
        +
        timeA
        +
        timeC0
        +
        timeC1;


    return
        C0,
        C1,
        rho,
        m,
        B,
        tail,
        modelCost,
        coeffTotal,
        timePm,
        timeTail,
        timePoints,
        timeTree,
        timeEval,
        timeV,
        timeInv,
        timeA,
        timeC0,
        timeC1;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 9. Q0 TABLE
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function BuildQ0TableOptimised(
    C0,
    omega,
    d
)

    poly :=
        P!C0;

    points := [];

    invomega :=
        1/omega;

    z :=
        Fp!1;

    for u in [0..d-1] do

        Append(~points,z);

        z *:=
            invomega;

    end for;

    assert z eq 1;

    tree :=
        BuildPointProductTree(
            P,
            points,
            LeafSize
        );

    values :=
        EvaluateWithProductTree(
            poly,
            points,
            tree,
            LeafSize
        );

    assert #values eq d;

    return values;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 10. ALGEBRAIC TRANSCRIPT
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function AlgebraicTranscript(
    R,
    C1,
    Q0
)

    zeta :=
        g^((p-1) div R);

    zetaPowers :=
        [
            zeta^k
            :
            k in [0..R-1]
        ];

    delta :=
        DeltaBranch(
            cosetIndex,
            trueEll,
            h,
            d
        );

    shifted :=
        ((trueEll-cosetIndex)
         mod d)+1;

    q0 :=
        Q0[shifted];

    char :=
        zetaPowers[
            (trueEll mod R)+1
        ];

    observedN0 :=
        char*q0
        +
        Fp!delta;

    x :=
        omega^(
            (cosetIndex-trueEll)
            mod d
        );

    q1 :=
        HornerEvaluate(
            C1,
            x
        );

    observedN1 :=
        secret
        *
        (
            char*q1
            -
            Fp!delta
        );

    return
        observedN0,
        observedN1;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 11. REAL R-POWER TRANSCRIPT
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function RealTranscript(R)

    M :=
        (p-1) div R;

    observedN0 :=
        Fp!0;

    observedN1 :=
        Fp!0;

    first :=
        g^cosetIndex;

    a :=
        first;

    for counter in [1..h] do

        y :=
            secret+a;

        if y eq 0 then

            value :=
                Fp!1;

        else

            value :=
                y^M;

        end if;

        observedN0 +:=
            value;

        observedN1 +:=
            a*value;

        a *:=
            Hgen;

    end for;

    assert a eq first;

    return
        observedN0,
        observedN1;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 12. FILTER
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function FilterCandidates(
    R,
    Q0,
    observedN0
)

    zeta :=
        g^((p-1) div R);

    powers :=
        [
            zeta^k
            :
            k in [0..R-1]
        ];

    bucket := [];

    for ell in [0..d-1] do

        shifted :=
            ((ell-cosetIndex)
             mod d)+1;

        delta :=
            DeltaBranch(
                cosetIndex,
                ell,
                h,
                d
            );

        char :=
            powers[
                (ell mod R)+1
            ];

        predicted :=
            char
            *
            Q0[shifted]
            +
            Fp!delta;

        if predicted
           eq observedN0
        then

            Append(
                ~bucket,
                ell
            );

        end if;

    end for;

    return bucket;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 13. FIRST-MOMENT RECOVERY
//
// NO Q1 TABLE.
//
// Horner only for |bucket| candidates.
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function RecoverCandidates(
    R,
    C1,
    bucket,
    observedN1
)

    zeta :=
        g^((p-1) div R);

    powers :=
        [
            zeta^k
            :
            k in [0..R-1]
        ];

    candidates := [];
    candidateExponents := [];
    degenerates := [];

    for ell in bucket do

        x :=
            omega^(
                (cosetIndex-ell)
                mod d
            );

        q1 :=
            HornerEvaluate(
                C1,
                x
            );

        delta :=
            DeltaBranch(
                cosetIndex,
                ell,
                h,
                d
            );

        char :=
            powers[
                (ell mod R)+1
            ];

        denominator :=
            char*q1
            -
            Fp!delta;

        if denominator eq 0 then

            if observedN1 eq 0 then
                Append(
                    ~degenerates,
                    ell
                );
            end if;

            continue;

        end if;

        candidate :=
            observedN1
            /
            denominator;

        if candidate ne 0
           and
           candidate^h
           eq omega^ell
        then

            Append(
                ~candidates,
                candidate
            );

            Append(
                ~candidateExponents,
                ell
            );

        end if;

    end for;

    return
        candidates,
        candidateExponents,
        degenerates;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 14. RUN ONE OPTIMISED ATTACK
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

function RunOptimisedAttack(R)

    print "";
    print "============================================================";
    printf "%o-POWER-RESIDUE PRF ATTACK\n",R;
    print "============================================================";

    rhoExpected :=
        d div R;

    /////////////////////////////////////////////////////////////////
    // COEFFICIENT PREPROCESSING
    /////////////////////////////////////////////////////////////////

    coeffStart :=
        Cputime();

    C0,
    C1,
    rho,
    m,
    B,
    tail,
    modelCost,
    coeffInternal,
    tPm,
    tTail,
    tPoints,
    tTree,
    tEval,
    tV,
    tInv,
    tA,
    tC0,
    tC1 :=
        BuildCoefficientsOptimised(R);

    coefficientTime :=
        Cputime(coeffStart);

    assert rho eq rhoExpected;


    /////////////////////////////////////////////////////////////////
    // Q0 TABLE
    /////////////////////////////////////////////////////////////////

    q0Start :=
        Cputime();

    Q0 :=
        BuildQ0TableOptimised(
            C0,
            omega,
            d
        );

    q0Time :=
        Cputime(q0Start);


    /////////////////////////////////////////////////////////////////
    // Transcript
    /////////////////////////////////////////////////////////////////

    transcriptStart :=
        Cputime();

    if UseRealOracle then

        observedN0,
        observedN1 :=
            RealTranscript(R);

    else

        observedN0,
        observedN1 :=
            AlgebraicTranscript(
                R,
                C1,
                Q0
            );

    end if;

    transcriptTime :=
        Cputime(transcriptStart);


    /////////////////////////////////////////////////////////////////
    // Filter
    /////////////////////////////////////////////////////////////////

    filterStart :=
        Cputime();

    bucket :=
        FilterCandidates(
            R,
            Q0,
            observedN0
        );

    filterTime :=
        Cputime(filterStart);

    assert trueEll in bucket;


    /////////////////////////////////////////////////////////////////
    // First-moment recovery
    /////////////////////////////////////////////////////////////////

    recoveryStart :=
        Cputime();

    candidates,
    candidateExponents,
    degenerates :=
        RecoverCandidates(
            R,
            C1,
            bucket,
            observedN1
        );

    recoveryTime :=
        Cputime(recoveryStart);


    /////////////////////////////////////////////////////////////////
    // Correctness
    /////////////////////////////////////////////////////////////////

    trueRecovered :=
        secret in candidates;

    if not trueRecovered then

        for ell in degenerates do

            if secret^h
               eq omega^ell
            then

                trueRecovered :=
                    true;

                break;

            end if;

        end for;

    end if;

    assert trueRecovered;


    /////////////////////////////////////////////////////////////////
    // Totals
    /////////////////////////////////////////////////////////////////

    preprocessingTime :=
        coefficientTime
        +
        q0Time;

    postTranscriptTime :=
        filterTime
        +
        recoveryTime;

    totalMeasured :=
        preprocessingTime
        +
        transcriptTime
        +
        postTranscriptTime;


    /////////////////////////////////////////////////////////////////
    // Detailed output
    /////////////////////////////////////////////////////////////////

    print "";
    print "BSGS";
    print "------------------------------------------------------------";

    print "rho                         =",rho;
    print "number full blocks B        =",B;
    print "baby polynomial degree m    =",m;
    print "tail                         =",tail;
    print "BSGS evaluation points      =",rho*B;
    print "model cost                  =",modelCost;

    print "";

    PrintTime(
        "baby polynomial",
        tPm
    );

    PrintTime(
        "tail polynomial",
        tTail
    );

    PrintTime(
        "evaluation-point generation",
        tPoints
    );

    PrintTime(
        "BSGS product tree",
        tTree
    );

    PrintTime(
        "BSGS multipoint evaluation",
        tEval
    );

    PrintTime(
        "recover V_q",
        tV
    );

    PrintTime(
        "batch inversion V_q",
        tInv
    );

    PrintTime(
        "binomial recurrence",
        tA
    );

    PrintTime(
        "construct C0",
        tC0
    );

    PrintTime(
        "construct C1",
        tC1
    );


    print "";
    print "ATTACK";
    print "------------------------------------------------------------";

    print "C0 degree                   =",rho;
    print "C1 degree                   =",rho;
    print "bucket                      =",bucket;
    print "bucket size                 =",#bucket;

    print "candidate exponents         =",
        candidateExponents;

    print "candidate count             =",
        #candidates;

    print "true secret recovered       =",
        trueRecovered;


    print "";
    print "TIMINGS";
    print "------------------------------------------------------------";

    PrintTime(
        "Coefficient construction",
        coefficientTime
    );

    PrintTime(
        "Q0 table evaluation",
        q0Time
    );

    PrintTime(
        "TOTAL PREPROCESSING",
        preprocessingTime
    );

    PrintTime(
        "Transcript",
        transcriptTime
    );

    PrintTime(
        "Zeroth-moment filter",
        filterTime
    );

    PrintTime(
        "First-moment recovery",
        recoveryTime
    );

    PrintTime(
        "POST-TRANSCRIPT",
        postTranscriptTime
    );

    PrintTime(
        "TOTAL MEASURED",
        totalMeasured
    );


    /////////////////////////////////////////////////////////////////
    // Compact result tuple
    /////////////////////////////////////////////////////////////////

    return
        <
            R,                  // 1
            rho,                // 2
            m,                  // 3
            B,                  // 4
            tail,               // 5
            rho*B,              // 6
            #bucket,            // 7
            #candidates,        // 8
            coefficientTime,    // 9
            q0Time,             // 10
            preprocessingTime,  // 11
            transcriptTime,     // 12
            filterTime,         // 13
            recoveryTime,       // 14
            postTranscriptTime, // 15
            totalMeasured       // 16
        >;

end function;


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 15. RUN ATTACKS
//
// Run higher degree first.
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

print "";
print "============================================================";
print "COMMON PARAMETERS";
print "============================================================";

print "p =",p;
print "h =",h;
print "d =",d;
print "coset j =",cosetIndex;

print "";

print "secret =",secret;
print "true ell =",trueEll;

print "";

print "UseRealOracle =",UseRealOracle;

print "";


Result8 :=
    RunOptimisedAttack(8);

Result4 :=
    RunOptimisedAttack(4);

Result2 :=
    RunOptimisedAttack(2);


///////////////////////////////////////////////////////////////////////////
// ===================================================================== //
// 16. FINAL COMPARISON
// ===================================================================== //
///////////////////////////////////////////////////////////////////////////

Results :=
    [
        Result2,
        Result4,
        Result8
    ];

print "";
print "==============================================================================================================";
print "FINAL COMPARISON";
print "==============================================================================================================";

printf
"%4o %8o %9o %5o %7o %10o %8o %12o %12o %12o\n",
"R",
"degree",
"baby m",
"B",
"tail",
"eval pts",
"bucket",
"T_coeff",
"T_Q0",
"T_pre";

print "--------------------------------------------------------------------------------------------------------------";

for A in Results do

    printf
    "%4o %8o %9o %5o %7o %10o %8o %12.3o %12.3o %12.3o\n",

        A[1],
        A[2],
        A[3],
        A[4],
        A[5],
        A[6],
        A[7],

        RR!A[9],
        RR!A[10],
        RR!A[11];

end for;

print "==============================================================================================================";


///////////////////////////////////////////////////////////////////////////
// ONLINE TABLE
///////////////////////////////////////////////////////////////////////////

print "";
print "==============================================================================================";
print "ONLINE / POST-TRANSCRIPT";
print "==============================================================================================";

printf
"%4o %8o %12o %12o %14o\n",
"R",
"bucket",
"T_filter",
"T_recovery",
"T_post";

print "----------------------------------------------------------------------------------------------";

for A in Results do

    printf
    "%4o %8o %12.5o %12.5o %14.5o\n",

        A[1],
        A[7],

        RR!A[13],
        RR!A[14],
        RR!A[15];

end for;

print "==============================================================================================";


///////////////////////////////////////////////////////////////////////////
// SPEEDUPS
///////////////////////////////////////////////////////////////////////////

T2 :=
    RR!Result2[11];

T4 :=
    RR!Result4[11];

T8 :=
    RR!Result8[11];

print "";
print "============================================================";
print "PREPROCESSING SPEEDUPS";
print "============================================================";

printf
"R=4 versus R=2 : %o x\n",
T2/T4;

printf
"R=8 versus R=2 : %o x\n",
T2/T8;

printf
"R=8 versus R=4 : %o x\n",
T4/T8;


///////////////////////////////////////////////////////////////////////////
// BEST
///////////////////////////////////////////////////////////////////////////

print "";
print "============================================================";
print "BEST ATTACK FOR THIS INSTANCE";
print "============================================================";

if T8 lt T4 and T8 lt T2 then

    print "R = 8 is the fastest preprocessing attack.";

elif T4 lt T2 then

    print "R = 4 is the fastest preprocessing attack.";

else

    print "R = 2 is the fastest preprocessing attack.";

end if;

print "";

print "Degrees:";
print "R=2 :",Result2[2];
print "R=4 :",Result4[2];
print "R=8 :",Result8[2];

print "";

print "Buckets:";
print "R=2 :",Result2[7];
print "R=4 :",Result4[7];
print "R=8 :",Result8[7];

print "";

print "All attacks use exactly h =",h;
print "oracle queries.";

print "============================================================";
