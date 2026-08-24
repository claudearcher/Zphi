#############################################################################
##
##  source : zphi a method by Claude Archer, described in his PhD thesis
##  "Classification of Group Extensions", Université Libre de Bruxelles (2002)
##
##  ZPhiClasses_PG3840_2_C4_OutV4_GAP415.g
## @Claude Archer
##  Classes Z-phi pour
##
##      P = PerfectGroup(3840,2).
##
##  Version visee : GAP 4.15.
##
##  DONNEES STRUCTURELLES CORRECTES
##  --------------------------------
##
##      Z(Pi) = C4,
##      Out(Pi) = V4,
##      rho : Out(Pi) -> Aut(C4)=C2 est SURJECTIVE.
##
##  L'action n'est donc pas triviale. Si
##
##      Out(Pi) = <a,b> = V4,
##
##  on choisit les generateurs de sorte que
##
##      Ker(rho) = <a>,
##      rho(a)=1,
##      rho(b)=rho(a*b)= inversion de C4.
##
##  Les cinq sous-groupes de V4 sont tous distingues, puisque V4 est
##  abelien. Ils donnent cinq branches de coupling :
##
##      1;
##      <a>      (C2, action triviale sur C4);
##      <b>      (C2, action par inversion);
##      <a*b>    (C2, action par inversion);
##      V4       (action d'image C2 et de noyau <a>).
##
##  Ainsi, les cinq branches demandees sont bien calculees, mais elles
##  n'ont pas toutes une action triviale.
##
##  REPRESENTATION DES Z-EXTENSIONS
##  --------------------------------
##
##  Pour |R|=n, le programme parcourt les SmallGroups S d'ordre 4*n et
##  les sous-groupes normaux A = C4 qui representent Z(P).
##
##  * Image 1 ou <a> :
##        l'action sur A est triviale, donc A <= Z(S).
##
##  * Image <b> ou <a*b> :
##        C_S(A) a l'indice 2 dans S et est exactement la preimage du
##        noyau du morphisme surjectif R -> C2.
##
##  * Image V4 :
##        si L est le noyau de S/A -> V4, alors
##
##              A <= L <= C_S(A),    [S:L]=4,
##
##        S/L = V4 et C_S(A)/L correspond au noyau <a> de rho.
##        Pour un couple (A,L), il existe deux identifications compatibles
##        S/L -> Out(P). Le stabilisateur de (A,L) dans Aut(S) peut les
##        echanger; le programme compte exactement leurs orbites.
##
##  MARQUAGE DU C4
##  ----------------
##
##  Il existe deux isomorphismes lambda : Z(P)=C4 -> A. Pour chaque image
##  J <= Out(P), le normalisateur N_Out(P)(J) est V4 tout entier, car V4
##  est abelien. Son image dans Aut(C4) est C2; les deux marquages lambda
##  sont donc toujours equivalents. Il suffit de conserver le sous-groupe
##  A, et non le choix d'un generateur de A.
##
##  FONCTIONS PRINCIPALES
##  ---------------------
##
##      res := ZPhiClasses_C4_V4_AllS(n);;
##
##
#############################################################################


#############################################################################
## 1. Utilitaires.
#############################################################################

C4V4_AutActionOnSubgroup := function(H, alpha)
    return Image(alpha, H);
end;


C4V4_IsContained := function(A, K)
    return ForAll(GeneratorsOfGroup(A), x -> x in K);
end;


C4V4_IsCyclic4 := function(A)
    return Size(A) = 4 and IsCyclic(A);
end;


C4V4_IsV4 := function(Q)
    return Size(Q) = 4
       and IsAbelian(Q)
       and ForAll(GeneratorsOfGroup(Q), x -> Order(x) <= 2);
end;


#############################################################################
## 2. Sous-groupes normaux C4.
#############################################################################

C4V4_NormalCyclic4Subgroups := function(S)
    local elements4, answer, x, A;

    elements4 := Filtered(AsList(S), x -> Order(x) = 4);
    answer := [];
    for x in elements4 do
        A := Subgroup(S, [x]);
        if IsNormal(S, A) and not A in answer then
            Add(answer, A);
        fi;
    od;
    return answer;
end;


C4V4_CentralCyclic4Subgroups := function(S, normalC4s)
    local centreS;

    centreS := Centre(S);
    return Filtered(normalC4s, A -> C4V4_IsContained(A, centreS));
end;


C4V4_InvertingCyclic4Subgroups := function(S, normalC4s)
    return Filtered(
        normalC4s,
        A -> Index(S, Centralizer(S, A)) = 2
    );
end;


#############################################################################
## 3. Noyaux de quotient C2 et V4.
#############################################################################

C4V4_IndexTwoKernels := function(S, normalSubgroups)
    return Filtered(normalSubgroups, K -> Index(S, K) = 2);
end;


C4V4_V4QuotientKernels := function(S, normalSubgroups)
    local answer, L, Q;

    answer := [];
    for L in normalSubgroups do
        if Index(S, L) = 4 then
            Q := FactorGroup(S, L);
            if C4V4_IsV4(Q) then
                Add(answer, L);
            fi;
            Q := fail;
        fi;
    od;
    return answer;
end;


#############################################################################
## 4. Action induite par un stabilisateur sur S/L = V4.
#############################################################################

C4V4_QuotientPermutation := function(alpha, S, L, naturalMap, quotient)
    local points, positions, q, preimage, imageQ, permutation;

    points := Set(Filtered(AsList(quotient), x -> x <> One(quotient)));
    if Length(points) <> 3 then
        Error("S/L is not V4");
    fi;

    positions := [];
    for q in points do
        preimage := PreImagesRepresentative(naturalMap, q);
        imageQ := Image(naturalMap, Image(alpha, preimage));
        Add(positions, Position(points, imageQ));
    od;
    if fail in positions then
        Error("an automorphism does not induce a permutation on S/L");
    fi;

    permutation := PermList(positions);
    if permutation = fail then
        Error("failed to construct the induced quotient permutation");
    fi;
    return permutation;
end;


## Pour une paire (A,L) de la branche V4, il existe exactement deux
## isomorphismes S/L -> V4 qui envoient C_S(A)/L sur Ker(rho)=C2.
## Le stabilisateur de (A,L) agit sur ces deux isomorphismes. Son image
## induite sur le quotient a ordre 1 ou 2; la contribution vaut 2/|image|.
C4V4_V4CompatibleIsomorphismOrbits := function(S, A, L, stabilizerAL)
    local naturalMap, quotient, centralizerA, kernelLine, permutations, alpha, imageGroup, sizeImage;

    centralizerA := Centralizer(S, A);
    if Index(S, centralizerA) <> 2 then
        Error("the V4 branch requires an inverting C4");
    fi;
    if not C4V4_IsContained(A, L)
       or not C4V4_IsContained(L, centralizerA) then
        Error("invalid chain A <= L <= C_S(A)");
    fi;

    naturalMap := NaturalHomomorphismByNormalSubgroup(S, L);
    quotient := Image(naturalMap);
    if not C4V4_IsV4(quotient) then
        Error("the quotient in the V4 branch is not V4");
    fi;

    kernelLine := Image(naturalMap, centralizerA);
    if Size(kernelLine) <> 2 then
        Error("C_S(A)/L is not the required C2");
    fi;

    permutations := [];
    for alpha in GeneratorsOfGroup(stabilizerAL) do
        if Image(alpha, centralizerA) <> centralizerA then
            Error("the stabilizer of A does not preserve C_S(A)");
        fi;
        Add(
            permutations,
            C4V4_QuotientPermutation(
                alpha, S, L, naturalMap, quotient
            )
        );
    od;

    if Length(permutations) = 0 then
        imageGroup := Group(());
    else
        imageGroup := Group(permutations);
    fi;
    sizeImage := Size(imageGroup);

    ## Le stabilisateur doit fixer la droite C_S(A)/L; son image sur les
    ## deux identifications compatibles est donc 1 ou C2.
    if not sizeImage in [1,2] then
        Error("unexpected induced action on the compatible V4 markings");
    fi;

    naturalMap := fail;
    quotient := fail;
    centralizerA := fail;
    kernelLine := fail;
    permutations := fail;
    imageGroup := fail;
    return 2 / sizeImage;
end;


#############################################################################
## 5. Calcul pour un SmallGroup S fixe.
#############################################################################

C4V4_ForGroup := function(S, normalC4s, normalSubgroups)
    local autS, centralC4s, invertingC4s, centralOrbits, invertingOrbits, trivialClasses, kernelC2Classes, inversionC2AClasses, inversionC2BClasses, wholeV4Classes, indexTwoKernels, v4Kernels, numberIndexTwoPairs, numberIndexTwoPairOrbits, numberV4Pairs, numberV4PairOrbits, orbitA, A, stabA, admissible, kernelOrbits, orbitK, K, stabAK, centralizerA, contribution, t0, autMs, trivialMs, c2Ms, v4Ms;

    t0 := Runtime();
    autS := AutomorphismGroup(S);
    autMs := Runtime() - t0;

    centralC4s := C4V4_CentralCyclic4Subgroups(S, normalC4s);
    invertingC4s := C4V4_InvertingCyclic4Subgroups(S, normalC4s);

    t0 := Runtime();
    centralOrbits := Orbits(
        autS, centralC4s, C4V4_AutActionOnSubgroup
    );
    trivialClasses := Length(centralOrbits);
    trivialMs := Runtime() - t0;

    indexTwoKernels := [];
    v4Kernels := [];
    if normalSubgroups <> fail then
        indexTwoKernels :=
            C4V4_IndexTwoKernels(S, normalSubgroups);
        v4Kernels :=
            C4V4_V4QuotientKernels(S, normalSubgroups);
    fi;

    ## Branche image Ker(rho)=<a>=C2, action triviale sur C4.
    t0 := Runtime();
    kernelC2Classes := 0;
    numberIndexTwoPairs := 0;
    numberIndexTwoPairOrbits := 0;
    for orbitA in centralOrbits do
        A := orbitA[1];
        stabA := Stabilizer(
            autS, A, C4V4_AutActionOnSubgroup
        );
        admissible := Filtered(
            indexTwoKernels,
            K -> C4V4_IsContained(A, K)
        );
        numberIndexTwoPairs :=
            numberIndexTwoPairs + Length(orbitA) * Length(admissible);
        kernelOrbits := Orbits(
            stabA, admissible, C4V4_AutActionOnSubgroup
        );
        numberIndexTwoPairOrbits :=
            numberIndexTwoPairOrbits + Length(kernelOrbits);
        kernelC2Classes := kernelC2Classes + Length(kernelOrbits);
    od;

    ## Les deux autres C2 sont non conjugues dans V4, mais leur action
    ## sur C4 est la meme inversion. Ils ont donc des nombres egaux.
    invertingOrbits := Orbits(
        autS, invertingC4s, C4V4_AutActionOnSubgroup
    );
    inversionC2AClasses := Length(invertingOrbits);
    inversionC2BClasses := Length(invertingOrbits);
    c2Ms := Runtime() - t0;

    ## Branche image V4 tout entier.
    t0 := Runtime();
    wholeV4Classes := 0;
    numberV4Pairs := 0;
    numberV4PairOrbits := 0;
    for orbitA in invertingOrbits do
        A := orbitA[1];
        centralizerA := Centralizer(S, A);
        stabA := Stabilizer(
            autS, A, C4V4_AutActionOnSubgroup
        );
        admissible := Filtered(
            v4Kernels,
            K -> C4V4_IsContained(A, K)
              and C4V4_IsContained(K, centralizerA)
        );
        numberV4Pairs :=
            numberV4Pairs + Length(orbitA) * Length(admissible);
        kernelOrbits := Orbits(
            stabA, admissible, C4V4_AutActionOnSubgroup
        );
        numberV4PairOrbits :=
            numberV4PairOrbits + Length(kernelOrbits);

        for orbitK in kernelOrbits do
            K := orbitK[1];
            stabAK := Stabilizer(
                stabA, K, C4V4_AutActionOnSubgroup
            );
            contribution := C4V4_V4CompatibleIsomorphismOrbits(
                S, A, K, stabAK
            );
            wholeV4Classes := wholeV4Classes + contribution;
        od;
    od;
    v4Ms := Runtime() - t0;

    return rec(
        numberNormalC4Subgroups := Length(normalC4s),
        numberCentralC4Subgroups := Length(centralC4s),
        numberInvertingC4Subgroups := Length(invertingC4s),
        numberCentralC4Orbits := Length(centralOrbits),
        numberInvertingC4Orbits := Length(invertingOrbits),
        numberIndexTwoPairs := numberIndexTwoPairs,
        numberIndexTwoPairOrbits := numberIndexTwoPairOrbits,
        numberV4Pairs := numberV4Pairs,
        numberV4PairOrbits := numberV4PairOrbits,
        trivialClasses := trivialClasses,
        kernelC2Classes := kernelC2Classes,
        inversionC2AClasses := inversionC2AClasses,
        inversionC2BClasses := inversionC2BClasses,
        wholeV4Classes := wholeV4Classes,
        totalClasses := trivialClasses + kernelC2Classes
            + inversionC2AClasses + inversionC2BClasses
            + wholeV4Classes,
        timings := rec(
            automorphismGroupMs := autMs,
            trivialBranchMs := trivialMs,
            c2BranchesMs := c2Ms,
            v4BranchMs := v4Ms
        )
    );
end;


#############################################################################
## 6. Fonction principale : somme sur tous les SmallGroups S d'ordre 4*n.
#############################################################################

ZPhiClasses_PG3840_2_AllS := function(n)
    local orderS, numberGroups, totals, perGroup, i, S, normalC4s, normalSubgroups, oneResult, t0, garbageCollectionMs, branchData;

    if not IsInt(n) or n < 1 then
        Error("n must be a positive integer");
    fi;

    orderS := 4 * n;
    numberGroups := NumberSmallGroups(orderS);
    totals := rec(
        groupsWithNormalC4 := 0,
        normalC4Subgroups := 0,
        centralC4Subgroups := 0,
        invertingC4Subgroups := 0,
        centralC4Orbits := 0,
        invertingC4Orbits := 0,
        indexTwoPairs := 0,
        indexTwoPairOrbits := 0,
        v4Pairs := 0,
        v4PairOrbits := 0,
        trivialClasses := 0,
        kernelC2Classes := 0,
        inversionC2AClasses := 0,
        inversionC2BClasses := 0,
        wholeV4Classes := 0,
        automorphismGroupMs := 0,
        trivialBranchMs := 0,
        c2BranchesMs := 0,
        v4BranchMs := 0
    );
    perGroup := [];
    garbageCollectionMs := 0;

    Print("ZPhiClasses_PG3840_2_AllS(", n, ")\n");
    Print("Applicable to PerfectGroup(3840,2)\n");
    Print("Z(P)=C4, Out(P)=V4, action image C2 (not trivial)\n");
    Print("SmallGroups of order ", orderS,
          " to test = ", numberGroups, "\n");

    for i in [1..numberGroups] do
        S := SmallGroup(orderS, i);
        normalC4s := C4V4_NormalCyclic4Subgroups(S);

        if Length(normalC4s) > 0 then
            totals.groupsWithNormalC4 :=
                totals.groupsWithNormalC4 + 1;

            ## Les noyaux non triviaux n'existent que si n est pair.
            if n mod 2 = 0 then
                normalSubgroups := NormalSubgroups(S);
            else
                normalSubgroups := fail;
            fi;

            oneResult := C4V4_ForGroup(
                S, normalC4s, normalSubgroups
            );

            totals.normalC4Subgroups :=
                totals.normalC4Subgroups
                + oneResult.numberNormalC4Subgroups;
            totals.centralC4Subgroups :=
                totals.centralC4Subgroups
                + oneResult.numberCentralC4Subgroups;
            totals.invertingC4Subgroups :=
                totals.invertingC4Subgroups
                + oneResult.numberInvertingC4Subgroups;
            totals.centralC4Orbits :=
                totals.centralC4Orbits
                + oneResult.numberCentralC4Orbits;
            totals.invertingC4Orbits :=
                totals.invertingC4Orbits
                + oneResult.numberInvertingC4Orbits;
            totals.indexTwoPairs :=
                totals.indexTwoPairs + oneResult.numberIndexTwoPairs;
            totals.indexTwoPairOrbits :=
                totals.indexTwoPairOrbits
                + oneResult.numberIndexTwoPairOrbits;
            totals.v4Pairs :=
                totals.v4Pairs + oneResult.numberV4Pairs;
            totals.v4PairOrbits :=
                totals.v4PairOrbits
                + oneResult.numberV4PairOrbits;
            totals.trivialClasses :=
                totals.trivialClasses + oneResult.trivialClasses;
            totals.kernelC2Classes :=
                totals.kernelC2Classes + oneResult.kernelC2Classes;
            totals.inversionC2AClasses :=
                totals.inversionC2AClasses
                + oneResult.inversionC2AClasses;
            totals.inversionC2BClasses :=
                totals.inversionC2BClasses
                + oneResult.inversionC2BClasses;
            totals.wholeV4Classes :=
                totals.wholeV4Classes + oneResult.wholeV4Classes;
            totals.automorphismGroupMs :=
                totals.automorphismGroupMs
                + oneResult.timings.automorphismGroupMs;
            totals.trivialBranchMs :=
                totals.trivialBranchMs
                + oneResult.timings.trivialBranchMs;
            totals.c2BranchesMs :=
                totals.c2BranchesMs
                + oneResult.timings.c2BranchesMs;
            totals.v4BranchMs :=
                totals.v4BranchMs
                + oneResult.timings.v4BranchMs;

            Add(perGroup, rec(
                id := [orderS, i],
                normalC4Subgroups :=
                    oneResult.numberNormalC4Subgroups,
                centralC4Orbits :=
                    oneResult.numberCentralC4Orbits,
                invertingC4Orbits :=
                    oneResult.numberInvertingC4Orbits,
                trivialClasses := oneResult.trivialClasses,
                kernelC2Classes := oneResult.kernelC2Classes,
                inversionC2AClasses :=
                    oneResult.inversionC2AClasses,
                inversionC2BClasses :=
                    oneResult.inversionC2BClasses,
                wholeV4Classes := oneResult.wholeV4Classes,
                totalClasses := oneResult.totalClasses
            ));
        fi;

        ## Liberer toutes les structures attachees au groupe termine.
        S := fail;
        normalC4s := fail;
        normalSubgroups := fail;
        oneResult := fail;

        if i mod 100 = 0 then
            t0 := Runtime();
            GASMAN("collect");
            garbageCollectionMs :=
                garbageCollectionMs + Runtime() - t0;
            Print("processed ", i, " / ", numberGroups,
                  " SmallGroups\n");
        fi;
    od;

    branchData := [
        rec(
            label := "trivial",
            actionOnC4 := "trivial",
            classes := totals.trivialClasses
        ),
        rec(
            label := "kernel_C2_<a>",
            actionOnC4 := "trivial",
            classes := totals.kernelC2Classes
        ),
        rec(
            label := "inverting_C2_<b>",
            actionOnC4 := "inversion",
            classes := totals.inversionC2AClasses
        ),
        rec(
            label := "inverting_C2_<a*b>",
            actionOnC4 := "inversion",
            classes := totals.inversionC2BClasses
        ),
        rec(
            label := "whole_V4",
            actionOnC4 := "image C2, kernel <a>",
            classes := totals.wholeV4Classes
        )
    ];

    Print("\nSummary\n");
    Print("n = ", n, "; |S| = ", orderS,
          "; |E| = ", 3840*n, "\n");
    Print("SmallGroups tested = ", numberGroups, "\n");
    Print("groups with a normal C4 = ",
          totals.groupsWithNormalC4, "\n");
    Print("normal C4 subgroups = ",
          totals.normalC4Subgroups, "\n");
    Print("central / inverting C4 subgroups = ",
          totals.centralC4Subgroups, " / ",
          totals.invertingC4Subgroups, "\n");
    Print("central / inverting C4 orbits = ",
          totals.centralC4Orbits, " / ",
          totals.invertingC4Orbits, "\n");
    Print("image 1 classes = ", totals.trivialClasses, "\n");
    Print("image kernel C2 <a> classes = ",
          totals.kernelC2Classes, "\n");
    Print("image inverting C2 <b> classes = ",
          totals.inversionC2AClasses, "\n");
    Print("image inverting C2 <a*b> classes = ",
          totals.inversionC2BClasses, "\n");
    Print("image whole V4 classes = ",
          totals.wholeV4Classes, "\n");
    Print("total Z-phi classes = ",
          Sum(branchData, x -> x.classes), "\n");
    Print("index-two pairs/orbits = ",
          totals.indexTwoPairs, "/",
          totals.indexTwoPairOrbits, "\n");
    Print("V4-kernel pairs/orbits = ",
          totals.v4Pairs, "/",
          totals.v4PairOrbits, "\n");
    Print("forced garbage collection time (ms) = ",
          garbageCollectionMs, "\n");

    return rec(
        perfectGroup := [3840,2],
        n := n,
        orderS := orderS,
        orderFinalExtension := 3840 * n,
        numberSmallGroupsTested := numberGroups,
        groupsWithNormalC4 := totals.groupsWithNormalC4,
        normalC4Subgroups := totals.normalC4Subgroups,
        centralC4Subgroups := totals.centralC4Subgroups,
        invertingC4Subgroups := totals.invertingC4Subgroups,
        centralC4Orbits := totals.centralC4Orbits,
        invertingC4Orbits := totals.invertingC4Orbits,
        indexTwoPairs := totals.indexTwoPairs,
        indexTwoPairOrbits := totals.indexTwoPairOrbits,
        v4Pairs := totals.v4Pairs,
        v4PairOrbits := totals.v4PairOrbits,
        byImageClass := branchData,
        totalClasses := Sum(branchData, x -> x.classes),
        perGroup := perGroup,
        branchTimings := rec(
            automorphismGroupMs := totals.automorphismGroupMs,
            trivialBranchMs := totals.trivialBranchMs,
            c2BranchesMs := totals.c2BranchesMs,
            v4BranchMs := totals.v4BranchMs
        ),
        garbageCollectionMs := garbageCollectionMs
    );
end;
