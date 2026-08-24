#############################################################################
##
##  source : zphi a method by Claude Archer, described in his PhD thesis
##  "Classification of Group Extensions", Université Libre de Bruxelles (2002)
##
##  ZPhiClasses_PG3840_7_V4_OutC2_trivial_GAP415.g
##
##  Calcul exact des Z-phi-classes pour
##
##      P = PerfectGroup(3840,7),
##      Z(P) = V4,
##      Out(P) = C2,
##
##  lorsque Out(P) agit trivialement (donc ponctuellement) sur Z(P).
##
##  Version visee : GAP 4.15.
##
##  La fonction principale est
##
##      res := ZPhiClasses_V4_C2_AllS(n);;
##
##  Elle parcourt les SmallGroups S d'ordre 4*n. Une Z-extension comporte
##  une identification marquee
##
##      lambda : Z(P) -> A,
##
##  ou A <= Z(S) est un sous-groupe isomorphe a V4. Cette identification
##  fait partie de la donnee : on ne doit pas oublier ses six choix.
##
##  ------------------------------------------------------------------------
##  POURQUOI LES SIX IDENTIFICATIONS NE SONT PAS TOUJOURS EQUIVALENTES
##  ------------------------------------------------------------------------
##
##  Dans l'equivalence d'Archer, lambda_1 et lambda_2 sont equivalentes s'il
##  existe alpha dans Aut(S) et pi dans Aut(P) tels que
##
##      alpha(lambda_1(z)) = lambda_2(pi(z))  pour tout z dans Z(P).
##
##  Ici Aut(P) fixe Z(P) ponctuellement, puisque l'action de Out(P)=C2 sur
##  Z(P) est triviale. Ainsi pi(z)=z et seule l'action de Aut(S) subsiste.
##
##  Pour un representant A d'une orbite de sous-groupes centraux V4, soit
##
##      L_A = Image(Stab_Aut(S)(A) -> Aut(A)) <= S3.
##
##  Les six isomorphismes Z(P)->A forment un torseur sous Aut(A)=S3. L_A y
##  agit librement. Le nombre de classes marquees au-dessus de A vaut donc
##
##      6 / |L_A|.
##
##  Il vaut 1 seulement si le stabilisateur induit tout S3 sur A.
##
##  ------------------------------------------------------------------------
##  LES DEUX COUPLINGS VERS Out(P)=C2
##  ------------------------------------------------------------------------
##
##  (1) Coupling trivial : on somme 6/|L_A| sur les orbites de A.
##
##  (2) Coupling surjectif : phi:S/A -> C2 est determine uniquement par son
##      noyau K/A. Donc K est un sous-groupe d'indice 2 de S contenant A.
##      On considere les orbites de couples (A,K). Pour un representant,
##
##        L_AK = Image(Stab_Aut(S)(A,K) -> Aut(A)),
##
##      et la contribution est 6/|L_AK|.
##
##  Comme Aut(C2)=1 et C2 est abelien, il n'y a aucune postcomposition ou
##  conjugaison supplementaire a quotienter.
##
##  ------------------------------------------------------------------------
##  OPTIMISATIONS ET MEMOIRE
##  ------------------------------------------------------------------------
##
##  * Aut(S) n'est construit que si S possede un V4 central.
##  * Les couples (A,K) ne sont pas tous materialises. Apres avoir fixe un
##    representant A, on calcule les orbites des K sous Stab(A).
##  * Si S=C2^d, la formule fermee donne une classe pour le coupling trivial
##    et, si d>=3, une classe pour le coupling surjectif. GL(d,2) n'est pas
##    construit.
##  * Les objets lourds sont remplaces par fail apres chaque groupe.
##  * GASMAN("collect") est force tous les 100 groupes et a la fin.
##  * Chaque fonction contient une unique declaration local.
##
#############################################################################


#############################################################################
## 1. Actions naturelles des automorphismes de S.
#############################################################################

V4C2_AutActionOnSubgroup := function(H, alpha)
    return Image(alpha, H);
end;


#############################################################################
## 2. Tests elementaires et enumeration des V4 centraux.
#############################################################################

V4C2_IsElementaryAbelian2Group := function(S)
    return IsAbelian(S)
       and ForAll(GeneratorsOfGroup(S), x -> Order(x) <= 2);
end;


V4C2_CentralV4Subgroups := function(S)
    local one, involutions, keys, subgroups, i, j, key, A;

    one := One(S);
    involutions := Filtered(AsList(Centre(S)), x -> Order(x) = 2);

    ## Un V4 contient exactement trois involutions non triviales.
    if Length(involutions) < 3 then
        return [];
    fi;

    keys := [];
    subgroups := [];

    for i in [1..Length(involutions)-1] do
        for j in [i+1..Length(involutions)] do
            ## Deux involutions centrales distinctes engendrent un V4.
            key := Set([
                one,
                involutions[i],
                involutions[j],
                involutions[i] * involutions[j]
            ]);
            if Length(key) = 4 and not key in keys then
                A := Subgroup(S, [involutions[i], involutions[j]]);
                Add(keys, key);
                Add(subgroups, A);
            fi;
        od;
    od;

    return subgroups;
end;


#############################################################################
## 3. Sous-groupes d'indice 2.
##
##    Chaque epimorphisme S -> C2 est determine par son noyau, puisque
##    Aut(C2)=1. Le raccourci elementaire abelien evite le seul cas ou
##    AllHomomorphisms pourrait construire GL(d,2) ou une liste enorme.
#############################################################################

V4C2_IndexTwoSubgroups := function(S)
    local C2, epimorphisms, kernels;

    C2 := CyclicGroup(IsPermGroup, 2);
    epimorphisms := Filtered(AllHomomorphisms(S, C2), IsSurjective);
    kernels := Set(List(epimorphisms, Kernel));

    if Length(kernels) <> Length(epimorphisms) then
        Error("distinct epimorphisms S -> C2 unexpectedly share a kernel");
    fi;
    if not ForAll(kernels, K -> Index(S, K) = 2 and IsNormal(S, K)) then
        Error("an alleged kernel is not a normal subgroup of index 2");
    fi;

    return kernels;
end;


V4C2_IsContained := function(A, K)
    return ForAll(GeneratorsOfGroup(A), x -> x in K);
end;


#############################################################################
## 4. Image du stabilisateur sur A=V4.
##
##    On fait agir les generateurs du stabilisateur sur les trois elements
##    non triviaux de A. Le groupe de permutations obtenu est exactement
##    l'image dans Aut(A)=S3. Son ordre doit appartenir a {1,2,3,6}.
#############################################################################

V4C2_RestrictionImageSize := function(stabilizer, A, S)
    local points, permutations, alpha, positions, permutation, imageGroup, answer;

    points := Set(Filtered(AsList(A), x -> x <> One(S)));
    if Length(points) <> 3 then
        Error("the marked subgroup is not V4");
    fi;

    permutations := [];
    for alpha in GeneratorsOfGroup(stabilizer) do
        positions := List(
            points,
            x -> Position(points, Image(alpha, x))
        );
        if fail in positions then
            Error("the alleged stabilizer does not preserve A");
        fi;
        permutation := PermList(positions);
        if permutation = fail then
            Error("the induced map on the three involutions is not a permutation");
        fi;
        Add(permutations, permutation);
    od;

    if Length(permutations) = 0 then
        imageGroup := Group(());
    else
        imageGroup := Group(permutations);
    fi;
    answer := Size(imageGroup);

    if not answer in [1,2,3,6] then
        Error("unexpected restriction image size in Aut(V4)");
    fi;
    return answer;
end;


#############################################################################
## 5. Calcul generique pour un groupe S non elementaire abelien.
#############################################################################

V4C2_ForGenericGroup := function(S, autS, centralV4s, indexTwoSubgroups)
    local v4Orbits, centralClasses, surjectiveClasses, centralHistogram, surjectiveHistogram, numberPairOrbits, numberAdmissiblePairs, numberIndexTwo, orbitA, A, stabA, restrictionSize, contribution, admissibleK, kOrbits, orbitK, K, stabAK, centralMs, surjectiveMs, t0;

    t0 := Runtime();
    v4Orbits := Orbits(
        autS,
        centralV4s,
        V4C2_AutActionOnSubgroup
    );

    centralClasses := 0;
    surjectiveClasses := 0;
    centralHistogram := [0,0,0,0,0,0];
    surjectiveHistogram := [0,0,0,0,0,0];
    numberPairOrbits := 0;
    numberAdmissiblePairs := 0;
    if indexTwoSubgroups = fail then
        numberIndexTwo := fail;
    else
        numberIndexTwo := Length(indexTwoSubgroups);
    fi;

    for orbitA in v4Orbits do
        A := orbitA[1];
        stabA := Stabilizer(
            autS,
            A,
            V4C2_AutActionOnSubgroup
        );
        restrictionSize := V4C2_RestrictionImageSize(stabA, A, S);
        contribution := 6 / restrictionSize;
        if not IsInt(contribution) then
            Error("6/|L_A| is not an integer");
        fi;
        centralClasses := centralClasses + contribution;
        centralHistogram[restrictionSize] :=
            centralHistogram[restrictionSize] + 1;
    od;
    centralMs := Runtime() - t0;

    t0 := Runtime();
    if indexTwoSubgroups <> fail then
        for orbitA in v4Orbits do
            A := orbitA[1];
            stabA := Stabilizer(
                autS,
                A,
                V4C2_AutActionOnSubgroup
            );
            admissibleK := Filtered(
                indexTwoSubgroups,
                K -> V4C2_IsContained(A, K)
            );

            ## Tous les A de l'orbite ont le meme nombre de K admissibles.
            numberAdmissiblePairs := numberAdmissiblePairs
                + Length(orbitA) * Length(admissibleK);

            kOrbits := Orbits(
                stabA,
                admissibleK,
                V4C2_AutActionOnSubgroup
            );
            numberPairOrbits := numberPairOrbits + Length(kOrbits);

            for orbitK in kOrbits do
                K := orbitK[1];
                ## Comme stabA fixe deja A, ce stabilisateur est exactement
                ## Stab_Aut(S)(A,K).
                stabAK := Stabilizer(
                    stabA,
                    K,
                    V4C2_AutActionOnSubgroup
                );
                restrictionSize :=
                    V4C2_RestrictionImageSize(stabAK, A, S);
                contribution := 6 / restrictionSize;
                if not IsInt(contribution) then
                    Error("6/|L_AK| is not an integer");
                fi;
                surjectiveClasses := surjectiveClasses + contribution;
                surjectiveHistogram[restrictionSize] :=
                    surjectiveHistogram[restrictionSize] + 1;
            od;
        od;
    fi;
    surjectiveMs := Runtime() - t0;

    return rec(
        elementaryAbelianShortcut := false,
        numberCentralV4Subgroups  := Length(centralV4s),
        numberCentralV4Orbits     := Length(v4Orbits),
        numberIndexTwoSubgroups   := numberIndexTwo,
        numberAdmissiblePairs     := numberAdmissiblePairs,
        numberPairOrbits          := numberPairOrbits,
        centralClasses            := centralClasses,
        surjectiveClasses         := surjectiveClasses,
        totalClasses              := centralClasses + surjectiveClasses,
        centralRestrictionHistogram := [
            centralHistogram[1],
            centralHistogram[2],
            centralHistogram[3],
            centralHistogram[6]
        ],
        surjectiveRestrictionHistogram := [
            surjectiveHistogram[1],
            surjectiveHistogram[2],
            surjectiveHistogram[3],
            surjectiveHistogram[6]
        ],
        centralMs                 := centralMs,
        surjectiveMs              := surjectiveMs
    );
end;


#############################################################################
## 6. Formule fermee pour S=C2^d.
##
##    GL(d,2) est transitif sur les sous-espaces A de dimension 2. Le
##    stabilisateur de A induit GL(A)=S3. Pour d>=3, GL(d,2) est aussi
##    transitif sur les drapeaux A<K<S avec dim(A)=2 et dim(K)=d-1, et le
##    stabilisateur du drapeau induit encore GL(A). Chaque branche fournit
##    donc exactement une classe.
#############################################################################

V4C2_ForElementaryAbelianGroup := function(S)
    local sizeS, dimension, power, numberV4, numberIndexTwo, numberKPerA, numberPairs, hasSurjective, surjectiveCount, surjectiveHistogram;

    sizeS := Size(S);
    dimension := 0;
    power := 1;
    while power < sizeS do
        power := 2 * power;
        dimension := dimension + 1;
    od;
    if power <> sizeS or dimension < 2 then
        Error("invalid elementary abelian group order");
    fi;

    numberV4 := ((2^dimension - 1) * (2^dimension - 2)) / 6;
    numberIndexTwo := 2^dimension - 1;
    numberKPerA := 2^(dimension-2) - 1;
    numberPairs := numberV4 * numberKPerA;
    hasSurjective := dimension >= 3;
    if hasSurjective then
        surjectiveCount := 1;
        surjectiveHistogram := [0,0,0,1];
    else
        surjectiveCount := 0;
        surjectiveHistogram := [0,0,0,0];
    fi;

    return rec(
        elementaryAbelianShortcut := true,
        dimension                  := dimension,
        automorphismGroupDescription := Concatenation(
            "GL(", String(dimension), ",2) (not constructed)"
        ),
        numberCentralV4Subgroups  := numberV4,
        numberCentralV4Orbits     := 1,
        numberIndexTwoSubgroups   := numberIndexTwo,
        numberAdmissiblePairs     := numberPairs,
        numberPairOrbits          := surjectiveCount,
        centralClasses            := 1,
        surjectiveClasses         := surjectiveCount,
        totalClasses              := 1 + surjectiveCount,
        centralRestrictionHistogram := [0,0,0,1],
        surjectiveRestrictionHistogram := surjectiveHistogram,
        centralMs                 := 0,
        surjectiveMs              := 0
    );
end;


#############################################################################
## 7. Fonction principale.
#############################################################################

ZPhiClasses_V4_C2_AllS := function(n)
    local orderS, numberGroups, i, S, centralV4s, autS, indexTwoSubgroups, groupData, compactData, perGroup, eligibleGroups, elementaryShortcuts, centralClasses, surjectiveClasses, centralV4Subgroups, centralV4Orbits, admissiblePairs, pairOrbits, centralHistogram, surjectiveHistogram, centralMs, surjectiveMs, indexTwoMs, autMs, gcMs, t0, gcStart, j, result;

    if not IsInt(n) or n < 1 then
        Error("n must be a positive integer");
    fi;

    orderS := 4 * n;
    numberGroups := NumberSmallGroups(orderS);
    perGroup := [];
    eligibleGroups := 0;
    elementaryShortcuts := 0;
    centralClasses := 0;
    surjectiveClasses := 0;
    centralV4Subgroups := 0;
    centralV4Orbits := 0;
    admissiblePairs := 0;
    pairOrbits := 0;
    centralHistogram := [0,0,0,0];
    surjectiveHistogram := [0,0,0,0];
    centralMs := 0;
    surjectiveMs := 0;
    indexTwoMs := 0;
    autMs := 0;
    gcMs := 0;

    Print("ZPhiClasses_V4_C2_AllS(", n, ")\n");
    Print("SmallGroups of order ", orderS, " to test = ", numberGroups, "\n");

    for i in [1..numberGroups] do
        S := SmallGroup(orderS, i);
        groupData := fail;

        ## Tester ce cas avant d'enumerer les V4 : pour C2^d, la liste des
        ## sous-espaces de dimension 2 peut deja etre tres grande.
        if V4C2_IsElementaryAbelian2Group(S) then
            eligibleGroups := eligibleGroups + 1;
            elementaryShortcuts := elementaryShortcuts + 1;
            centralV4s := fail;
            groupData := V4C2_ForElementaryAbelianGroup(S);
            Print(
                "elementary abelian shortcut for SmallGroup(",
                orderS, ",", i, "): ",
                groupData.automorphismGroupDescription, "\n"
            );
        else
            centralV4s := V4C2_CentralV4Subgroups(S);
            if Length(centralV4s) > 0 then
                eligibleGroups := eligibleGroups + 1;
                t0 := Runtime();
                autS := AutomorphismGroup(S);
                autMs := autMs + Runtime() - t0;

                if n mod 2 = 0 then
                    t0 := Runtime();
                    indexTwoSubgroups := V4C2_IndexTwoSubgroups(S);
                    indexTwoMs := indexTwoMs + Runtime() - t0;
                else
                    indexTwoSubgroups := fail;
                fi;

                groupData := V4C2_ForGenericGroup(
                    S,
                    autS,
                    centralV4s,
                    indexTwoSubgroups
                );
            fi;
        fi;

        if groupData <> fail then
            centralClasses := centralClasses + groupData.centralClasses;
            surjectiveClasses :=
                surjectiveClasses + groupData.surjectiveClasses;
            centralV4Subgroups :=
                centralV4Subgroups + groupData.numberCentralV4Subgroups;
            centralV4Orbits :=
                centralV4Orbits + groupData.numberCentralV4Orbits;
            admissiblePairs :=
                admissiblePairs + groupData.numberAdmissiblePairs;
            pairOrbits := pairOrbits + groupData.numberPairOrbits;
            centralMs := centralMs + groupData.centralMs;
            surjectiveMs := surjectiveMs + groupData.surjectiveMs;

            for j in [1..4] do
                centralHistogram[j] := centralHistogram[j]
                    + groupData.centralRestrictionHistogram[j];
                surjectiveHistogram[j] := surjectiveHistogram[j]
                    + groupData.surjectiveRestrictionHistogram[j];
            od;

            compactData := rec(
                smallGroupId              := [orderS, i],
                structure                 := StructureDescription(S),
                elementaryAbelianShortcut :=
                    groupData.elementaryAbelianShortcut,
                numberCentralV4Subgroups  :=
                    groupData.numberCentralV4Subgroups,
                numberCentralV4Orbits     :=
                    groupData.numberCentralV4Orbits,
                numberIndexTwoSubgroups   :=
                    groupData.numberIndexTwoSubgroups,
                numberAdmissiblePairs     :=
                    groupData.numberAdmissiblePairs,
                numberPairOrbits          := groupData.numberPairOrbits,
                centralClasses            := groupData.centralClasses,
                surjectiveClasses         := groupData.surjectiveClasses,
                totalClasses              := groupData.totalClasses,
                centralRestrictionHistogram :=
                    groupData.centralRestrictionHistogram,
                surjectiveRestrictionHistogram :=
                    groupData.surjectiveRestrictionHistogram
            );
            Add(perGroup, compactData);
        fi;

        ## Liberer toutes les references lourdes du groupe courant.
        S := fail;
        centralV4s := fail;
        autS := fail;
        indexTwoSubgroups := fail;
        groupData := fail;
        compactData := fail;

        if i mod 100 = 0 or i = numberGroups then
            gcStart := Runtime();
            GASMAN("collect");
            gcMs := gcMs + Runtime() - gcStart;
        fi;
        if i mod 100 = 0 then
            Print("processed ", i, " / ", numberGroups, " SmallGroups\n");
        fi;
    od;

    result := rec(
        n                         := n,
        orderS                    := orderS,
        applicablePerfectGroup    := [3840,7],
        centreStructure           := "C2 x C2",
        outStructure              := "C2",
        actionOnCentre            := "trivial (pointwise)",
        smallGroupsTested          := numberGroups,
        eligibleSmallGroups        := eligibleGroups,
        elementaryAbelianShortcuts := elementaryShortcuts,
        centralV4Subgroups         := centralV4Subgroups,
        unmarkedCentralV4Orbits    := centralV4Orbits,
        admissiblePairs            := admissiblePairs,
        unmarkedPairOrbits         := pairOrbits,
        centralProductClasses      := centralClasses,
        surjectiveCouplingClasses  := surjectiveClasses,
        totalClasses               := centralClasses + surjectiveClasses,
        restrictionImageSizes      := [1,2,3,6],
        centralRestrictionHistogram := centralHistogram,
        surjectiveRestrictionHistogram := surjectiveHistogram,
        timings := rec(
            automorphismGroupsMs  := autMs,
            indexTwoSubgroupsMs   := indexTwoMs,
            centralOrbitMs        := centralMs,
            surjectiveOrbitMs     := surjectiveMs,
            forcedGarbageCollectionMs := gcMs
        ),
        perGroup                   := perGroup
    );

    Print("\nSummary\n");
    Print("n = ", n, "\n");
    Print("SmallGroups tested = ", numberGroups, "\n");
    Print("groups with a central V4 = ", eligibleGroups, "\n");
    Print("elementary abelian shortcuts = ", elementaryShortcuts, "\n");
    Print("central V4 subgroups = ", centralV4Subgroups, "\n");
    Print("unmarked central V4 orbits = ", centralV4Orbits, "\n");
    Print("central product Z-phi classes = ", centralClasses, "\n");
    Print("admissible pairs (V4,K) = ", admissiblePairs, "\n");
    Print("unmarked pair orbits = ", pairOrbits, "\n");
    Print("surjective coupling Z-phi classes = ", surjectiveClasses, "\n");
    Print("total Z-phi classes = ", centralClasses + surjectiveClasses, "\n");
    Print(
        "central stabilizer image sizes [1,2,3,6] = ",
        centralHistogram, "\n"
    );
    Print(
        "pair stabilizer image sizes [1,2,3,6] = ",
        surjectiveHistogram, "\n"
    );
    Print("forced garbage collection time (ms) = ", gcMs, "\n");

    return result;
end;
