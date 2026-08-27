#############################################################################
##
##  ZPhiClasses_C2_OutD8_AllS_FINAL_Optimized_GAP415.g
##
##  Calcul exact des Z-phi-classes dans le cas
##
##      Z(P) = C2,       Out(P) = D8,
##
##  l'action de Out(P) sur Z(P) etant necessairement triviale, puisque
##  Aut(C2) = 1.
##
##  Version visee : GAP 4.15.
##
##  Version new-only V4 : les branches klein_A et klein_B utilisent une
##  unique enumeration d'orbites de noyaux et ne construisent plus les
##  epimorphismes vers V4.
##  Version C2-pairs : les trois branches C2 utilisent directement les
##  orbites de couples (Z,K). Les temps C2, C4 et D8 sont mesures separement.
##  Version new-only D8 : la branche whole_D8 utilise les orbites de noyaux.
##  La liste NormalSubgroups(R) est partagee entre les branches V4 et D8.
##
##  Application dans le catalogue des groupes parfaits :
##
##      P = PerfectGroup(1920,1),  Out(P) = D8,
##      P = PerfectGroup(1920,2),  Out(P) = D8.
##
##  La fonction optionnelle C2D8_VerifyPerfectGroups1920() permet de refaire
##  cette verification dans GAP a partir de Aut(P)/Inn(P).
##
##  ------------------------------------------------------------------------
##  DEFINITION UTILISEE
##  ------------------------------------------------------------------------
##
##  Une Z-phi-extension est ici une paire (S,phi), avec
##
##      1 -> Z=<z> -> S -> R -> 1,       |z|=2, z central,
##      phi : R=S/<z> -> Out(P)=D8.
##
##  D'apres l'equivalence d'Archer, (S1,phi1) et (S2,phi2) sont equivalentes
##  s'il existe un isomorphisme j:S1->S2 et pi dans Aut(P) tels que
##
##      (1) j(z) = z^pi pour z dans Z(P),
##      (2) phi2(jbar(r)) = pibar^(-1) phi1(r) pibar.
##
##  Ici Aut(P) agit trivialement sur Z(P)=C2. La condition (1) devient donc
##  simplement j(z)=z. Si H=Image(phi) est remplace par un representant fixe
##  de sa classe de conjugaison dans D8, seuls les elements de N_D8(H)
##  conservent ce representant. Pour un S et un z fixes, les Z-phi-classes
##  d'image H sont donc les orbites des epimorphismes
##
##      phi : S/<z> ->> H
##
##  sous les deux operations suivantes :
##
##      - precomposition par les automorphismes induits sur S/<z> par
##        Stab_Aut(S)(z);
##      - postcomposition par les automorphismes de H induits par conjugaison
##        par N_D8(H).
##
##  Le programme implemente exactement cette double action. Il ne remplace
##  pas N_D8(H) par Aut(H), car cela identifierait parfois trop de couplings,
##  notamment pour H=V4.
##
##  CONTROLE SPECIAL LORSQUE H EST UN C2
##
##  Le rectificatif joint au projet donne, pour chacune des trois classes de
##  sous-groupes C2 de D8, la formule plus simple suivante. On considere les
##  couples
##
##      (Z,K),  Z=<z> <= Z(S),  |Z|=2,  Z <= K normal dans S,
##              [S:K]=2.
##
##  Comme Aut(C2)=1 et comme N_D8(H) centralise H pour chacun des trois C2,
##  chaque orbite de tels couples sous Aut(S) contribue exactement une
##  Z-phi-classe. Les trois classes d'images
##
##      <r^2>, <s>, <sr>
##
##  doivent donc donner le meme nombre. Le programme applique directement
##  cette formule : il enumere une seule fois les sous-groupes K d'indice 2
##  de S, puis calcule leurs orbites sous le stabilisateur de z.
##  Pour n=4,6,...,32, il compare aussi automatiquement le resultat aux
##  valeurs publiees dans le PDF rectificatif; n=2 sert de test minimal
##  supplementaire (2 classes par branche C2 et 8 classes au total).
##
##  ------------------------------------------------------------------------
##  UTILISATION
##  ------------------------------------------------------------------------
##
##      Read("ZPhiClasses_C2_OutD8_AllS_FINAL_Optimized_GAP415.g");
##
##      d := C2D8_SubgroupClassData(8);;
##      C2D8_PrintSubgroupTable(d);
##
##      res := ZPhiClasses_C2_D8_AllS(2);;
##      res.totalClasses;       # doit valoir 8
##      res.centralProducts;    # doit valoir 2
##      res.byImageClass;
##      res.c2TheoryCheck;      # controle independant de la formule pour C2
##
##  IMPORTANT : terminer l'affectation par deux points-virgules. Le record
##  retourne ne conserve plus les groupes S, Aut(S), quotients, sous-groupes
##  ou homomorphismes : perGroup ne contient que les entiers necessaires aux
##  controles. Les references lourdes sont remplacees par fail apres chaque
##  groupe et GASMAN("collect") est force tous les 100 groupes seulement.
##  Si S=C2^d, Aut(S)=GL(d,2) n'est volontairement pas construit.
##
#############################################################################


#############################################################################
## 1. Action des automorphismes de S sur les elements de S.
#############################################################################

C2D8_AutActionOnElement := function(x, alpha)
    return Image(alpha, x);
end;


## Action naturelle sur les sous-groupes. Elle sert au controle independant
## de la formule theorique des branches d'image C2.
C2D8_AutActionOnSubgroup := function(K, alpha)
    return Image(alpha, K);
end;


#############################################################################
## 2. Les involutions centrales de S.
#############################################################################

C2D8_CentralInvolutions := function(S)
    return Filtered(AsList(Centre(S)), z -> Order(z) = 2);
end;


## Test sans construire Aut(S). Dans un groupe abelien, si tous les
## generateurs ont un ordre divisant 2, tout element a un ordre divisant 2.
C2D8_IsElementaryAbelian2Group := function(S)
    return Size(S) > 1
       and IsAbelian(S)
       and ForAll(GeneratorsOfGroup(S), x -> Order(x) <= 2);
end;


#############################################################################
## 3. Modele canonique de D8 et ses huit classes de conjugaison de
##    sous-groupes.
##
##    Convention : D8 est le groupe diedral d'ordre 8,
##
##       D8=<r,s | r^4=s^2=1, srs=r^-1>.
##
##    Il possede dix sous-groupes, repartis en huit classes de conjugaison.
##    Les seuls sous-groupes non normaux sont les quatre sous-groupes de
##    reflexion. Ils forment deux classes de conjugaison de taille 2.
#############################################################################

C2D8_SubgroupClassData := function(n)
    local D, els, r, rot, s, sr, specs, data, sp, H, N, entry, subgroupClasses, expectedClassSizes, expectedNormalizerSizes, autD8, innerD8;

    if not IsInt(n) or n < 1 then
        Error("n must be a positive integer");
    fi;

    D   := DihedralGroup(IsPermGroup, 8);
    els := AsList(D);

    r := First(els, x -> Order(x) = 4);
    if r = fail then
        Error("could not find a rotation of order 4 in D8");
    fi;

    rot := Subgroup(D, [r]);
    s := First(els, x -> Order(x) = 2 and not x in rot);
    if s = fail then
        Error("could not find a reflection in D8");
    fi;
    sr := s * r;

    ## Each item is [label, representative subgroup, displayed generators].
    specs := [
        ["trivial",      TrivialSubgroup(D),       []],
        ["central_C2",   Subgroup(D, [r^2]),       [r^2]],
        ["reflection_A", Subgroup(D, [s]),         [s]],
        ["reflection_B", Subgroup(D, [sr]),        [sr]],
        ["rotation_C4",  Subgroup(D, [r]),         [r]],
        ["klein_A",      Subgroup(D, [r^2, s]),    [r^2, s]],
        ["klein_B",      Subgroup(D, [r^2, sr]),   [r^2, sr]],
        ["whole_D8",     D,                         [r, s]]
    ];

    data := [];
    for sp in specs do
        H := sp[2];
        N := Normalizer(D, H);
        entry := rec(
            label             := sp[1],
            subgroup          := H,
            generators        := sp[3],
            order             := Size(H),
            structure         := StructureDescription(H),
            normalizer        := N,
            normalizerOrder   := Size(N),
            classSize         := Index(D, N),
            isNormal          := IsNormal(D, H),
            orderDividesN     := (n mod Size(H) = 0)
        );
        Add(data, entry);
    od;

    ## Structural verification of the table supplied in the article/project.
    expectedClassSizes      := [1, 1, 2, 2, 1, 1, 1, 1];
    expectedNormalizerSizes := [8, 8, 4, 4, 8, 8, 8, 8];

    if List(data, x -> x.classSize) <> expectedClassSizes then
        Error("unexpected conjugacy class sizes for subgroups of D8");
    fi;
    if List(data, x -> x.normalizerOrder) <> expectedNormalizerSizes then
        Error("unexpected normalizer orders for subgroups of D8");
    fi;
    if Number(data, x -> not x.isNormal) <> 2 then
        Error("exactly two subgroup classes of D8 must be non-normal");
    fi;
    if Sum(Filtered(data, x -> not x.isNormal), x -> x.classSize) <> 4 then
        Error("the two non-normal classes must contain four reflections");
    fi;

    subgroupClasses := ConjugacyClassesSubgroups(D);
    if Length(subgroupClasses) <> 8 then
        Error("D8 must have eight conjugacy classes of subgroups");
    fi;
    if Sum(data, x -> x.classSize) <> 10 then
        Error("D8 must have ten subgroups in total");
    fi;

    autD8 := AutomorphismGroup(D);
    innerD8 := InnerAutomorphismsAutomorphismGroup(autD8);
    if Size(autD8) <> 8 or Size(innerD8) <> 4 then
        Error("unexpected Aut(D8) or Inn(D8) order");
    fi;

    return rec(
        n                 := n,
        D8                := D,
        r                 := r,
        s                 := s,
        autD8             := autD8,
        innerD8           := innerD8,
        allClasses        := data,
        admissibleClasses := Filtered(data, x -> x.orderDividesN)
    );
end;


C2D8_PrintSubgroupTable := function(d)
    local x;

    Print("Subgroup conjugacy classes of D8 admissible for n=", d.n, "\n");
    Print("label            |H| class normal? |N_D8(H)| structure\n");
    for x in d.allClasses do
        Print(
            x.label, "  ",
            x.order, "    ",
            x.classSize, "     ",
            x.isNormal, "      ",
            x.normalizerOrder, "        ",
            x.structure
        );
        if x.orderDividesN then
            Print("   admissible\n");
        else
            Print("   excluded\n");
        fi;
    od;
end;


#############################################################################
## 4. Automorphisme induit sur R=S/<z>.
##
##    alpha appartient au stabilisateur de z; il stabilise donc <z> et
##    induit un automorphisme beta de R.
#############################################################################

C2D8_InducedAutomorphismOnQuotient := function(S, nat, R, alpha)
    local gensR, preimages, imagesR, beta;

    gensR    := GeneratorsOfGroup(R);
    preimages := List(gensR, q -> PreImagesRepresentative(nat, q));
    imagesR   := List(preimages, x -> Image(nat, Image(alpha, x)));

    beta := GroupHomomorphismByImages(R, R, gensR, imagesR);
    if beta = fail or not IsBijective(beta) then
        Error("failed to construct the automorphism induced on S/<z>");
    fi;
    return beta;
end;


#############################################################################
## 5. Signature d'un homomorphisme sur un systeme fixe de generateurs.
##
##    Elle permet de retrouver rapidement, dans la liste des epimorphismes,
##    les images obtenues par pre- ou postcomposition.
#############################################################################

C2D8_HomSignature := function(phi, gensR)
    return List(gensR, q -> Image(phi, q));
end;


#############################################################################
## 6. Orbites des epimorphismes R ->> H.
##
##    quotientAutomorphisms contient les generateurs de l'action induite par
##    Stab_Aut(S)(z). normalizer=N_D8(H) agit sur H par conjugaison.
#############################################################################

C2D8_EpimorphismOrbitData := function(R, H, quotientAutomorphisms, normalizer)
    local allHoms, epis, gensR, signatures, normalizerGenerators, seen, orbitRepresentatives, orbitSizes, orbitIndexLists, seed, queue, orbit, i, current, phi, beta, g, newSignature, pos;

    allHoms := AllHomomorphisms(R, H);
    epis    := Filtered(allHoms, IsSurjective);
    gensR   := GeneratorsOfGroup(R);

    signatures := List(epis, phi -> C2D8_HomSignature(phi, gensR));
    normalizerGenerators := GeneratorsOfGroup(normalizer);

    seen                 := List([1..Length(epis)], i -> false);
    orbitRepresentatives := [];
    orbitSizes           := [];
    orbitIndexLists      := [];

    for seed in [1..Length(epis)] do
        if not seen[seed] then
            queue := [seed];
            orbit := [];
            seen[seed] := true;

            while Length(queue) > 0 do
                current := queue[1];
                Remove(queue, 1);
                Add(orbit, current);
                phi := epis[current];

                ## Precomposition: phi is replaced by phi o beta.
                for beta in quotientAutomorphisms do
                    newSignature := List(
                        gensR,
                        q -> Image(phi, Image(beta, q))
                    );
                    pos := Position(signatures, newSignature);
                    if pos = fail then
                        Error("precomposition left the epimorphism list");
                    fi;
                    if not seen[pos] then
                        seen[pos] := true;
                        Add(queue, pos);
                    fi;
                od;

                ## Postcomposition by conjugation with g in N_D8(H).
                for g in normalizerGenerators do
                    newSignature := List(
                        gensR,
                        q -> Image(phi, q)^g
                    );
                    pos := Position(signatures, newSignature);
                    if pos = fail then
                        Error("normalizer conjugation left the epimorphism list");
                    fi;
                    if not seen[pos] then
                        seen[pos] := true;
                        Add(queue, pos);
                    fi;
                od;
            od;

            Add(orbitRepresentatives, epis[seed]);
            Add(orbitSizes, Length(orbit));
            Add(orbitIndexLists, orbit);
        fi;
    od;

    return rec(
        numberHomomorphisms       := Length(allHoms),
        numberEpimorphisms        := Length(epis),
        numberZPhiClasses         := Length(orbitRepresentatives),
        orbitRepresentatives      := orbitRepresentatives,
        representativeKernels     := List(orbitRepresentatives, Kernel),
        orbitSizes                := orbitSizes,
        orbitIndexLists           := orbitIndexLists
    );
end;


#############################################################################
## 7. Calcul new-only des branches V4 par orbites de noyaux.
##
##    Pour un epimorphisme phi:R->>V4, le noyau L est normal d'indice 4 et
##    R/L est non cyclique. Reciproquement, un tel L fournit exactement
##    |Aut(V4)|=6 epimorphismes. On classe d'abord les L sous l'action du
##    groupe A induit par Stab_Aut(S)(z), puis on calcule, pour chaque orbite,
##    le groupe CL des automorphismes induits sur R/L par Stab_A(L).
##
##    Le normalisateur dans D8 de chacun des deux V4 est D8 et son action sur
##    V4 a pour image un C2 dans Aut(V4)=S3. La contribution d'une orbite de
##    noyaux est donc le nombre de doubles classes |CL\S3/C2| :
##
##       3 si |CL|=1,  2 si |CL|=2,  1 si |CL|=3 ou 6.
##
##    Ce calcul est effectue UNE SEULE FOIS puis reutilise pour klein_A et
##    klein_B. Aucun appel a AllHomomorphisms(R,V4) ne subsiste.
#############################################################################

C2D8_AutomorphismGroupFromGenerators := function(G, gens)
    local id;
    id := IdentityMapping(G);
    if Length(gens) = 0 then
        return Group([id]);
    fi;
    return Group(gens);
end;


C2D8_V4ByKernelOrbits := function(R, inducedAutGroup, normalSubgroups, normalMs)
    local t0, candidates, L, Q, candidateMs, orbitMs, clMs, totalMs, kernelOrbits, orb, stabilizerL, natL, clGenerators, beta, CL, clSize, contribution, classes, numberCL1, numberCL2, numberCL3, numberCL6, answer;

    candidates := [];
    t0 := Runtime();
    for L in normalSubgroups do
        if Index(R, L) = 4 then
            Q := FactorGroup(R, L);
            if not IsCyclic(Q) then
                Add(candidates, L);
            fi;
            Q := fail;
        fi;
    od;
    candidateMs := Runtime() - t0;

    t0 := Runtime();
    kernelOrbits := Orbits(
        inducedAutGroup,
        candidates,
        C2D8_AutActionOnSubgroup
    );
    orbitMs := Runtime() - t0;

    classes := 0;
    numberCL1 := 0;
    numberCL2 := 0;
    numberCL3 := 0;
    numberCL6 := 0;
    t0 := Runtime();

    for orb in kernelOrbits do
        L := orb[1];
        stabilizerL := Stabilizer(
            inducedAutGroup,
            L,
            C2D8_AutActionOnSubgroup
        );
        natL := NaturalHomomorphismByNormalSubgroup(R, L);
        Q := Image(natL);

        clGenerators := [];
        for beta in GeneratorsOfGroup(stabilizerL) do
            Add(
                clGenerators,
                C2D8_InducedAutomorphismOnQuotient(R, natL, Q, beta)
            );
        od;
        CL := C2D8_AutomorphismGroupFromGenerators(Q, clGenerators);
        clSize := Size(CL);

        if clSize = 1 then
            contribution := 3;
            numberCL1 := numberCL1 + 1;
        elif clSize = 2 then
            contribution := 2;
            numberCL2 := numberCL2 + 1;
        elif clSize = 3 then
            contribution := 1;
            numberCL3 := numberCL3 + 1;
        elif clSize = 6 then
            contribution := 1;
            numberCL6 := numberCL6 + 1;
        else
            Error("unexpected subgroup size in Aut(V4)=S3: ", clSize);
        fi;
        classes := classes + contribution;

        L := fail;
        stabilizerL := fail;
        natL := fail;
        Q := fail;
        clGenerators := fail;
        CL := fail;
    od;

    clMs := Runtime() - t0;
    totalMs := normalMs + candidateMs + orbitMs + clMs;

    answer := rec(
        classes                 := classes,
        numberEpimorphisms      := 6 * Length(candidates),
        numberNormalSubgroups   := Length(normalSubgroups),
        numberCandidateKernels  := Length(candidates),
        numberKernelOrbits      := Length(kernelOrbits),
        numberCL1               := numberCL1,
        numberCL2               := numberCL2,
        numberCL3               := numberCL3,
        numberCL6               := numberCL6,
        normalSubgroupsMs       := normalMs,
        candidateFilteringMs    := candidateMs,
        kernelOrbitsMs          := orbitMs,
        inducedCLMs             := clMs,
        totalMs                 := totalMs
    );

    candidates := fail;
    kernelOrbits := fail;
    orb := fail;
    return answer;
end;


C2D8_V4CompactEpimorphismData := function(v4Data)
    return rec(
        numberHomomorphisms       := fail,
        numberEpimorphisms        := v4Data.numberEpimorphisms,
        numberZPhiClasses         := v4Data.classes,
        orbitRepresentatives      := fail,
        representativeKernels     := fail,
        orbitSizes                := fail,
        orbitIndexLists           := fail,
        representativesMaterialized := false,
        computedByKernelOrbits    := true,
        numberCandidateKernels    := v4Data.numberCandidateKernels,
        numberKernelOrbits        := v4Data.numberKernelOrbits
    );
end;


#############################################################################
## 8. Calcul new-only de la branche whole_D8 par orbites de noyaux.
##
##    Les noyaux L verifient R/L isomorphe a D8. Chaque L donne huit
##    epimorphismes. Pour une orbite de noyaux, la contribution vaut 2 si
##    l'action induite CL est contenue dans Inn(D8), et 1 sinon, puisque
##    Inn(D8) est normal d'indice 2 dans Aut(D8).
#############################################################################

C2D8_TransportAutomorphism := function(Q, H, isoQH, beta)
    local gensH, preimages, imagesH, gamma;

    gensH := GeneratorsOfGroup(H);
    preimages := List(
        gensH,
        h -> PreImagesRepresentative(isoQH, h)
    );
    imagesH := List(
        preimages,
        q -> Image(isoQH, Image(beta, q))
    );
    gamma := GroupHomomorphismByImages(H, H, gensH, imagesH);
    if gamma = fail or not IsBijective(gamma) then
        Error("failed to transport an automorphism from R/L to D8");
    fi;
    return gamma;
end;


C2D8_D8ByKernelOrbits := function(R, inducedAutGroup, normalSubgroups, H, innerH)
    local t0, filterMs, orbitMs, inducedMs, candidates, L, Q, kernelOrbits, orb, stabilizerL, natL, isoQH, clGenerators, beta, inducedQ, gamma, CL, allInner, contribution, classes, innerOnlyOrbits, outerOrbits, answer;

    candidates := [];
    t0 := Runtime();
    for L in normalSubgroups do
        if Index(R, L) = 8 then
            Q := FactorGroup(R, L);
            if IdGroup(Q) = [8,3] then
                Add(candidates, L);
            fi;
            Q := fail;
        fi;
    od;
    filterMs := Runtime() - t0;

    t0 := Runtime();
    kernelOrbits := Orbits(
        inducedAutGroup,
        candidates,
        C2D8_AutActionOnSubgroup
    );
    orbitMs := Runtime() - t0;

    classes := 0;
    innerOnlyOrbits := 0;
    outerOrbits := 0;
    t0 := Runtime();
    for orb in kernelOrbits do
        L := orb[1];
        stabilizerL := Stabilizer(
            inducedAutGroup,
            L,
            C2D8_AutActionOnSubgroup
        );
        natL := NaturalHomomorphismByNormalSubgroup(R, L);
        Q := Image(natL);
        isoQH := IsomorphismGroups(Q, H);
        if isoQH = fail then
            Error("candidate quotient is not isomorphic to the fixed D8");
        fi;

        clGenerators := [];
        for beta in GeneratorsOfGroup(stabilizerL) do
            inducedQ := C2D8_InducedAutomorphismOnQuotient(
                R,
                natL,
                Q,
                beta
            );
            gamma := C2D8_TransportAutomorphism(
                Q,
                H,
                isoQH,
                inducedQ
            );
            Add(clGenerators, gamma);
        od;
        CL := C2D8_AutomorphismGroupFromGenerators(H, clGenerators);
        allInner := ForAll(
            GeneratorsOfGroup(CL),
            gamma -> gamma in innerH
        );

        if allInner then
            contribution := 2;
            innerOnlyOrbits := innerOnlyOrbits + 1;
        else
            contribution := 1;
            outerOrbits := outerOrbits + 1;
        fi;
        classes := classes + contribution;

        L := fail;
        stabilizerL := fail;
        natL := fail;
        Q := fail;
        isoQH := fail;
        clGenerators := fail;
        inducedQ := fail;
        gamma := fail;
        CL := fail;
    od;
    inducedMs := Runtime() - t0;

    answer := rec(
        classes                := classes,
        numberEpimorphisms     := 8 * Length(candidates),
        numberNormalSubgroups  := Length(normalSubgroups),
        numberCandidateKernels := Length(candidates),
        numberKernelOrbits     := Length(kernelOrbits),
        innerOnlyKernelOrbits  := innerOnlyOrbits,
        outerKernelOrbits      := outerOrbits,
        candidateFilteringMs   := filterMs,
        kernelOrbitsMs         := orbitMs,
        inducedActionMs        := inducedMs,
        totalMs                := filterMs + orbitMs + inducedMs
    );

    candidates := fail;
    kernelOrbits := fail;
    orb := fail;
    return answer;
end;


C2D8_D8CompactEpimorphismData := function(d8Data)
    return rec(
        numberHomomorphisms       := fail,
        numberEpimorphisms        := d8Data.numberEpimorphisms,
        numberZPhiClasses         := d8Data.classes,
        orbitRepresentatives      := fail,
        representativeKernels     := fail,
        orbitSizes                := fail,
        orbitIndexLists           := fail,
        representativesMaterialized := false,
        computedByKernelOrbits    := true,
        numberCandidateKernels    := d8Data.numberCandidateKernels,
        numberKernelOrbits        := d8Data.numberKernelOrbits
    );
end;


#############################################################################
## 9. Calcul direct des trois branches C2 par les couples (Z,K).
##
##    Pour H=C2, Aut(H)=1. Apres fixation de z, les epimorphismes
##    S/<z>->>C2 correspondent exactement aux sous-groupes K d'indice 2 de
##    S qui contiennent z. Les Z-phi-classes sont leurs orbites sous
##    Stab_Aut(S)(z). Le meme resultat est reutilise pour central_C2,
##    reflection_A et reflection_B.
#############################################################################

C2D8_C2PairOrbitDataFromStabilizer := function(indexTwoSubgroups, z, stabAut)
    local admissibleK, pairOrbits;

    admissibleK := Filtered(indexTwoSubgroups, K -> z in K);
    pairOrbits := Orbits(
        stabAut,
        admissibleK,
        C2D8_AutActionOnSubgroup
    );

    return rec(
        admissibleIndexTwoSubgroups := admissibleK,
        pairOrbits                  := pairOrbits,
        pairOrbitRepresentatives   := List(pairOrbits, orb -> orb[1]),
        numberPairOrbits           := Length(pairOrbits),
        computedAsPrimaryC2Method  := true
    );
end;


C2D8_C2CompactEpimorphismData := function(pairData)
    return rec(
        numberHomomorphisms       := fail,
        numberEpimorphisms        :=
            Length(pairData.admissibleIndexTwoSubgroups),
        numberZPhiClasses         := pairData.numberPairOrbits,
        orbitRepresentatives      := fail,
        representativeKernels     := pairData.pairOrbitRepresentatives,
        orbitSizes                := List(pairData.pairOrbits, Length),
        orbitIndexLists           := fail,
        representativesMaterialized := true,
        computedByC2PairOrbits    := true
    );
end;


#############################################################################
## 10. Calcul pour un groupe S et une orbite d'involution centrale z.
#############################################################################

C2D8_ForMarkedCentralInvolution := function(S, autS, z, subgroupData, indexTwoSubgroups)
    local Z, nat, R, stabAut, quotientAutomorphisms, alpha, inducedAutGroup, normalSubgroupsR, normalMs, byImage, hrec, epiData, v4Data, d8Data, c2PairData, c2Ms, c4Ms, d8Ms, t0, elapsed, answer;

    Z   := Subgroup(S, [z]);
    nat := NaturalHomomorphismByNormalSubgroup(S, Z);
    R   := Image(nat);

    stabAut := Stabilizer(autS, z, C2D8_AutActionOnElement);

    quotientAutomorphisms := [];
    for alpha in GeneratorsOfGroup(stabAut) do
        Add(
            quotientAutomorphisms,
            C2D8_InducedAutomorphismOnQuotient(S, nat, R, alpha)
        );
    od;

    c2PairData := fail;
    c2Ms := 0;
    if indexTwoSubgroups <> fail then
        t0 := Runtime();
        c2PairData := C2D8_C2PairOrbitDataFromStabilizer(
            indexTwoSubgroups,
            z,
            stabAut
        );
        c2Ms := Runtime() - t0;
    fi;

    byImage := [];
    v4Data := fail;
    d8Data := fail;
    inducedAutGroup := fail;
    normalSubgroupsR := fail;
    normalMs := 0;
    c4Ms := 0;
    d8Ms := 0;
    for hrec in subgroupData.admissibleClasses do
        if hrec.order = 2 and c2PairData <> fail then
            epiData := C2D8_C2CompactEpimorphismData(c2PairData);
        elif hrec.label = "klein_A" or hrec.label = "klein_B" then
            if v4Data = fail then
                inducedAutGroup := C2D8_AutomorphismGroupFromGenerators(
                    R,
                    quotientAutomorphisms
                );
                t0 := Runtime();
                normalSubgroupsR := NormalSubgroups(R);
                normalMs := Runtime() - t0;
                v4Data := C2D8_V4ByKernelOrbits(
                    R,
                    inducedAutGroup,
                    normalSubgroupsR,
                    normalMs
                );
            fi;
            epiData := C2D8_V4CompactEpimorphismData(v4Data);
        elif hrec.label = "whole_D8" then
            if inducedAutGroup = fail then
                inducedAutGroup := C2D8_AutomorphismGroupFromGenerators(
                    R,
                    quotientAutomorphisms
                );
            fi;
            if normalSubgroupsR = fail then
                t0 := Runtime();
                normalSubgroupsR := NormalSubgroups(R);
                normalMs := Runtime() - t0;
            fi;
            d8Data := C2D8_D8ByKernelOrbits(
                R,
                inducedAutGroup,
                normalSubgroupsR,
                subgroupData.D8,
                subgroupData.innerD8
            );
            d8Ms := d8Data.totalMs;
            epiData := C2D8_D8CompactEpimorphismData(d8Data);
        else
            t0 := Runtime();
            epiData := C2D8_EpimorphismOrbitData(
                R,
                hrec.subgroup,
                quotientAutomorphisms,
                hrec.normalizer
            );
            elapsed := Runtime() - t0;
            if hrec.label = "rotation_C4" then
                c4Ms := c4Ms + elapsed;
            fi;
        fi;

        Add(byImage, rec(
            imageLabel       := hrec.label,
            imageOrder       := hrec.order,
            imageStructure   := hrec.structure,
            imageSubgroup    := hrec.subgroup,
            normalizer       := hrec.normalizer,
            normalizerOrder  := hrec.normalizerOrder,
            classSizeInD8    := hrec.classSize,
            epimorphismData  := epiData,
            numberClasses    := epiData.numberZPhiClasses
        ));
    od;

    answer := rec(
        z                     := z,
        Z                     := Z,
        quotient              := R,
        quotientStructure     := StructureDescription(R),
        naturalMap            := nat,
        stabilizerAutS        := stabAut,
        inducedAutomorphisms  := quotientAutomorphisms,
        v4KernelOrbitData     := v4Data,
        d8KernelOrbitData     := d8Data,
        c2PairOrbitData       := c2PairData,
        branchTimings         := rec(
            c2PairOrbitsMs    := c2Ms,
            c4EpimorphismsMs  := c4Ms,
            d8EpimorphismsMs  := 0,
            d8KernelOrbitsMs  := d8Ms,
            sharedNormalSubgroupsMs := normalMs
        ),
        byImageClass          := byImage,
        totalClasses          := Sum(byImage, x -> x.numberClasses)
    );

    inducedAutGroup := fail;
    normalSubgroupsR := fail;
    epiData := fail;
    return answer;
end;


#############################################################################
## 11. Formule fermee lorsque S est elementaire abelien.
##
##    Soit S=V=C2^d, vu comme espace vectoriel de dimension d sur F2, et
##    soit Z=<z> une droite. Alors Aut(S)=GL(V).
##
##    (a) GL(V) est transitif sur V-{0}: tout vecteur non nul se complete en
##        une base, et l'application envoyant une telle base sur une autre
##        est un element de GL(V). Il n'y a donc qu'une orbite de Z.
##
##    (b) Le stabilisateur GL(V)_z induit tout GL(V/Z). En effet, apres avoir
##        choisi un supplement W de Z, tout a dans GL(W) s'etend a V par
##        z |-> z. Cette extension fixe z et induit a sur V/Z.
##
##    (c) Les sous-groupes K contenant Z et d'indice 2 (resp. 4) dans V
##        correspondent aux hyperplans (resp. sous-espaces de codimension 2)
##        de V/Z. Le groupe GL(V/Z) est transitif sur les sous-espaces de
##        dimension fixee : on choisit une base de chaque sous-espace, on la
##        complete en une base de V/Z, puis on envoie une base complete sur
##        l'autre. Il y a donc une seule orbite de couples (Z,K) dans chacun
##        des deux cas, lorsque la dimension du quotient est suffisante.
##
##    (d) Pour une cible H=V4, un noyau K de codimension 2 ne determine pas
##        un unique epimorphisme : il en determine |Aut(V4)|=6. Cependant
##        GL(V/Z) est transitif sur TOUS les epimorphismes V/Z ->> V4. Si f
##        et g sont surjectifs, on choisit des bases adaptees a Ker(f) et
##        Ker(g), puis un automorphisme beta tel que g=f o beta. Les six
##        identifications possibles du quotient avec V4 sont donc deja
##        absorbees par la precomposition. Chaque classe de conjugaison V4
##        de D8 contribue exactement une Z-phi-classe.
##
##    (e) Aucun epimorphisme sur C4 n'existe, car tout element de V/Z a un
##        ordre divisant 2. Aucun epimorphisme sur D8 n'existe, car l'image
##        d'un groupe abelien est abelienne.
##
##    Ainsi, si q=|S/Z|=n :
##
##       image 1  : 1 classe, 1 epimorphisme;
##       image C2 : 1 classe par branche, q-1 epimorphismes par branche;
##       image V4 : 1 classe par branche, (q-1)(q-2) epimorphismes;
##       image C4 ou D8 : 0 classe.
##
##    Le nombre (q-1)(q-2) compte les couples ordonnes de formes lineaires
##    independantes sur V/Z. Cette branche ne construit ni GL(d,2), ni ses
##    stabilisateurs, ni aucune orbite.
#############################################################################

C2D8_ClosedEpimorphismDataElementary := function(q, hrec)
    local numberHoms, numberEpis, numberClasses;

    if hrec.label = "trivial" then
        numberHoms    := 1;
        numberEpis    := 1;
        numberClasses := 1;
    elif hrec.order = 2 then
        numberHoms    := q;
        numberEpis    := q - 1;
        numberClasses := 1;
    elif hrec.label = "rotation_C4" then
        ## Tout homomorphisme a son image dans l'unique C2 de C4.
        numberHoms    := q;
        numberEpis    := 0;
        numberClasses := 0;
    elif hrec.label = "klein_A" or hrec.label = "klein_B" then
        numberHoms    := q^2;
        if q >= 4 then
            numberEpis    := (q - 1) * (q - 2);
            numberClasses := 1;
        else
            numberEpis    := 0;
            numberClasses := 0;
        fi;
    elif hrec.label = "whole_D8" then
        ## Le nombre total d'homomorphismes n'est pas necessaire au calcul.
        numberHoms    := fail;
        numberEpis    := 0;
        numberClasses := 0;
    else
        Error("unexpected D8 subgroup class in elementary-abelian branch");
    fi;

    return rec(
        numberHomomorphisms       := numberHoms,
        numberEpimorphisms        := numberEpis,
        numberZPhiClasses         := numberClasses,
        orbitRepresentatives      := fail,
        representativeKernels     := fail,
        orbitSizes                := fail,
        orbitIndexLists           := fail,
        representativesMaterialized := false,
        computedByClosedFormula   := true
    );
end;


C2D8_ForElementaryAbelianGroup := function(S, smallGroupId, subgroupData)
    local z, Z, nat, R, q, sizeCopy, dimension, byImage, hrec, epiData, markedData, expectedTotal;

    z := First(GeneratorsOfGroup(S), x -> Order(x) = 2);
    if z = fail then
        Error("nontrivial elementary abelian 2-group has no generator of order 2");
    fi;

    Z   := Subgroup(S, [z]);
    nat := NaturalHomomorphismByNormalSubgroup(S, Z);
    R   := Image(nat);
    q   := Size(R);

    dimension := 0;
    sizeCopy := Size(S);
    while sizeCopy > 1 do
        if sizeCopy mod 2 <> 0 then
            Error("elementary abelian group does not have 2-power order");
        fi;
        sizeCopy := QuoInt(sizeCopy, 2);
        dimension := dimension + 1;
    od;

    byImage := [];
    for hrec in subgroupData.admissibleClasses do
        epiData := C2D8_ClosedEpimorphismDataElementary(q, hrec);
        Add(byImage, rec(
            imageLabel       := hrec.label,
            imageOrder       := hrec.order,
            imageStructure   := hrec.structure,
            imageSubgroup    := hrec.subgroup,
            normalizer       := hrec.normalizer,
            normalizerOrder  := hrec.normalizerOrder,
            classSizeInD8    := hrec.classSize,
            epimorphismData  := epiData,
            numberClasses    := epiData.numberZPhiClasses
        ));
    od;

    markedData := rec(
        z                       := z,
        Z                       := Z,
        quotient                := R,
        quotientStructure       := StructureDescription(R),
        naturalMap              := nat,
        stabilizerAutS          := fail,
        inducedAutomorphisms    := fail,
        automorphismGroupSkipped := true,
        computedByClosedFormula := true,
        byImageClass            := byImage,
        totalClasses            := Sum(byImage, x -> x.numberClasses)
    );

    if q mod 2 = 0 then
        markedData.c2PairOrbitData := rec(
            admissibleIndexTwoSubgroups := fail,
            pairOrbits                  := fail,
            pairOrbitRepresentatives   := fail,
            numberPairOrbits           := 1,
            computedByClosedFormula    := true
        );
    fi;

    if q = 1 then
        expectedTotal := 1;
    elif q = 2 then
        expectedTotal := 4;  # 1 + trois branches C2
    else
        expectedTotal := 6;  # 1 + trois C2 + deux V4
    fi;
    if markedData.totalClasses <> expectedTotal then
        Error("elementary-abelian closed formula produced an unexpected total");
    fi;

    return rec(
        smallGroupId                     := smallGroupId,
        S                                := S,
        structure                        := StructureDescription(S),
        autS                             := fail,
        automorphismGroupSkipped         := true,
        automorphismGroupDescription     := Concatenation(
            "GL(", String(dimension), ",2) (not constructed)"
        ),
        elementaryAbelianDimension       := dimension,
        elementaryAbelianClosedFormula   := true,
        indexTwoSubgroups                := fail,
        centralInvolutionOrbits          := fail,
        centralInvolutionOrbitRepresentatives := [z],
        numberCentralInvolutionOrbits    := 1,
        markedCentralInvolutions         := [markedData]
    );
end;


#############################################################################
## 12. Controle theorique pour les trois images C2 de D8.
##
##    Pour un S fixe, les sous-groupes K d'indice 2 sont exactement les
##    noyaux des epimorphismes S -> C2. Comme Aut(C2)=1, deux epimorphismes
##    sur C2 ont le meme noyau si et seulement s'ils sont egaux. Cette methode
##    construit donc tous les K une seule fois, sans passer par les
##    epimorphismes S/<z> -> H utilises par le calcul principal.
##
##    Apres choix d'un representant z de son orbite sous Aut(S), les orbites
##    de couples (Z=<z>,K) sont exactement les orbites des K contenant z sous
##    Stab_Aut(S)(z).
#############################################################################

C2D8_IndexTwoSubgroups := function(S)
    local C2, epis, kernels;

    C2 := CyclicGroup(IsPermGroup, 2);
    epis := Filtered(AllHomomorphisms(S, C2), IsSurjective);
    kernels := Set(List(epis, Kernel));

    if Length(kernels) <> Length(epis) then
        Error("two distinct epimorphisms S -> C2 unexpectedly have the same kernel");
    fi;
    if not ForAll(
        kernels,
        K -> Index(S, K) = 2 and IsNormal(S, K)
    ) then
        Error("the independently constructed kernels are not normal of index 2");
    fi;

    return kernels;
end;


C2D8_C2PairOrbitData := function(indexTwoSubgroups, markedData)
    return C2D8_C2PairOrbitDataFromStabilizer(
        indexTwoSubgroups,
        markedData.z,
        markedData.stabilizerAutS
    );
end;


## Valeurs du PDF (n=4,6,...,32), completees par le test minimal n=2.
## "zphi_classes_archer_cours_optimise_rectificatif_..._n32_complet".
## c2SingleBranch est la contribution de CHACUNE des trois classes de C2 :
## centre, reflexions A et reflexions B. totalD8 est la somme sur les huit
## classes de conjugaison de sous-groupes de D8.
    local table, pos;

    table := [
        rec(n :=  2, c2SingleBranch :=    2, totalD8 :=     8),
        rec(n :=  4, c2SingleBranch :=    8, totalD8 :=    44),
        rec(n :=  6, c2SingleBranch :=    4, totalD8 :=    16),
        rec(n :=  8, c2SingleBranch :=   42, totalD8 :=   261),
        rec(n := 10, c2SingleBranch :=    4, totalD8 :=    16),
        rec(n := 12, c2SingleBranch :=   24, totalD8 :=   132),
        rec(n := 14, c2SingleBranch :=    4, totalD8 :=    16),
        rec(n := 16, c2SingleBranch :=  286, totalD8 :=  2201),
        rec(n := 18, c2SingleBranch :=   10, totalD8 :=    40),
        rec(n := 20, c2SingleBranch :=   26, totalD8 :=   140),
        rec(n := 22, c2SingleBranch :=    4, totalD8 :=    16),
        rec(n := 24, c2SingleBranch :=  166, totalD8 :=  1050),
        rec(n := 26, c2SingleBranch :=    4, totalD8 :=    16),
        rec(n := 28, c2SingleBranch :=   24, totalD8 :=   130),
        rec(n := 30, c2SingleBranch :=    8, totalD8 :=    32),
        rec(n := 32, c2SingleBranch := 3026, totalD8 := 30363)
    ];

    pos := Position(List(table, x -> x.n), n);
    if pos = fail then
        return fail;
    fi;
    return table[pos];
end;


C2D8_VerifyC2Theory := function(result)
    local labels, entries, pairOrbitCount, branchCounts, label, hrec, normalizerActsTrivially, gd, md, mdCounts, expected, regressionChecked;

    if result.n mod 2 <> 0 then
        return rec(
            applicable := false,
            reason := "no subgroup of order 2 is admissible when 2 does not divide n"
        );
    fi;

    labels := ["central_C2", "reflection_A", "reflection_B"];
    entries := List(
        labels,
        label -> First(result.byImageClass, x -> x.label = label)
    );
    if fail in entries then
        Error("one of the three C2 image classes is missing");
    fi;

    ## Pour H=C2, la conjugaison induite par le normalisateur doit etre
    ## l'identite sur H. Cela reste vrai pour une reflexion, bien que son
    ## normalisateur n'ait que l'ordre 4.
    normalizerActsTrivially := true;
    for label in labels do
        hrec := First(
            result.subgroupClassData.allClasses,
            x -> x.label = label
        );
        if not ForAll(
            AsList(hrec.normalizer),
            g -> ForAll(AsList(hrec.subgroup), h -> h^g = h)
        ) then
            normalizerActsTrivially := false;
        fi;
    od;
    if not normalizerActsTrivially then
        Error("a D8 normalizer acts nontrivially on a C2 image");
    fi;

    pairOrbitCount := Sum(
        result.perGroup,
        gd -> Sum(
            gd.markedCentralInvolutions,
            md -> md.c2PairOrbitData.numberPairOrbits
        )
    );
    branchCounts := List(entries, e -> e.classes);

    ## Controle fin, groupe par groupe et orbite de z par orbite de z. Ce
    ## controle est plus fort que la seule egalite des totaux globaux.
    for gd in result.perGroup do
        for md in gd.markedCentralInvolutions do
            mdCounts := List(
                labels,
                label -> First(
                    md.byImageClass,
                    b -> b.imageLabel = label
                ).numberClasses
            );
            if not ForAll(
                mdCounts,
                x -> x = md.c2PairOrbitData.numberPairOrbits
            ) then
                Error(
                    "C2 theoretical formula failed for SmallGroup(",
                    gd.smallGroupId[1], ",", gd.smallGroupId[2], ")"
                );
            fi;
        od;
    od;

    if not ForAll(branchCounts, x -> x = pairOrbitCount) then
        Error("the three C2 branches do not equal the (Z,K)-orbit count");
    fi;

    regressionChecked := expected <> fail;
    if regressionChecked then
        if pairOrbitCount <> expected.c2SingleBranch then
            Error(
                "C2 regression failed: PDF expects ",
                expected.c2SingleBranch, " but GAP found ", pairOrbitCount
            );
        fi;
        if result.totalClasses <> expected.totalD8 then
            Error(
                "D8 regression failed: PDF expects total ",
                expected.totalD8, " but GAP found ", result.totalClasses
            );
        fi;
    fi;

    return rec(
        applicable                    := true,
        verified                      := true,
        formula                       := "one class per Aut(S)-orbit of pairs (Z,K), Z<=K and [S:K]=2",
        c2ImageLabels                 := labels,
        pairOrbitCount                := pairOrbitCount,
        branchCounts                  := branchCounts,
        totalOfThreeC2Branches        := Sum(branchCounts),
        theoreticalThreeBranchTotal   := 3 * pairOrbitCount,
        normalizerActsTriviallyOnC2   := normalizerActsTrivially,
        regressionChecked             := regressionChecked,
        regressionExpectation         := expected
    );
end;


#############################################################################
## 13. Compression des donnees conservees apres chaque groupe.
#############################################################################

C2D8_CompactGroupData := function(groupData)
    local compactMarked, md, compactMd;

    compactMarked := [];
    for md in groupData.markedCentralInvolutions do
        compactMd := rec(
            byImageClass := List(
                md.byImageClass,
                b -> rec(
                    imageLabel    := b.imageLabel,
                    numberClasses := b.numberClasses
                )
            )
        );
        if IsBound(md.c2PairOrbitData) then
            compactMd.c2PairOrbitData := rec(
                numberPairOrbits := md.c2PairOrbitData.numberPairOrbits
            );
        fi;
        if IsBound(md.v4KernelOrbitData) and md.v4KernelOrbitData <> fail then
            compactMd.v4KernelOrbitData := ShallowCopy(
                md.v4KernelOrbitData
            );
        else
            compactMd.v4KernelOrbitData := fail;
        fi;
        if IsBound(md.d8KernelOrbitData) and md.d8KernelOrbitData <> fail then
            compactMd.d8KernelOrbitData := ShallowCopy(
                md.d8KernelOrbitData
            );
        else
            compactMd.d8KernelOrbitData := fail;
        fi;
        if IsBound(md.branchTimings) then
            compactMd.branchTimings := ShallowCopy(md.branchTimings);
        fi;
        Add(compactMarked, compactMd);
    od;

    return rec(
        smallGroupId                  := groupData.smallGroupId,
        structure                     := groupData.structure,
        numberCentralInvolutionOrbits :=
            groupData.numberCentralInvolutionOrbits,
        markedCentralInvolutions      := compactMarked,
        dataCompacted                 := true
    );
end;


#############################################################################
## 14. Fonction principale.
##
##    Entree : n=|R|.
##    Le programme parcourt tous les SmallGroup(2*n,i), donc tous les groupes
##    auxiliaires S d'ordre 2n disponibles dans la Small Groups Library.
##
##    Pour chaque S :
##      - si S est elementaire abelien, on applique la formule fermee de la
##        section 11 et Aut(S)=GL(d,2) n'est jamais construit;
##      - sinon Aut(S) est calcule une seule fois pour ce groupe;
##      - on prend un representant de chaque orbite d'involutions centrales;
##      - les deux branches V4 sont calculees une seule fois par orbites de
##        noyaux et whole_D8 utilise aussi les orbites de noyaux;
##      - NormalSubgroups(R) est calcule une seule fois pour V4 et D8;
##      - seules les images triviale et C4 utilisent encore la fonction
##        generique d'enumeration des homomorphismes;
##      - les donnees lourdes sont liberees apres chaque groupe et une
##        collecte complete est forcee tous les 100 groupes et a la fin.
#############################################################################

ZPhiClasses_C2_D8_AllS := function(n)
    local orderS, numberGroups, subgroupData, totalsByImage, perGroup, i, S, autS, centralInvolutions, zOrbits, zReps, groupData, compactGroupData, z, markedData, b, pos, totalClasses, centralProducts, totalMarkedOrbits, result, indexTwoSubgroups, elementaryAbelianGroupsOptimized, totalGCms, gcStart, v4KernelComputations, v4CandidateKernels, v4KernelOrbits, v4CL1, v4CL2, v4CL3, v4CL6, v4TotalMs, d8KernelComputations, d8CandidateKernels, d8KernelOrbits, d8InnerOnly, d8Outer, d8TotalMs, sharedNormalTotalMs, c2IndexTwoTotalMs, c2PairTotalMs, c4TotalMs, t0;

    if not IsInt(n) or n < 1 then
        Error("n must be a positive integer");
    fi;

    orderS      := 2 * n;
    numberGroups := NumberSmallGroups(orderS);
    subgroupData := C2D8_SubgroupClassData(n);

    totalsByImage := List(
        subgroupData.admissibleClasses,
        h -> rec(
            label            := h.label,
            order            := h.order,
            structure        := h.structure,
            classSizeInD8    := h.classSize,
            normalizerOrder  := h.normalizerOrder,
            classes          := 0,
            epimorphisms     := 0
        )
    );

    perGroup          := [];
    totalClasses      := 0;
    centralProducts   := 0;
    totalMarkedOrbits := 0;
    elementaryAbelianGroupsOptimized := 0;
    totalGCms := 0;
    v4KernelComputations := 0;
    v4CandidateKernels := 0;
    v4KernelOrbits := 0;
    v4CL1 := 0;
    v4CL2 := 0;
    v4CL3 := 0;
    v4CL6 := 0;
    v4TotalMs := 0;
    d8KernelComputations := 0;
    d8CandidateKernels := 0;
    d8KernelOrbits := 0;
    d8InnerOnly := 0;
    d8Outer := 0;
    d8TotalMs := 0;
    sharedNormalTotalMs := 0;
    c2IndexTwoTotalMs := 0;
    c2PairTotalMs := 0;
    c4TotalMs := 0;

    Print("ZPhiClasses_C2_D8_AllS(", n, ")\n");
    Print("SmallGroups of order ", orderS, " to test = ", numberGroups, "\n");
    C2D8_PrintSubgroupTable(subgroupData);

    for i in [1..numberGroups] do
        S := SmallGroup(orderS, i);

        if C2D8_IsElementaryAbelian2Group(S) then
            ## Cas ferme : aucune construction de GL(d,2), de stabilisateur,
            ## de sous-groupes d'indice 2/4, ni d'orbites d'epimorphismes.
            groupData := C2D8_ForElementaryAbelianGroup(
                S,
                [orderS, i],
                subgroupData
            );
            elementaryAbelianGroupsOptimized :=
                elementaryAbelianGroupsOptimized + 1;
            Print(
                "elementary abelian shortcut for SmallGroup(",
                orderS, ",", i, "): ",
                groupData.automorphismGroupDescription, "\n"
            );
        else
            autS := AutomorphismGroup(S); # calcule une fois et conserve

            centralInvolutions := C2D8_CentralInvolutions(S);
            zOrbits := Orbits(
                autS,
                centralInvolutions,
                C2D8_AutActionOnElement
            );
            ## Orbits(...) returns ordinary lists. Taking orb[1] is both
            ## cheaper and more portable than Representative(orb).
            zReps := List(zOrbits, orb -> orb[1]);

            ## Calcul independant, une seule fois par S, des noyaux d'indice 2.
            if n mod 2 = 0 then
                t0 := Runtime();
                indexTwoSubgroups := C2D8_IndexTwoSubgroups(S);
                c2IndexTwoTotalMs := c2IndexTwoTotalMs + Runtime() - t0;
            else
                indexTwoSubgroups := fail;
            fi;

            groupData := rec(
                smallGroupId               := [orderS, i],
                S                          := S,
                structure                  := StructureDescription(S),
                autS                       := autS,
                automorphismGroupSkipped   := false,
                elementaryAbelianClosedFormula := false,
                indexTwoSubgroups          := indexTwoSubgroups,
                centralInvolutionOrbits    := zOrbits,
                centralInvolutionOrbitRepresentatives := zReps,
                numberCentralInvolutionOrbits := Length(zReps),
                markedCentralInvolutions   := []
            );

            for z in zReps do
                markedData := C2D8_ForMarkedCentralInvolution(
                    S,
                    autS,
                    z,
                    subgroupData,
                    indexTwoSubgroups
                );
                Add(groupData.markedCentralInvolutions, markedData);
            od;
        fi;

        ## Agregation commune aux branches generale et elementaire abelienne.
        for markedData in groupData.markedCentralInvolutions do
            totalMarkedOrbits := totalMarkedOrbits + 1;
            totalClasses      := totalClasses + markedData.totalClasses;

            if IsBound(markedData.v4KernelOrbitData)
               and markedData.v4KernelOrbitData <> fail then
                v4KernelComputations := v4KernelComputations + 1;
                v4CandidateKernels := v4CandidateKernels +
                    markedData.v4KernelOrbitData.numberCandidateKernels;
                v4KernelOrbits := v4KernelOrbits +
                    markedData.v4KernelOrbitData.numberKernelOrbits;
                v4CL1 := v4CL1 + markedData.v4KernelOrbitData.numberCL1;
                v4CL2 := v4CL2 + markedData.v4KernelOrbitData.numberCL2;
                v4CL3 := v4CL3 + markedData.v4KernelOrbitData.numberCL3;
                v4CL6 := v4CL6 + markedData.v4KernelOrbitData.numberCL6;
                v4TotalMs := v4TotalMs +
                    markedData.v4KernelOrbitData.totalMs;
            fi;
            if IsBound(markedData.d8KernelOrbitData)
               and markedData.d8KernelOrbitData <> fail then
                d8KernelComputations := d8KernelComputations + 1;
                d8CandidateKernels := d8CandidateKernels +
                    markedData.d8KernelOrbitData.numberCandidateKernels;
                d8KernelOrbits := d8KernelOrbits +
                    markedData.d8KernelOrbitData.numberKernelOrbits;
                d8InnerOnly := d8InnerOnly +
                    markedData.d8KernelOrbitData.innerOnlyKernelOrbits;
                d8Outer := d8Outer +
                    markedData.d8KernelOrbitData.outerKernelOrbits;
            fi;
            if IsBound(markedData.branchTimings) then
                c2PairTotalMs := c2PairTotalMs +
                    markedData.branchTimings.c2PairOrbitsMs;
                c4TotalMs := c4TotalMs +
                    markedData.branchTimings.c4EpimorphismsMs;
                d8TotalMs := d8TotalMs +
                    markedData.branchTimings.d8KernelOrbitsMs;
                sharedNormalTotalMs := sharedNormalTotalMs +
                    markedData.branchTimings.sharedNormalSubgroupsMs;
            fi;

            for b in markedData.byImageClass do
                pos := Position(
                    List(totalsByImage, x -> x.label),
                    b.imageLabel
                );
                totalsByImage[pos].classes :=
                    totalsByImage[pos].classes + b.numberClasses;
                totalsByImage[pos].epimorphisms :=
                    totalsByImage[pos].epimorphisms +
                    b.epimorphismData.numberEpimorphisms;
            od;
        od;

        compactGroupData := C2D8_CompactGroupData(groupData);
        Add(perGroup, compactGroupData);

        ## Aucune reference aux objets lourds du groupe courant ne doit
        ## subsister hors de l'entree compacte ajoutee ci-dessus.
        S := fail;
        autS := fail;
        centralInvolutions := fail;
        zOrbits := fail;
        zReps := fail;
        z := fail;
        indexTwoSubgroups := fail;
        markedData := fail;
        b := fail;
        groupData := fail;
        compactGroupData := fail;

        if i mod 100 = 0 or i = numberGroups then
            gcStart := Runtime();
            GASMAN("collect");
            totalGCms := totalGCms + Runtime() - gcStart;
        fi;

        if i mod 100 = 0 then
            Print("processed ", i, " / ", numberGroups, " SmallGroups\n");
        fi;
    od;

    pos := Position(List(totalsByImage, x -> x.label), "trivial");
    if pos = fail then
        Error("the trivial image class is missing");
    fi;
    centralProducts := totalsByImage[pos].classes;

    result := rec(
        n                            := n,
        orderS                       := orderS,
        applicablePerfectGroups      := [[1920,1], [1920,2]],
        outStructure                 := "D8",
        centreStructure              := "C2",
        actionOnCentre               := "trivial",
        subgroupClassData            := subgroupData,
        smallGroupsTested             := numberGroups,
        elementaryAbelianGroupsOptimized :=
            elementaryAbelianGroupsOptimized,
        markedCentralInvolutionOrbits := totalMarkedOrbits,
        centralProducts               := centralProducts,
        nontrivialCouplingClasses      := totalClasses-centralProducts,
        totalClasses                  := totalClasses,
        byImageClass                  := totalsByImage,
        v4KernelOptimization          := rec(
            enabled                  := true,
            computedOnceForBothV4    := true,
            kernelComputations       := v4KernelComputations,
            candidateKernels         := v4CandidateKernels,
            kernelOrbits             := v4KernelOrbits,
            numberCL1                := v4CL1,
            numberCL2                := v4CL2,
            numberCL3                := v4CL3,
            numberCL6                := v4CL6,
            totalMs                  := v4TotalMs
        ),
        d8KernelOptimization          := rec(
            enabled                  := true,
            kernelComputations       := d8KernelComputations,
            candidateKernels         := d8CandidateKernels,
            kernelOrbits             := d8KernelOrbits,
            innerOnlyKernelOrbits    := d8InnerOnly,
            outerKernelOrbits        := d8Outer,
            totalMs                  := d8TotalMs
        ),
        branchTimings                 := rec(
            c2IndexTwoSubgroupsMs    := c2IndexTwoTotalMs,
            c2PairOrbitsMs           := c2PairTotalMs,
            c4EpimorphismsMs         := c4TotalMs,
            d8EpimorphismsMs         := 0,
            d8KernelOrbitsMs         := d8TotalMs,
            sharedNormalSubgroupsMs  := sharedNormalTotalMs
        ),
        garbageCollectionInterval     := 100,
        garbageCollectionMs           := totalGCms,
        perGroupDataCompacted          := true,
        perGroup                      := perGroup
    );

    ## Arrete immediatement avec une erreur si la formule theorique pour C2,
    ## l'egalite des trois branches, ou une valeur tabulee du PDF n'est pas
    ## retrouvee.
    result.c2TheoryCheck := C2D8_VerifyC2Theory(result);

    Print("\nSummary\n");
    Print("n = ", n, "\n");
    Print("SmallGroups tested = ", numberGroups, "\n");
    Print("elementary abelian groups treated by closed formula = ",
          elementaryAbelianGroupsOptimized, "\n");
    Print("marked central involution orbits = ", totalMarkedOrbits, "\n");
    Print("central products (trivial coupling) = ", centralProducts, "\n");
    Print("nontrivial coupling classes = ",
          result.nontrivialCouplingClasses, "\n");
    Print("total Z-phi classes = ", totalClasses, "\n");
    Print("V4 new-only kernel computations = ",
          v4KernelComputations, " (shared by klein_A and klein_B)\n");
    Print("V4 candidate kernels = ", v4CandidateKernels,
          "; kernel orbits = ", v4KernelOrbits, "\n");
    Print("D8 new-only kernel computations = ",
          d8KernelComputations, "\n");
    Print("D8 candidate kernels = ", d8CandidateKernels,
          "; kernel orbits = ", d8KernelOrbits, "\n");
    Print("D8 inner-only / outer kernel orbits = ",
          d8InnerOnly, "/", d8Outer, "\n");
    Print("C2 index-two subgroup time (ms) = ",
          c2IndexTwoTotalMs, "\n");
    Print("C2 pair-orbit time (ms) = ", c2PairTotalMs, "\n");
    Print("C4 epimorphism time (ms) = ", c4TotalMs, "\n");
    Print("D8 kernel-orbit time (ms) = ", d8TotalMs, "\n");
    Print("shared NormalSubgroups time for V4/D8 (ms) = ",
          sharedNormalTotalMs, "\n");
    Print("forced garbage collection time (ms) = ", totalGCms, "\n");
    Print("classes by image subgroup class:\n");
    for b in totalsByImage do
        Print("  ", b.label, " : ", b.classes,
              "  (epimorphisms before orbit reduction = ",
              b.epimorphisms, ")\n");
    od;
    if result.c2TheoryCheck.applicable then
        Print("C2 theory check: ",
              result.c2TheoryCheck.pairOrbitCount,
              " pair-orbits for each C2 branch; three-branch total = ",
              result.c2TheoryCheck.totalOfThreeC2Branches, "\n");
        if result.c2TheoryCheck.regressionChecked then
            Print("PDF regression for n=", n, ": verified\n");
        else
            Print("No tabulated PDF regression value for n=", n,
                  "; the structural C2 formula was nevertheless verified\n");
        fi;
    fi;

    return result;
end;


#############################################################################
## 15. Verification optionnelle de Out(PerfectGroup(1920,1)) et
##    Out(PerfectGroup(1920,2)).
##
##    Cette fonction peut etre couteuse : elle calcule Aut(P). Elle n'est pas
##    appelee automatiquement par le calcul des Z-phi-classes.
#############################################################################

C2D8_VerifyPerfectGroups1920 := function()
    local ans, x, P, ZP, autP, innP, outP, iso, outPerm, z, fixesCentre;

    ans := [];
    for x in [1,2] do
        P  := PerfectGroup(1920, x);
        ZP := Centre(P);
        if Size(ZP) <> 2 then
            Error("PerfectGroup(1920,", x, ") does not have centre C2");
        fi;
        z := First(AsList(ZP), y -> Order(y) = 2);

        autP := AutomorphismGroup(P);
        innP := InnerAutomorphismsAutomorphismGroup(autP);
        outP := FactorGroup(autP, innP);
        iso := IsomorphismPermGroup(outP);
        outPerm := Image(iso);

        fixesCentre := ForAll(
            GeneratorsOfGroup(autP),
            alpha -> Image(alpha, z) = z
        );

        Add(ans, rec(
            perfectGroupId := [1920, x],
            centreOrder    := Size(ZP),
            outOrder       := Size(outPerm),
            outId          := IdGroup(outPerm),
            outStructure   := StructureDescription(outPerm),
            fixesCentre    := fixesCentre,
            isD8           := IdGroup(outPerm) = [8,3]
        ));
    od;

    if not ForAll(ans, a -> a.isD8 and a.fixesCentre) then
        Error("the expected Out(P)=D8 verification failed");
    fi;

    return ans;
end;


#############################################################################
## 16. Test minimal.
##
##     Pour n=2, seules les images 1 et C2 sont possibles. D8 a trois classes
##     de sous-groupes C2. Les deux groupes auxiliaires C4 et V4 fournissent
##     chacun une classe pour le coupling trivial et une classe pour chacune
##     des trois images C2. Le total attendu est donc
##
##         2 * (1+3) = 8.
#############################################################################

C2D8_SelfTest := function()
    local res;

    res := ZPhiClasses_C2_D8_AllS(2);
    if res.centralProducts <> 2 then
        Error("self-test failed: expected 2 central products");
    fi;
    if res.totalClasses <> 8 then
        Error("self-test failed: expected 8 Z-phi classes");
    fi;
    if not res.c2TheoryCheck.verified then
        Error("self-test failed: C2 theoretical check was not verified");
    fi;
    if res.c2TheoryCheck.pairOrbitCount <> 2 then
        Error("self-test failed: expected 2 (Z,K)-orbits per C2 branch");
    fi;
    if res.elementaryAbelianGroupsOptimized <> 1 then
        Error("self-test failed: the V4 shortcut was not used exactly once");
    fi;
    return true;
end;

##################### calcul des valeurs manquantes de zphi-classes C2 D8 ####
#Read("ZPhiClasses_C2_OutD8_AllS_FINAL_Optimized_GAP415.g");;

missingEven := [34,36..62];;
evenResults := [];;

LogTo("ZPhiClasses_C2_D8_n34_to_n62.log");;

for n in missingEven do
    Print("\n========================================\n");
    Print("Début du calcul pour n = ", n, "\n");
    Print("|S| = ", 2*n, "; |E| = ", 1920*n, "\n");
    Print("========================================\n");

    t0 := Runtime();;
    res := ZPhiClasses_C2_D8_AllS(n);;
    t1 := Runtime();;

    Add(evenResults, rec(
        n            := n,
        auxiliaryOrder := 2*n,
        extensionOrder := 1920*n,
        totalClasses := res.totalClasses,
        runtimeMs    := t1-t0
    ));;

    Print(
        "RESULTAT n = ", n,
        " : N(n) = ", res.totalClasses,
        "; temps = ", Float((t1-t0)/60000),
        " minutes\n"
    );

    # Libération des objets du groupe qui vient d'être traité.
    res := fail;;

    # Un seul ramassage forcé entre deux valeurs de n.
    GASMAN("collect");;
od;

LogTo();;

#################### Afficher le tableau final ####

for r in evenResults do
    Print(
        "n = ", r.n,
        " ; |S| = ", r.auxiliaryOrder,
        " ; |E| = ", r.extensionOrder,
        " ; N(n) = ", r.totalClasses,
        " ; temps = ", Float(r.runtimeMs/60000),
        " minutes\n"
    );
od;

######################## Calcul instantané des cas impairs

oddResults := List(
    [33,35..63],
    n -> rec(
        n := n,
        extensionOrder := 1920*n,
        totalClasses := NrSmallGroups(n)
    )
);;

for r in oddResults do
    Print(
        "n = ", r.n,
        " ; |E| = ", r.extensionOrder,
        " ; N(n) = ", r.totalClasses,
        " (produits directs uniquement)\n"
    );
od;

####################""

# Example usage:
# gap> Read("ZPhiClasses_C2_OutD8_AllS_github_clean.g");
# gap> ZPhiClasses_C2_OutD8_AllS(8);
# gap> ZPhiClasses_C2_OutD8_AllS(16);