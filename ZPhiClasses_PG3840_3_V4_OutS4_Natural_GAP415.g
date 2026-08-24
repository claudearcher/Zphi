#############################################################################
##
##  source : zphi a method by Claude Archer, described in his PhD thesis
##  "Classification of Group Extensions", Université Libre de Bruxelles (2002)
##
##  ZPhiClasses_PG3840_3_V4_OutS4_Natural_GAP415.g
##
##  Z-phi-classes for P = PerfectGroup(3840,3)
##
##      Z(P)   = V4,
##      Out(P) = S4,
##
##  where S4 acts on Z(P) by conjugation on its normal Klein subgroup
##
##      A = < (1,2)(3,4), (1,3)(2,4) >.
##
##  The action has image S3 and kernel A:
##
##      S4/A is isomorphic to S3.
##
##  GAP compatibility: 4.15.x.
##
##  Mathematical convention
##  -----------------------
##  The parameter n is the order of the quotient E/P.  For every group S
##  of order 4*n, the algorithm considers a normal subgroup Z isomorphic
##  to V4, a surjection f:S -> U <= S4 with Z <= Ker(f), and an ordered
##  isomorphism i:A -> Z.  It retains precisely the triples satisfying
##
##      i(a)^s = i(a^f(s))
##
##  for a in a fixed basis of A and for generators s of S.  In contrast
##  with the trivial-action case, Z need not be central in S.
##
##  Equivalence is generated simultaneously by Aut(S) and by the
##  normalizer N_S4(U).  A normalizer element changes BOTH f and the
##  ordered identification A -> Z.  This simultaneous action is essential.
##
##  The eleven representatives U below are the eleven S4-conjugacy classes
##  of subgroups of S4.  Only those with |U| dividing n are considered.
##
##  Memory discipline
##  -----------------
##  Expensive variables are assigned fail after each SmallGroup.  A forced
##  GASMAN("collect") is performed only every 100 groups.  Every function
##  uses a single GAP local declaration.
##
#############################################################################


#############################################################################
## 1. Elementary helpers
#############################################################################

PG3S4_IsV4 := function(V)
    local elements;

    if Size(V) <> 4 or not IsAbelian(V) then
        return false;
    fi;
    elements := Elements(V);
    return ForAll(elements, x -> x = One(V) or Order(x) = 2);
end;


PG3S4_OrderedBasesV4 := function(V)
    local nonidentity, bases, x, y;

    if not PG3S4_IsV4(V) then
        Error("PG3S4_OrderedBasesV4 expects a Klein four group");
    fi;
    nonidentity := Filtered(Elements(V), x -> x <> One(V));
    bases := [];
    for x in nonidentity do
        for y in nonidentity do
            if x <> y then
                Add(bases, [x,y]);
            fi;
        od;
    od;
    if Length(bases) <> 6 then
        Error("a V4 must have exactly six ordered bases");
    fi;
    return bases;
end;


PG3S4_IsElementaryAbelian2Group := function(S)
    local one;

    if not IsAbelian(S) then
        return false;
    fi;
    one := One(S);
    return ForAll(GeneratorsOfGroup(S), x -> x = one or Order(x) = 2);
end;


PG3S4_RankElementaryAbelian2Group := function(S)
    local q, d;

    if not PG3S4_IsElementaryAbelian2Group(S) then
        Error("the group is not elementary abelian of exponent two");
    fi;
    q := Size(S);
    d := 0;
    while q > 1 do
        if q mod 2 <> 0 then
            Error("the group order is not a power of two");
        fi;
        q := q/2;
        d := d+1;
    od;
    return d;
end;


#############################################################################
## 2. Canonical S4 data and its eleven subgroup classes
#############################################################################

PG3S4_ActionData := function()
    local G, z1, z2, A, actionMap, image, kernel, c4, data;

    G := SymmetricGroup(4);
    z1 := (1,2)(3,4);
    z2 := (1,3)(2,4);
    A := Group(z1,z2);
    actionMap := ActionHomomorphism(G, Elements(A), OnPoints);
    image := Image(actionMap);
    kernel := Kernel(actionMap);

    if not PG3S4_IsV4(A) or not IsNormal(G,A) then
        Error("the canonical centre A is not the normal Klein subgroup");
    fi;
    if Size(image) <> 6 or kernel <> A then
        Error("unexpected action of S4 on its normal Klein subgroup");
    fi;

    c4 := Group((1,2,3,4));
    data := rec(
        outerGroup := G,
        centre := A,
        centreBasis := [z1,z2],
        centreAction := actionMap,
        centreActionImage := image,
        centreActionKernel := kernel,
        standardC4 := c4
    );
    return data;
end;


PG3S4_ImageClasses := function(data)
    local G, z1, z2, A, c4;

    G := data.outerGroup;
    z1 := data.centreBasis[1];
    z2 := data.centreBasis[2];
    A := data.centre;
    c4 := data.standardC4;

    return [
        rec(label := "trivial", U := TrivialSubgroup(G)),
        rec(label := "C2_transposition", U := Group((1,2))),
        rec(label := "C2_double_transposition", U := Group(z1)),
        rec(label := "C3", U := Group((1,2,3))),
        rec(label := "C4", U := c4),
        rec(label := "V4_normal", U := A),
        rec(label := "V4_nonnormal", U := Group((1,2),(3,4))),
        rec(label := "S3", U := Stabilizer(G,4)),
        rec(label := "D8", U := Normalizer(G,c4)),
        rec(label := "A4", U := AlternatingGroup(4)),
        rec(label := "S4", U := G)
    ];
end;


#############################################################################
## 3. Surjections S -> U and normal V4 subgroups of S
#############################################################################

PG3S4_GQuotientsIncludingTrivial := function(S,U)
    local gensS, oneU, images;

    if Size(U) > 1 then
        return GQuotients(S,U);
    fi;
    gensS := GeneratorsOfGroup(S);
    oneU := One(U);
    images := List(gensS, x -> oneU);
    return [GroupHomomorphismByImages(S,U,gensS,images)];
end;


PG3S4_MapCode := function(f,gensS,elementsU)
    return List(gensS, x -> Position(elementsU,Image(f,x)));
end;


PG3S4_OrientedMaps := function(S,U,gensS)
    local quotientMaps, autU, autElements, elementsU, maps, codes,
          f0, beta, f, code;

    quotientMaps := PG3S4_GQuotientsIncludingTrivial(S,U);
    autU := AutomorphismGroup(U);
    autElements := Elements(autU);
    elementsU := Elements(U);
    maps := [];
    codes := [];

    for f0 in quotientMaps do
        for beta in autElements do
            f := f0*beta;
            code := PG3S4_MapCode(f,gensS,elementsU);
            if Position(codes,code) = fail then
                Add(maps,f);
                Add(codes,code);
            fi;
        od;
    od;
    return rec(
        quotientMaps := quotientMaps,
        maps := maps,
        codes := codes,
        elementsU := elementsU
    );
end;


PG3S4_NormalV4Subgroups := function(S)
    local normals;

    normals := NormalSubgroups(S);
    return Filtered(normals, Z -> PG3S4_IsV4(Z));
end;


#############################################################################
## 4. Markings A -> Z and compatibility with conjugation
#############################################################################

PG3S4_CanonicalToMarked := function(a,basis,data)
    local oneA;

    oneA := One(data.centre);
    if a = oneA then
        return One(Group(basis));
    elif a = data.centreBasis[1] then
        return basis[1];
    elif a = data.centreBasis[2] then
        return basis[2];
    elif a = data.centreBasis[1]*data.centreBasis[2] then
        return basis[1]*basis[2];
    fi;
    Error("element outside the canonical Klein centre");
end;


PG3S4_TransportBasisByTarget := function(basis,g,data)
    local ginv;

    # ConjugatorAutomorphism(U,g) sends u to u^g.  Therefore the compatible
    # marking after f -> f^g is i'(a)=i(a^(g^-1)).
    ginv := g^-1;
    return List(data.centreBasis, a ->
        PG3S4_CanonicalToMarked(a^ginv,basis,data));
end;


PG3S4_IsCompatible := function(f,Z,basis,gensS,data)
    local oneU, s, u, j, lhs, rhs, aimage;

    oneU := One(Range(f));
    if not ForAll(GeneratorsOfGroup(Z), z -> Image(f,z) = oneU) then
        return false;
    fi;
    for s in gensS do
        u := Image(f,s);
        for j in [1,2] do
            lhs := basis[j]^s;
            aimage := data.centreBasis[j]^u;
            rhs := PG3S4_CanonicalToMarked(aimage,basis,data);
            if lhs <> rhs then
                return false;
            fi;
        od;
    od;
    return true;
end;


#############################################################################
## 5. Data shared by all image branches for one S
#############################################################################

PG3S4_PrepareSContext := function(S)
    local gensS, normalV4s, bases, autS, autGens, autZ, autBasis,
          alpha, rowZ, rowBasis, zi, bi, Z2, z2, basis2, b2, bRow;

    if Size(S) mod 4 <> 0 then
        return rec(valid := false, normalV4s := []);
    fi;
    gensS := GeneratorsOfGroup(S);
    normalV4s := PG3S4_NormalV4Subgroups(S);
    if Length(normalV4s) = 0 then
        return rec(
            valid := true,
            gensS := gensS,
            normalV4s := [],
            bases := [],
            autGens := [],
            autZ := [],
            autBasis := []
        );
    fi;

    bases := List(normalV4s, Z -> PG3S4_OrderedBasesV4(Z));
    autS := AutomorphismGroup(S);
    autGens := GeneratorsOfGroup(autS);
    autZ := [];
    autBasis := [];

    for alpha in autGens do
        rowZ := [];
        rowBasis := [];
        for zi in [1..Length(normalV4s)] do
            Z2 := Image(alpha,normalV4s[zi]);
            z2 := Position(normalV4s,Z2);
            if z2 = fail then
                Error("normal V4 subgroups are not closed under Aut(S)");
            fi;
            Add(rowZ,z2);
            bRow := [];
            for bi in [1..6] do
                basis2 := List(bases[zi][bi], b -> Image(alpha,b));
                b2 := Position(bases[z2],basis2);
                if b2 = fail then
                    Error("ordered V4 bases are not closed under Aut(S)");
                fi;
                Add(bRow,b2);
            od;
            Add(rowBasis,bRow);
        od;
        Add(autZ,rowZ);
        Add(autBasis,rowBasis);
    od;
    return rec(
        valid := true,
        gensS := gensS,
        normalV4s := normalV4s,
        bases := bases,
        autS := autS,
        autGens := autGens,
        autZ := autZ,
        autBasis := autBasis
    );
end;


PG3S4_MapActionTables := function(context,mapData,data,U)
    local maps, codes, elementsU, autMap, normMap, normBasis, alpha,
          row, f, code, pos, normalizer, normGens, g, beta, zi, bi,
          basis2, b2, rowBasis, rowZ;

    maps := mapData.maps;
    codes := mapData.codes;
    elementsU := mapData.elementsU;
    autMap := [];
    for alpha in context.autGens do
        row := [];
        for f in maps do
            code := PG3S4_MapCode(alpha^-1*f,context.gensS,elementsU);
            pos := Position(codes,code);
            if pos = fail then
                Error("oriented maps are not closed under Aut(S)");
            fi;
            Add(row,pos);
        od;
        Add(autMap,row);
    od;

    normalizer := Normalizer(data.outerGroup,U);
    normGens := GeneratorsOfGroup(normalizer);
    normMap := [];
    normBasis := [];
    for g in normGens do
        beta := ConjugatorAutomorphism(U,g);
        row := [];
        for f in maps do
            code := PG3S4_MapCode(f*beta,context.gensS,elementsU);
            pos := Position(codes,code);
            if pos = fail then
                Error("oriented maps are not closed under N_S4(U)");
            fi;
            Add(row,pos);
        od;
        Add(normMap,row);

        rowZ := [];
        for zi in [1..Length(context.normalV4s)] do
            rowBasis := [];
            for bi in [1..6] do
                basis2 := PG3S4_TransportBasisByTarget(
                    context.bases[zi][bi],g,data);
                b2 := Position(context.bases[zi],basis2);
                if b2 = fail then
                    Error("target normalizer does not preserve V4 markings");
                fi;
                Add(rowBasis,b2);
            od;
            Add(rowZ,rowBasis);
        od;
        Add(normBasis,rowZ);
    od;
    return rec(
        autMap := autMap,
        normMap := normMap,
        normBasis := normBasis,
        normalizer := normalizer,
        normGens := normGens
    );
end;


#############################################################################
## 6. Fast orbit count for one image U
#############################################################################

PG3S4_CandidateId := function(m,z,b,numberZ)
    return ((m-1)*numberZ+(z-1))*6+b;
end;


PG3S4_CountImage := function(S,context,imageData,data)
    local start, U, mapData, maps, numberMaps, numberZ, denseSize,
          active, seen, candidateCount, m, z, b, id, actionTables,
          number, queue, head, tmp, m0, z0, b0, k, m2, z2, b2, id2;

    start := Runtime();
    U := imageData.U;
    numberZ := Length(context.normalV4s);
    if not context.valid or numberZ = 0 then
        return rec(
            label := imageData.label,
            imageOrder := Size(U),
            normalV4Subgroups := numberZ,
            quotientMaps := 0,
            orientedMaps := 0,
            compatibleMarkedCandidates := 0,
            classes := 0,
            total := 0,
            runtimeMs := Runtime()-start
        );
    fi;

    mapData := PG3S4_OrientedMaps(S,U,context.gensS);
    maps := mapData.maps;
    numberMaps := Length(maps);
    denseSize := numberMaps*numberZ*6;
    if numberMaps = 0 then
        return rec(
            label := imageData.label,
            imageOrder := Size(U),
            normalV4Subgroups := numberZ,
            quotientMaps := Length(mapData.quotientMaps),
            orientedMaps := 0,
            compatibleMarkedCandidates := 0,
            classes := 0,
            total := 0,
            runtimeMs := Runtime()-start
        );
    fi;

    active := List([1..denseSize], x -> false);
    candidateCount := 0;
    for m in [1..numberMaps] do
        for z in [1..numberZ] do
            for b in [1..6] do
                if PG3S4_IsCompatible(
                    maps[m],context.normalV4s[z],context.bases[z][b],
                    context.gensS,data) then
                    id := PG3S4_CandidateId(m,z,b,numberZ);
                    active[id] := true;
                    candidateCount := candidateCount+1;
                fi;
            od;
        od;
    od;
    if candidateCount = 0 then
        return rec(
            label := imageData.label,
            imageOrder := Size(U),
            normalV4Subgroups := numberZ,
            quotientMaps := Length(mapData.quotientMaps),
            orientedMaps := numberMaps,
            compatibleMarkedCandidates := 0,
            classes := 0,
            total := 0,
            runtimeMs := Runtime()-start
        );
    fi;

    actionTables := PG3S4_MapActionTables(context,mapData,data,U);
    seen := List([1..denseSize], x -> false);
    number := 0;
    for id in [1..denseSize] do
        if active[id] and not seen[id] then
            number := number+1;
            queue := [id];
            seen[id] := true;
            head := 1;
            while head <= Length(queue) do
                id := queue[head];
                head := head+1;
                tmp := QuoInt(id-1,6);
                b0 := (id-1) mod 6 + 1;
                z0 := tmp mod numberZ + 1;
                m0 := QuoInt(tmp,numberZ)+1;

                for k in [1..Length(context.autGens)] do
                    m2 := actionTables.autMap[k][m0];
                    z2 := context.autZ[k][z0];
                    b2 := context.autBasis[k][z0][b0];
                    id2 := PG3S4_CandidateId(m2,z2,b2,numberZ);
                    if not active[id2] then
                        Error("Aut(S) leaves the compatible candidate set");
                    fi;
                    if not seen[id2] then
                        seen[id2] := true;
                        Add(queue,id2);
                    fi;
                od;

                for k in [1..Length(actionTables.normGens)] do
                    m2 := actionTables.normMap[k][m0];
                    b2 := actionTables.normBasis[k][z0][b0];
                    id2 := PG3S4_CandidateId(m2,z0,b2,numberZ);
                    if not active[id2] then
                        Error("N_S4(U) leaves the compatible candidate set");
                    fi;
                    if not seen[id2] then
                        seen[id2] := true;
                        Add(queue,id2);
                    fi;
                od;
            od;
        fi;
    od;
    return rec(
        label := imageData.label,
        imageOrder := Size(U),
        normalV4Subgroups := numberZ,
        quotientMaps := Length(mapData.quotientMaps),
        orientedMaps := numberMaps,
        compatibleMarkedCandidates := candidateCount,
        classes := number,
        total := number,
        runtimeMs := Runtime()-start
    );
end;


#############################################################################
## 7. Closed shortcut for S elementary abelian
#############################################################################

PG3S4_ElementaryAbelianShortcut := function(S,classes)
    local d, byImage, c, value, total;

    d := PG3S4_RankElementaryAbelian2Group(S);
    byImage := [];
    total := 0;
    for c in classes do
        value := 0;
        if c.label = "trivial" and d >= 2 then
            value := 1;
        elif c.label = "C2_double_transposition" and d >= 3 then
            value := 1;
        elif c.label = "V4_normal" and d >= 4 then
            value := 1;
        fi;
        Add(byImage,rec(
            label := c.label,
            imageOrder := Size(c.U),
            normalV4Subgroups := fail,
            quotientMaps := fail,
            orientedMaps := fail,
            compatibleMarkedCandidates := fail,
            classes := value,
            total := value,
            runtimeMs := 0,
            elementaryAbelianClosedFormula := true
        ));
        total := total+value;
    od;
    return rec(
        byImageClass := byImage,
        summary := List(Filtered(byImage,x -> x.classes <> 0),
                        x -> [x.label,x.classes]),
        totalClasses := total,
        total := total,
        elementaryAbelianShortcut := true,
        elementaryAbelianRank := d
    );
end;


#############################################################################
## 8. Public counts for one S, one SmallGroup, or all S of order 4*n
#############################################################################

PG3S4_ForSWithData := function(S,data)
    local start, n, classes, context, byImage, c, ans, total;

    start := Runtime();
    if Size(S) mod 4 <> 0 then
        Error("the order of S must be divisible by 4");
    fi;
    n := Size(S)/4;
    classes := Filtered(PG3S4_ImageClasses(data), c ->
        n mod Size(c.U) = 0);

    if PG3S4_IsElementaryAbelian2Group(S) then
        ans := PG3S4_ElementaryAbelianShortcut(S,classes);
        ans.runtimeMs := Runtime()-start;
        return ans;
    fi;

    context := PG3S4_PrepareSContext(S);
    byImage := [];
    total := 0;
    for c in classes do
        ans := PG3S4_CountImage(S,context,c,data);
        Add(byImage,ans);
        total := total+ans.classes;
    od;
    return rec(
        byImageClass := byImage,
        summary := List(Filtered(byImage,x -> x.classes <> 0),
                        x -> [x.label,x.classes]),
        totalClasses := total,
        total := total,
        normalV4Subgroups := Length(context.normalV4s),
        elementaryAbelianShortcut := false,
        runtimeMs := Runtime()-start
    );
end;


ZPhiClasses_PG3840_3_ForS := function(S)
    return PG3S4_ForSWithData(S,PG3S4_ActionData());
end;


ZPhiClasses_PG3840_3_SmallGroup := function(n,i)
    local S, ans;

    S := SmallGroup(4*n,i);
    ans := ZPhiClasses_PG3840_3_ForS(S);
    return rec(
        n := n,
        orderS := 4*n,
        extensionOrder := 3840*n,
        smallGroup := [4*n,i],
        byImageClass := ans.byImageClass,
        summary := ans.summary,
        totalClasses := ans.totalClasses,
        total := ans.totalClasses,
        elementaryAbelianShortcut := ans.elementaryAbelianShortcut,
        runtimeMs := ans.runtimeMs
    );
end;


ZPhiClasses_PG3840_3_AllS_FromTo := function(n,first,last)
    local start, number, data, classes, totals, totalCandidates,
          totalMaps, perGroup, total, elementaryCount, gcMs, i, S, ans,
          j, tgc, result;

    start := Runtime();
    number := NumberSmallGroups(4*n);
    if first < 1 or last < first or last > number then
        Error("invalid SmallGroups range");
    fi;
    data := PG3S4_ActionData();
    classes := Filtered(PG3S4_ImageClasses(data), c ->
        n mod Size(c.U) = 0);
    totals := List(classes, c -> 0);
    totalCandidates := List(classes, c -> 0);
    totalMaps := List(classes, c -> 0);
    perGroup := [];
    total := 0;
    elementaryCount := 0;
    gcMs := 0;

    Print("ZPhiClasses_PG3840_3_AllS(n=",n,")\n");
    Print("P=PerfectGroup(3840,3), Z(P)=V4, Out(P)=S4\n");
    Print("S4 acts naturally on V4; image S3 and kernel V4\n");
    Print("SmallGroups of order ",4*n," to test = ",last-first+1,
          "/",number,"\n");
    Print("admissible image classes = ",
          List(classes,c -> [c.label,Size(c.U)]),"\n");

    for i in [first..last] do
        S := SmallGroup(4*n,i);
        ans := PG3S4_ForSWithData(S,data);
        if ans.elementaryAbelianShortcut then
            elementaryCount := elementaryCount+1;
            Print("elementary abelian shortcut for SmallGroup(",4*n,
                  ",",i,")\n");
        fi;
        if ans.totalClasses <> 0 then
            Add(perGroup,rec(
                smallGroup := [4*n,i],
                classes := ans.totalClasses,
                byImageClass := List(ans.byImageClass,
                    x -> [x.label,x.classes])
            ));
            total := total+ans.totalClasses;
        fi;
        for j in [1..Length(classes)] do
            totals[j] := totals[j]+ans.byImageClass[j].classes;
            if ans.byImageClass[j].compatibleMarkedCandidates <> fail then
                totalCandidates[j] := totalCandidates[j]
                    + ans.byImageClass[j].compatibleMarkedCandidates;
            fi;
            if ans.byImageClass[j].orientedMaps <> fail then
                totalMaps[j] := totalMaps[j]
                    + ans.byImageClass[j].orientedMaps;
            fi;
        od;

        # Release all group-specific objects, including Aut(S), immediately.
        S := fail;
        ans := fail;
        if (i-first+1) mod 100 = 0 then
            tgc := Runtime();
            GASMAN("collect");
            gcMs := gcMs+Runtime()-tgc;
            Print("processed ",i-first+1,"/",last-first+1,
                  "; classes=",total,"\n");
        fi;
    od;

    result := rec(
        n := n,
        orderS := 4*n,
        extensionOrder := 3840*n,
        range := [first,last],
        smallGroupsTested := last-first+1,
        contributingSmallGroups := Length(perGroup),
        elementaryAbelianShortcuts := elementaryCount,
        byImageClass := List([1..Length(classes)], j -> rec(
            label := classes[j].label,
            imageOrder := Size(classes[j].U),
            classes := totals[j],
            orientedMaps := totalMaps[j],
            compatibleMarkedCandidates := totalCandidates[j]
        )),
        perGroup := perGroup,
        totalClasses := total,
        total := total,
        forcedGarbageCollectionMs := gcMs,
        runtimeMs := Runtime()-start
    );

    Print("\nSummary\n");
    Print("n = ",n,"; |S| = ",4*n,"; |E| = ",3840*n,"\n");
    Print("SmallGroups tested = ",last-first+1,"\n");
    Print("contributing SmallGroups = ",Length(perGroup),"\n");
    Print("elementary abelian shortcuts = ",elementaryCount,"\n");
    for j in [1..Length(result.byImageClass)] do
        Print("  ",result.byImageClass[j].label," : ",
              result.byImageClass[j].classes,
              "  (compatible marked candidates = ",
              result.byImageClass[j].compatibleMarkedCandidates,")\n");
    od;
    Print("total Z-phi classes = ",total,"\n");
    Print("forced garbage collection time (ms) = ",gcMs,"\n");
    return result;
end;


ZPhiClasses_PG3840_3_AllS := function(n)
    return ZPhiClasses_PG3840_3_AllS_FromTo(
        n,1,NumberSmallGroups(4*n));
end;
