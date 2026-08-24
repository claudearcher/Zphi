#############################################################################
##
##  source : zphi a method by Claude Archer, described in his PhD thesis
##  "Classification of Group Extensions", Université Libre de Bruxelles (2002)
##
##  ZPhiClasses_PG3840_4_V4_OutD8_ImageC2_GAP415v5.g
##
##  Full Z-phi-class counter for
##
##      P = PerfectGroup(3840,4),
##      Z(P)   = V4,
##      Out(P) = D8 = < r,s | r^4=s^2=1, srs=r^-1 >,
##
##  where Out(P) acts on Z(P) with image C2 and kernel
##
##      H = < r^2, s > = V4.
##
##  GAP compatibility target: GAP 4.15.
##
##  Difference with v2
##  ------------------
##  Version v2 counted only the branches for which the marked V4 in S is
##  central, equivalently Image(phi) <= H = Ker(D8 -> Aut(V4)).
##
##  This v5 also counts the branches with non-trivial action on the marked
##  V4.  Hence the algorithm now searches for all normal subgroups
##
##      Z triangleleft S,   Z isomorphic to V4,
##
##  not only for V4 subgroups contained in Centre(S).  For every image
##  U <= D8, every oriented epimorphism f:S -> U, and every ordered marking
##  lambda:Z(P)->Z, it keeps exactly the compatible triples satisfying
##
##      lambda(a)^s = lambda(a^f(s))
##
##  for a in a fixed ordered basis of Z(P) and generators s of S.
##
##  Equivalence is generated simultaneously by Aut(S) and N_D8(U).  A target
##  normalizer element conjugates f and transports the marking at the same
##  time.  This is the same orbit mechanism as in the validated script for
##  PerfectGroup(3840,3), but with the outer group restricted from S4 to D8.
##
##  Public functions
##  ----------------
##
##      res := ZPhiClasses_V4_D8_ImageC2_AllS(n);;
##      res := ZPhiClasses_V4_D8_ImageC2_AllS_FromTo(n,first,last);;
##      res := ZPhiClasses_V4_D8_ImageC2_SmallGroup(n,i);;
##
#############################################################################


#############################################################################
## 1. Elementary helpers
#############################################################################

V4D8C2V5_IsV4 := function(V)
    local elements;

    if Size(V) <> 4 or not IsAbelian(V) then
        return false;
    fi;
    elements := Elements(V);
    return ForAll(elements, x -> x = One(V) or Order(x) = 2);
end;


V4D8C2V5_OrderedBasesV4 := function(V)
    local nonidentity, bases, x, y;

    if not V4D8C2V5_IsV4(V) then
        Error("V4D8C2V5_OrderedBasesV4 expects a Klein four group");
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


V4D8C2V5_IsElementaryAbelian2Group := function(S)
    local one;

    if not IsAbelian(S) then
        return false;
    fi;
    one := One(S);
    return ForAll(GeneratorsOfGroup(S), x -> x = one or Order(x) = 2);
end;


V4D8C2V5_RankElementaryAbelian2Group := function(S)
    local q, d;

    if not V4D8C2V5_IsElementaryAbelian2Group(S) then
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
## 2. Canonical D8 data and its subgroup classes
#############################################################################

V4D8C2V5_ActionData := function()
    local r, s, D, A, actionMap, image, kernel, data;

    ## D8 is realized inside S4.  The normal Klein subgroup A is the kernel
    ## of the action on the three non-trivial elements of A.
    r := (1,2,3,4);
    s := (1,2)(3,4);
    D := Group(r,s);
    A := Group(r^2,s);

    actionMap := ActionHomomorphism(D, Elements(A), OnPoints);
    image := Image(actionMap);
    kernel := Kernel(actionMap);

    if Size(D) <> 8 or not V4D8C2V5_IsV4(A) or not IsNormal(D,A) then
        Error("the canonical D8 data are inconsistent");
    fi;
    if Size(image) <> 2 or kernel <> A then
        Error("unexpected action of D8 on its normal Klein subgroup");
    fi;

    data := rec(
        outerGroup := D,
        r := r,
        s := s,
        centre := A,
        centreBasis := [r^2,s],
        centreAction := actionMap,
        centreActionImage := image,
        centreActionKernel := kernel
    );
    return data;
end;


V4D8C2V5_SubgroupClassLabel := function(data,U,idx)
    local D, K, ZD, actionImage, actionOrder, order, struct, label;

    D := data.outerGroup;
    K := data.centreActionKernel;
    ZD := Centre(D);
    actionImage := Image(data.centreAction,U);
    actionOrder := Size(actionImage);
    order := Size(U);
    struct := StructureDescription(U);

    if order = 1 then
        label := "trivial";
    elif actionOrder = 1 then
        if order = 2 and IsSubgroup(ZD,U) then
            label := "trivial_action_central_C2";
        elif order = 2 then
            label := "trivial_action_kernel_reflection_C2";
        elif order = 4 and U = K then
            label := "trivial_action_kernel_V4";
        else
            label := Concatenation("trivial_action_order_",String(order),"_class_",String(idx));
        fi;
    else
        if order = 2 then
            label := "nontrivial_action_C2";
        elif order = 4 and IsCyclic(U) then
            label := "nontrivial_action_C4";
        elif order = 4 then
            label := "nontrivial_action_V4";
        elif order = Size(D) then
            label := "full_D8_nontrivial_action";
        else
            label := Concatenation("nontrivial_action_order_",String(order),"_class_",String(idx));
        fi;
    fi;

    return label;
end;


V4D8C2V5_ImageClasses := function(data)
    local D, subgroupClasses, classes, i, U, actionImage, actionOrder,
          centreAction, label;

    D := data.outerGroup;
    subgroupClasses := ConjugacyClassesSubgroups(D);
    classes := [];

    for i in [1..Length(subgroupClasses)] do
        U := Representative(subgroupClasses[i]);
        actionImage := Image(data.centreAction,U);
        actionOrder := Size(actionImage);
        if actionOrder = 1 then
            centreAction := "trivial";
        else
            centreAction := Concatenation("nontrivial_order_",String(actionOrder));
        fi;
        label := V4D8C2V5_SubgroupClassLabel(data,U,i);
        Add(classes,rec(
            label := label,
            classIndex := i,
            U := U,
            imageOrder := Size(U),
            centreAction := centreAction,
            centreActionImageOrder := actionOrder,
            subgroupStructure := StructureDescription(U),
            normalizerOrder := Size(Normalizer(D,U))
        ));
    od;

    SortBy(classes, c -> [Size(c.U), c.centreActionImageOrder,
        c.subgroupStructure, c.label]);
    return classes;
end;


V4D8C2V5_PrintImageClasses := function(data)
    local c;

    Print("Label\tOrder\tStructure\tActionOnCentre\tNormalizerOrder\n");
    for c in V4D8C2V5_ImageClasses(data) do
        Print(c.label,"\t",Size(c.U),"\t",c.subgroupStructure,"\t",
              c.centreAction,"\t",c.normalizerOrder,"\n");
    od;
end;

#############################################################################
## 3. Surjections S -> U and normal V4 subgroups of S
#############################################################################

V4D8C2V5_GQuotientsIncludingTrivial := function(S,U)
    local gensS, oneU, images;

    if Size(U) > 1 then
        return GQuotients(S,U);
    fi;
    gensS := GeneratorsOfGroup(S);
    oneU := One(U);
    images := List(gensS, x -> oneU);
    return [GroupHomomorphismByImages(S,U,gensS,images)];
end;


V4D8C2V5_MapCode := function(f,gensS,elementsU)
    return List(gensS, x -> Position(elementsU,Image(f,x)));
end;


V4D8C2V5_OrientedMaps := function(S,U,gensS)
    local quotientMaps, autU, autElements, elementsU, maps, codes,
          f0, beta, f, code;

    quotientMaps := V4D8C2V5_GQuotientsIncludingTrivial(S,U);
    autU := AutomorphismGroup(U);
    autElements := Elements(autU);
    elementsU := Elements(U);
    maps := [];
    codes := [];

    for f0 in quotientMaps do
        for beta in autElements do
            f := f0*beta;
            code := V4D8C2V5_MapCode(f,gensS,elementsU);
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


V4D8C2V5_NormalV4Subgroups := function(S)
    local normals;

    normals := NormalSubgroups(S);
    return Filtered(normals, Z -> V4D8C2V5_IsV4(Z));
end;


#############################################################################
## 4. Markings Z(P) -> Z and compatibility with conjugation
#############################################################################

V4D8C2V5_CanonicalToMarked := function(a,basis,data)
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


V4D8C2V5_TransportBasisByTarget := function(basis,g,data)
    local ginv;

    ## ConjugatorAutomorphism(U,g) sends u to u^g.  Therefore the compatible
    ## marking after f -> f^g is lambda'(a)=lambda(a^(g^-1)).
    ginv := g^-1;
    return List(data.centreBasis, a ->
        V4D8C2V5_CanonicalToMarked(a^ginv,basis,data));
end;


V4D8C2V5_IsCompatible := function(f,Z,basis,gensS,data)
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
            rhs := V4D8C2V5_CanonicalToMarked(aimage,basis,data);
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

V4D8C2V5_PrepareSContext := function(S)
    local gensS, normalV4s, bases, autS, autGens, autZ, autBasis,
          alpha, rowZ, rowBasis, zi, bi, Z2, z2, basis2, b2, bRow;

    if Size(S) mod 4 <> 0 then
        return rec(valid := false, normalV4s := []);
    fi;
    gensS := GeneratorsOfGroup(S);
    normalV4s := V4D8C2V5_NormalV4Subgroups(S);
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

    bases := List(normalV4s, Z -> V4D8C2V5_OrderedBasesV4(Z));
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


V4D8C2V5_MapActionTables := function(context,mapData,data,U)
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
            code := V4D8C2V5_MapCode(alpha^-1*f,context.gensS,elementsU);
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
            code := V4D8C2V5_MapCode(f*beta,context.gensS,elementsU);
            pos := Position(codes,code);
            if pos = fail then
                Error("oriented maps are not closed under N_D8(U)");
            fi;
            Add(row,pos);
        od;
        Add(normMap,row);

        rowZ := [];
        for zi in [1..Length(context.normalV4s)] do
            rowBasis := [];
            for bi in [1..6] do
                basis2 := V4D8C2V5_TransportBasisByTarget(
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

V4D8C2V5_CandidateId := function(m,z,b,numberZ)
    return ((m-1)*numberZ+(z-1))*6+b;
end;


V4D8C2V5_CountImage := function(S,context,imageData,data)
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
            centreAction := imageData.centreAction,
            normalV4Subgroups := numberZ,
            quotientMaps := 0,
            orientedMaps := 0,
            compatibleMarkedCandidates := 0,
            classes := 0,
            total := 0,
            runtimeMs := Runtime()-start
        );
    fi;

    mapData := V4D8C2V5_OrientedMaps(S,U,context.gensS);
    maps := mapData.maps;
    numberMaps := Length(maps);
    denseSize := numberMaps*numberZ*6;
    if numberMaps = 0 then
        return rec(
            label := imageData.label,
            imageOrder := Size(U),
            centreAction := imageData.centreAction,
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
                if V4D8C2V5_IsCompatible(
                    maps[m],context.normalV4s[z],context.bases[z][b],
                    context.gensS,data) then
                    id := V4D8C2V5_CandidateId(m,z,b,numberZ);
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
            centreAction := imageData.centreAction,
            normalV4Subgroups := numberZ,
            quotientMaps := Length(mapData.quotientMaps),
            orientedMaps := numberMaps,
            compatibleMarkedCandidates := 0,
            classes := 0,
            total := 0,
            runtimeMs := Runtime()-start
        );
    fi;

    actionTables := V4D8C2V5_MapActionTables(context,mapData,data,U);
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
                    id2 := V4D8C2V5_CandidateId(m2,z2,b2,numberZ);
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
                    id2 := V4D8C2V5_CandidateId(m2,z0,b2,numberZ);
                    if not active[id2] then
                        Error("N_D8(U) leaves the compatible candidate set");
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
        centreAction := imageData.centreAction,
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

V4D8C2V5_ElementaryAbelianShortcut := function(S,classes)
    local d, byImage, c, value, total, rankU;

    d := V4D8C2V5_RankElementaryAbelian2Group(S);
    byImage := [];
    total := 0;
    for c in classes do
        value := 0;
        ## If S is abelian, every marked V4 is central.  Hence a compatible
        ## branch must have trivial action on the canonical centre.  For an
        ## elementary abelian image U of rank e, the epimorphism S -> U and a
        ## marked V4 in its kernel give one class precisely when d >= e+2.
        if c.centreActionImageOrder = 1
           and V4D8C2V5_IsElementaryAbelian2Group(c.U) then
            rankU := V4D8C2V5_RankElementaryAbelian2Group(c.U);
            if d >= rankU + 2 then
                value := 1;
            fi;
        fi;
        Add(byImage,rec(
            label := c.label,
            imageOrder := Size(c.U),
            centreAction := c.centreAction,
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

V4D8C2V5_ForSWithData := function(S,data)
    local start, n, classes, context, byImage, c, ans, total;

    start := Runtime();
    if Size(S) mod 4 <> 0 then
        Error("the order of S must be divisible by 4");
    fi;
    n := Size(S)/4;
    classes := Filtered(V4D8C2V5_ImageClasses(data), c ->
        n mod Size(c.U) = 0);

    if V4D8C2V5_IsElementaryAbelian2Group(S) then
        ans := V4D8C2V5_ElementaryAbelianShortcut(S,classes);
        ans.runtimeMs := Runtime()-start;
        return ans;
    fi;

    context := V4D8C2V5_PrepareSContext(S);
    byImage := [];
    total := 0;
    for c in classes do
        ans := V4D8C2V5_CountImage(S,context,c,data);
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


ZPhiClasses_V4_D8_ImageC2_ForS := function(S)
    return V4D8C2V5_ForSWithData(S,V4D8C2V5_ActionData());
end;


ZPhiClasses_V4_D8_ImageC2_SmallGroup := function(n,i)
    local S, ans;

    S := SmallGroup(4*n,i);
    ans := ZPhiClasses_V4_D8_ImageC2_ForS(S);
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


ZPhiClasses_V4_D8_ImageC2_AllS_FromTo := function(n,first,last)
    local start, number, data, classes, totals, totalCandidates,
          totalMaps, perGroup, total, elementaryCount, gcMs, i, S, ans,
          j, tgc, result;

    start := Runtime();
    number := NumberSmallGroups(4*n);
    if not IsInt(n) or n < 1 then
        Error("n must be a positive integer");
    fi;
    if first < 1 or last < first or last > number then
        Error("invalid SmallGroups range");
    fi;
    data := V4D8C2V5_ActionData();
    classes := Filtered(V4D8C2V5_ImageClasses(data), c ->
        n mod Size(c.U) = 0);
    totals := List(classes, c -> 0);
    totalCandidates := List(classes, c -> 0);
    totalMaps := List(classes, c -> 0);
    perGroup := [];
    total := 0;
    elementaryCount := 0;
    gcMs := 0;

    Print("ZPhiClasses_V4_D8_ImageC2_AllS_v5(n=",n,")\n");
    Print("P=PerfectGroup(3840,4), Z(P)=V4, Out(P)=D8\n");
    Print("D8 acts on V4 with image C2 and kernel H=<r^2,s>\n");
    Print("This v5 searches all normal V4 subgroups, not only central V4s.\n");
    Print("SmallGroups of order ",4*n," to test = ",last-first+1,
          "/",number,"\n");
    Print("admissible image classes = ",
          List(classes,c -> [c.label,Size(c.U),c.centreAction]),"\n");

    for i in [first..last] do
        S := SmallGroup(4*n,i);
        ans := V4D8C2V5_ForSWithData(S,data);
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
        applicablePerfectGroup := [3840,4],
        centreStructure := "C2 x C2",
        outStructure := "D8",
        actionOnCentre :=
            "nontrivial, image C2, kernel H=<r^2,s>=V4",
        algorithmVersion := "v5: all normal V4 subgroups, including noncentral compatible branches",
        range := [first,last],
        smallGroupsTested := last-first+1,
        contributingSmallGroups := Length(perGroup),
        elementaryAbelianShortcuts := elementaryCount,
        byImageClass := List([1..Length(classes)], j -> rec(
            label := classes[j].label,
            imageOrder := Size(classes[j].U),
            centreAction := classes[j].centreAction,
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
              "  (action=",result.byImageClass[j].centreAction,
              ", compatible marked candidates = ",
              result.byImageClass[j].compatibleMarkedCandidates,")\n");
    od;
    Print("total Z-phi classes = ",total,"\n");
    Print("forced garbage collection time (ms) = ",gcMs,"\n");
    return result;
end;


ZPhiClasses_V4_D8_ImageC2_AllS := function(n)
    return ZPhiClasses_V4_D8_ImageC2_AllS_FromTo(
        n,1,NumberSmallGroups(4*n));
end;
