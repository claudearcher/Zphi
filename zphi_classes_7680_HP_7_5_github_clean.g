#############################################################################
## Z-phi classes for PerfectGroup(7680,5)
## Clean GitHub release file: 
#############################################################################

HP75OutGroupDataCached := fail;
HP75V5_GL3Cache := fail;
HP75V5DeepAudit := false;

IdGroupSafe := function(G)
    if Size(G) = 1 then
        return [1,1];
    fi;
    return IdGroup(G);
end;

HP75JoinListOfStrings := function(list, sep)
    local s, i;
    if Length(list) = 0 then
        return "";
    fi;
    s := list[1];
    for i in [2..Length(list)] do
        s := Concatenation(s, sep, list[i]);
    od;
    return s;
end;

IsC2CubeGroup := function(G)
    return Size(G) = 8 and IdGroup(G) = [8,5];
end;

Vec2Add := function(u, v)
    return [(u[1]+v[1]) mod 2, (u[2]+v[2]) mod 2];
end;

Vec3Add := function(u, v)
    return [(u[1]+v[1]) mod 2, (u[2]+v[2]) mod 2, (u[3]+v[3]) mod 2];
end;

ApplyMat2ToVec := function(A, v)
    return [ (v[1]*A[1][1] + v[2]*A[2][1]) mod 2,
             (v[1]*A[1][2] + v[2]*A[2][2]) mod 2 ];
end;

ApplyMat3ToVec := function(A, v)
    return [ (v[1]*A[1][1] + v[2]*A[2][1] + v[3]*A[3][1]) mod 2,
             (v[1]*A[1][2] + v[2]*A[2][2] + v[3]*A[3][2]) mod 2,
             (v[1]*A[1][3] + v[2]*A[2][3] + v[3]*A[3][3]) mod 2 ];
end;

Mat2Equal := function(A, B)
    return A[1] = B[1] and A[2] = B[2];
end;

Mat3Equal := function(A, B)
    return A[1] = B[1] and A[2] = B[2] and A[3] = B[3];
end;

Mat2Position := function(list, A)
    local i;
    for i in [1..Length(list)] do
        if Mat2Equal(list[i], A) then
            return i;
        fi;
    od;
    return fail;
end;

Mat3Position := function(list, A)
    local i;
    for i in [1..Length(list)] do
        if Mat3Equal(list[i], A) then
            return i;
        fi;
    od;
    return fail;
end;

ComposeMat2 := function(A, B)
    return [ApplyMat2ToVec(A, B[1]), ApplyMat2ToVec(A, B[2])];
end;

ComposeMat3 := function(A, B)
    return [ApplyMat3ToVec(A, B[1]), ApplyMat3ToVec(A, B[2]), ApplyMat3ToVec(A, B[3])];
end;

GL2F2Matrices := function()
    local mats, a, b, c, d, det;
    mats := [];
    for a in [0,1] do
        for b in [0,1] do
            for c in [0,1] do
                for d in [0,1] do
                    det := (a*d + b*c) mod 2;
                    if det = 1 then
                        Add(mats, [[a,b],[c,d]]);
                    fi;
                od;
            od;
        od;
    od;
    return mats;
end;

InverseMat2HP75 := function(A)
    local B, I;
    I := [[1,0],[0,1]];
    for B in GL2F2Matrices() do
        if Mat2Equal(ComposeMat2(A,B),I) and
           Mat2Equal(ComposeMat2(B,A),I) then
            return B;
        fi;
    od;
    Error("Matrice GL(2,2) non inversible (inattendu).");
end;

Block3FromGL2 := function(A)
    return [[A[1][1], A[1][2], 0], [A[2][1], A[2][2], 0], [0,0,1]];
end;

HP75ImageS3Matrices3 := function()
    return List(GL2F2Matrices(), A -> Block3FromGL2(A));
end;

HP75A2FromMatrix3 := function(M)
    if M[3] <> [0,0,1] then
        return fail;
    fi;
    if M[1][3] <> 0 or M[2][3] <> 0 then
        return fail;
    fi;
    return [[M[1][1], M[1][2]], [M[2][1], M[2][2]]];
end;

IsMatrixInHP75ImageS3 := function(M)
    return Mat3Position(HP75ImageS3Matrices3(), M) <> fail;
end;

MatrixClosure3 := function(gens)
    local closure, mat, changed, a, b, comp, pos;
    closure := [[[1,0,0],[0,1,0],[0,0,1]]];
    for mat in gens do
        if Mat3Position(closure, mat) = fail then
            Add(closure, mat);
        fi;
    od;
    changed := true;
    while changed do
        changed := false;
        for a in ShallowCopy(closure) do
            for b in ShallowCopy(closure) do
                comp := ComposeMat3(a, b);
                pos := Mat3Position(closure, comp);
                if pos = fail then
                    Add(closure, comp);
                    changed := true;
                fi;
            od;
        od;
    od;
    return closure;
end;

CoordinatesC2CubeByBasis := function(basis, x)
    local a, b, c, y;
    for a in [0..1] do
        for b in [0..1] do
            for c in [0..1] do
                y := basis[1]^a * basis[2]^b * basis[3]^c;
                if y = x then
                    return [a,b,c];
                fi;
            od;
        od;
    od;
    Error("Coordonnees C2^3 introuvables.");
end;

C2CubeElementFromCoordinates := function(basis, coord)
    return basis[1]^coord[1] * basis[2]^coord[2] * basis[3]^coord[3];
end;

ApplyMatrixToMarkingC2Cube := function(marking, M)
    return [C2CubeElementFromCoordinates(marking, M[1]), C2CubeElementFromCoordinates(marking, M[2]), C2CubeElementFromCoordinates(marking, M[3])];
end;

ActionMatrixOfElementOnMarkedC2Cube := function(marking, s)
    local im1, im2, im3;
    im1 := CoordinatesC2CubeByBasis(marking, marking[1]^s);
    im2 := CoordinatesC2CubeByBasis(marking, marking[2]^s);
    im3 := CoordinatesC2CubeByBasis(marking, marking[3]^s);
    return [im1, im2, im3];
end;

ActionMatricesOfSOnMarkedC2Cube := function(S, marking)
    return List(GeneratorsOfGroup(S), s -> ActionMatrixOfElementOnMarkedC2Cube(marking, s));
end;

ActionImageIdHP75 := function(S, marking)
    local closure, imgSize;
    closure := MatrixClosure3(ActionMatricesOfSOnMarkedC2Cube(S, marking));
    imgSize := Length(closure);
    if imgSize = 1 then
        return [1,1];
    elif imgSize = 2 then
        return [2,1];
    elif imgSize = 3 then
        return [3,1];
    elif imgSize = 6 then
        return [6,1];
    fi;
    Error("Image d'action inattendue pour HP (7,5) : taille ", imgSize);
end;

HP75IntListString := function(list)
    return HP75JoinListOfStrings(List(list, x -> String(x)), "_");
end;

MarkingKeyByElementsHP75 := function(S, marking)
    local elems;
    elems := Elements(S);
    return [Position(elems, marking[1]), Position(elems, marking[2]), Position(elems, marking[3])];
end;

HP75MarkingKeyStringFromElements := function(S, marking)
    return HP75IntListString(MarkingKeyByElementsHP75(S, marking));
end;

ImageOfMarkingByAutSHP75 := function(marking, aut)
    return [Image(aut, marking[1]), Image(aut, marking[2]), Image(aut, marking[3])];
end;

HP75KernelVectors := function()
    return [[0,0], [1,0], [0,1], [1,1]];
end;

HP75AffineImageOfVector := function(v, A, x)
    return Vec2Add(v, ApplyMat2ToVec(A, x));
end;

HP75PermFromVectorAndA2 := function(v, A)
    local points, images, x, y;
    points := HP75KernelVectors();
    images := [];
    for x in points do
        y := HP75AffineImageOfVector(v, A, x);
        Add(images, Position(points, y));
    od;
    return PermList(images);
end;

HP75OutGroupData := function()
    local points, mats, elems, v, A, perm, outG;
    if HP75OutGroupDataCached <> fail then
        return HP75OutGroupDataCached;
    fi;
    points := HP75KernelVectors();
    mats := GL2F2Matrices();
    elems := [];
    for v in points do
        for A in mats do
            perm := HP75PermFromVectorAndA2(v, A);
            Add(elems, rec(v := v, A := A, perm := perm, enc := [v[1], v[2], Mat2Position(mats, A)]));
        od;
    od;
    outG := Group(List(elems, e -> e.perm));
    HP75OutGroupDataCached := rec(points := points, mats := mats, elems := elems, group := outG, identityA := [[1,0],[0,1]]);
    return HP75OutGroupDataCached;
end;

HP75A2FromPerm := function(p)
    local data, e;
    data := HP75OutGroupData();
    for e in data.elems do
        if e.perm = p then
            return e.A;
        fi;
    od;
    Error("Permutation hors du modele HP75 Out=S4.");
end;

HP75PhiImageIdFromPerms := function(perms)
    local G;
    G := Group(perms);
    return IdGroupSafe(G);
end;

HP75LambdaA2OfQElement := function(nat, marking, q)
    local s, mat3, A;
    s := PreImagesRepresentative(nat, q);
    mat3 := ActionMatrixOfElementOnMarkedC2Cube(marking, s);
    A := HP75A2FromMatrix3(mat3);
    if A = fail then
        Error("Action non admissible dans l'image S3 de HP (7,5).");
    fi;
    return A;
end;

HP75HomMatchesLambda := function(hom, elemsQ, lambdaAList)
    local i, p, A;
    for i in [1..Length(elemsQ)] do
        p := Image(hom, elemsQ[i]);
        A := HP75A2FromPerm(p);
        if not Mat2Equal(A, lambdaAList[i]) then
            return false;
        fi;
    od;
    return true;
end;

AllTuplesFromListHP75 := function(list, len)
    local res, smaller, x, t;
    if len = 0 then
        return [[]];
    fi;
    smaller := AllTuplesFromListHP75(list, len-1);
    res := [];
    for x in list do
        for t in smaller do
            Add(res, Concatenation([x], t));
        od;
    od;
    return res;
end;

NormalC2CubeSubgroups := function(S)
    local norms;
    norms := NormalSubgroups(S);
    return Filtered(norms, N -> IsC2CubeGroup(N));
end;

HP75ImageSubgroupByAut := function(N, a)
    return Image(a, N);
end;

NormalC2CubeSubgroupOrbitRepsHP75 := function(S, autS)
    local goodZ, orbs;
    goodZ := NormalC2CubeSubgroups(S);
    if Length(goodZ) = 0 then
        return [];
    fi;
    orbs := Orbits(autS, goodZ, HP75ImageSubgroupByAut);
    return List(orbs, o -> o[1]);
end;

StabilizerOfZ0InAutSHP75 := function(autS, Z0)
    return Stabilizer(autS, Z0, HP75ImageSubgroupByAut);
end;

ZPhiOrbitRecordHP75 := function(S, datum)
    return rec(SId := IdGroup(S), RId := datum.RId, actionImageId := datum.actionImageId, phiImageId := datum.phiImageId, Z0Generators := GeneratorsOfGroup(datum.Z0), marking := datum.marking, phiList := datum.phiList);
end;

AddOrIncreasePairCount := function(list, pair, inc)
    local row;
    for row in list do
        if row[1] = pair then
            row[2] := row[2] + inc;
            return;
        fi;
    od;
    Add(list, [pair, inc]);
end;

AddOrIncreaseTripleCount := function(list, pair1, pair2, inc)
    local row;
    for row in list do
        if row[1] = pair1 and row[2] = pair2 then
            row[3] := row[3] + inc;
            return;
        fi;
    od;
    Add(list, [pair1, pair2, inc]);
end;

AddOrIncreaseQuadrupleCount := function(list, pair1, pair2, pair3, inc)
    local row;
    for row in list do
        if row[1] = pair1 and row[2] = pair2 and row[3] = pair3 then
            row[4] := row[4] + inc;
            return;
        fi;
    od;
    Add(list, [pair1, pair2, pair3, inc]);
end;

SortPairCountList := function(list)
    Sort(list, function(a,b)
        if a[1][1] <> b[1][1] then return a[1][1] < b[1][1]; fi;
        return a[1][2] < b[1][2];
    end);
end;

SortTripleCountList := function(list)
    Sort(list, function(a,b)
        if a[1][1] <> b[1][1] then return a[1][1] < b[1][1]; fi;
        if a[1][2] <> b[1][2] then return a[1][2] < b[1][2]; fi;
        if a[2][1] <> b[2][1] then return a[2][1] < b[2][1]; fi;
        return a[2][2] < b[2][2];
    end);
end;

SortQuadrupleCountList := function(list)
    Sort(list, function(a,b)
        if a[1][1] <> b[1][1] then return a[1][1] < b[1][1]; fi;
        if a[1][2] <> b[1][2] then return a[1][2] < b[1][2]; fi;
        if a[2][1] <> b[2][1] then return a[2][1] < b[2][1]; fi;
        if a[2][2] <> b[2][2] then return a[2][2] < b[2][2]; fi;
        if a[3][1] <> b[3][1] then return a[3][1] < b[3][1]; fi;
        return a[3][2] < b[3][2];
    end);
end;

HP75AllGL3MatricesV5 := function()
    local nz, mats, a, b, c, ab;
    if HP75V5_GL3Cache <> fail then
        return HP75V5_GL3Cache;
    fi;

    nz := [
        [1,0,0], [0,1,0], [0,0,1],
        [1,1,0], [1,0,1], [0,1,1], [1,1,1]
    ];

    mats := [];
    for a in nz do
        for b in nz do
            if b <> a then
                ab := Vec3Add(a,b);
                for c in nz do
                    if c <> a and c <> b and c <> ab then
                        Add(mats, [ShallowCopy(a), ShallowCopy(b), ShallowCopy(c)]);
                    fi;
                od;
            fi;
        od;
    od;

    if Length(mats) <> 168 then
        Error("GL(3,2) v5: 168 matrices attendues, obtenu ", Length(mats));
    fi;

    HP75V5_GL3Cache := mats;
    return HP75V5_GL3Cache;
end;

HP75IdentityMat3V5 := function()
    return [[1,0,0],[0,1,0],[0,0,1]];
end;

HP75InverseMat3V5 := function(A)
    local B, I;
    I := HP75IdentityMat3V5();
    for B in HP75AllGL3MatricesV5() do
        if Mat3Equal(ComposeMat3(A,B), I) and
           Mat3Equal(ComposeMat3(B,A), I) then
            return B;
        fi;
    od;
    Error("Matrice GL(3,2) non inversible (inattendu).");
end;

HP75CentralizerGL3V5 := function(gens)
    local C, X, A, ok;
    C := [];
    for X in HP75AllGL3MatricesV5() do
        ok := true;
        for A in gens do
            if not Mat3Equal(ComposeMat3(X,A), ComposeMat3(A,X)) then
                ok := false;
                break;
            fi;
        od;
        if ok then
            Add(C,X);
        fi;
    od;
    return C;
end;

HP75Vec3StringV5 := function(v)
    return Concatenation(String(v[1]),String(v[2]),String(v[3]));
end;

HP75Mat3StringV5 := function(M)
    return Concatenation(
        HP75Vec3StringV5(M[1]), "_",
        HP75Vec3StringV5(M[2]), "_",
        HP75Vec3StringV5(M[3])
    );
end;

HP75ActionTupleKeyV5 := function(mats)
    return HP75JoinListOfStrings(List(mats, HP75Mat3StringV5), "x");
end;

HP75ActionImageIdFromMatricesV5 := function(mats)
    local sz;
    sz := Length(MatrixClosure3(mats));
    if sz = 1 then
        return [1,1];
    elif sz = 2 then
        return [2,1];
    elif sz = 3 then
        return [3,1];
    elif sz = 6 then
        return [6,1];
    fi;
    Error("Image d'action HP75 v5 inattendue: taille ", sz);
end;

HP75ReferenceBasisC2CubeV5 := function(Z0)
    local nz, a, b, c;
    nz := Filtered(Elements(Z0), x -> x <> One(Z0));
    for a in nz do
        for b in nz do
            if b <> a then
                for c in nz do
                    if Size(Group([a,b,c])) = 8 then
                        return [a,b,c];
                    fi;
                od;
            fi;
        od;
    od;
    Error("Impossible de trouver une base de Z0 ~= C2^3.");
end;

HP75IntertwinerPacketsV5 := function(S, Z0)
    local base, baseMats, gl3, reps, repDict, M, Minv, mats, A,
          key, m0, actionId, C, packet, packets, seenMark, markings,
          markDict, c, m, mkey, expected, p;

    base := HP75ReferenceBasisC2CubeV5(Z0);
    baseMats := ActionMatricesOfSOnMarkedC2Cube(S, base);
    gl3 := HP75AllGL3MatricesV5();

    reps := [];
    repDict := rec();

    # Cheap 168-matrix scan: no homomorphisms, no phiLists.
    for M in gl3 do
        Minv := HP75InverseMat3V5(M);
        mats := [];
        for A in baseMats do
            Add(mats, ComposeMat3(Minv, ComposeMat3(A,M)));
        od;

        if ForAll(mats, IsMatrixInHP75ImageS3) then
            key := HP75ActionTupleKeyV5(mats);
            if not IsBound(repDict.(key)) then
                m0 := ApplyMatrixToMarkingC2Cube(base, M);
                actionId := HP75ActionImageIdFromMatricesV5(mats);
                repDict.(key) := Length(reps) + 1;
                Add(reps, rec(
                    actionKey := key,
                    actionMats := mats,
                    actionId := actionId,
                    oneIntertwiner := M,
                    oneMarking := m0
                ));
            fi;
        fi;
    od;

    packets := [];
    markings := [];
    markDict := rec();
    seenMark := rec();
    expected := 0;

    for p in reps do
        C := HP75CentralizerGL3V5(p.actionMats);
        packet := rec(
            actionKey := p.actionKey,
            actionMats := p.actionMats,
            actionId := p.actionId,
            centralizerSize := Length(C),
            markings := []
        );

        expected := expected + Length(C);

        # If m0 gives beta, then m0*C gives the same exact beta.
        for c in C do
            m := ApplyMatrixToMarkingC2Cube(p.oneMarking, c);

            # Optional expensive audit.  Disabled in production because
            # centralizer theory already guarantees the same exact action.
            if HP75V5DeepAudit = true then
                if HP75ActionTupleKeyV5(
                    ActionMatricesOfSOnMarkedC2Cube(S,m)
                ) <> p.actionKey then
                    Error(
                        "Erreur centralisateur v5: l'action exacte a change."
                    );
                fi;
            fi;

            mkey := HP75MarkingKeyStringFromElements(S,m);
            if IsBound(seenMark.(mkey)) then
                Error("Erreur v5: un marquage apparait dans deux paquets d'action.");
            fi;

            seenMark.(mkey) := true;
            Add(packet.markings, m);
            Add(markings, m);
            markDict.(mkey) := Length(markings);
        od;

        Add(packets, packet);
    od;

    if Length(markings) <> expected then
        Error(
            "Erreur v5 intertwiners: somme des centralisateurs = ",
            expected, " mais marquages distincts = ", Length(markings)
        );
    fi;

    return rec(
        baseMarking := base,
        exactActionPackets := packets,
        markings := markings,
        markingDict := markDict,
        numberExactActions := Length(packets),
        numberAdmissibleMarkings := Length(markings)
    );
end;

HP75OutIndexFromPermV5 := function(p)
    local data, i;
    data := HP75OutGroupData();
    for i in [1..Length(data.elems)] do
        if data.elems[i].perm = p then
            return i;
        fi;
    od;
    Error("Permutation hors du modele HP75.");
end;

HP75PhiCodesStringV5 := function(codes)
    return HP75JoinListOfStrings(List(codes, x -> String(x)), "_");
end;

HP75PhiListFromCodesV5 := function(codes)
    local data;
    data := HP75OutGroupData();
    return List(codes, i -> ShallowCopy(data.elems[i].enc));
end;

CompatiblePhiDataHP75V5 := function(S, Z0, marking, nat, Q)
    local dataOut, outG, kvecs, gensQ, elemsQ, elemsS,
          lambdaGenA, lambdaAllA, tuples, tuple, imgs, i, hom,
          codes, imgPerms, phiId, results, seen, key, s, q, p;

    dataOut := HP75OutGroupData();
    outG := dataOut.group;
    kvecs := HP75KernelVectors();

    gensQ := GeneratorsOfGroup(Q);
    elemsQ := Elements(Q);
    elemsS := Elements(S);

    lambdaGenA :=
        List(gensQ, q -> HP75LambdaA2OfQElement(nat, marking, q));
    lambdaAllA :=
        List(elemsQ, q -> HP75LambdaA2OfQElement(nat, marking, q));

    tuples := AllTuplesFromListHP75(kvecs, Length(gensQ));

    results := [];
    seen := rec();

    for tuple in tuples do
        imgs := [];
        for i in [1..Length(gensQ)] do
            Add(
                imgs,
                HP75PermFromVectorAndA2(tuple[i], lambdaGenA[i])
            );
        od;

        hom := GroupHomomorphismByImages(Q, outG, gensQ, imgs);

        if hom <> fail and HP75HomMatchesLambda(hom, elemsQ, lambdaAllA) then
            codes := [];

            for s in elemsS do
                q := Image(nat,s);
                p := Image(hom,q);
                Add(codes, HP75OutIndexFromPermV5(p));
            od;

            key := HP75PhiCodesStringV5(codes);

            if not IsBound(seen.(key)) then
                seen.(key) := true;
                imgPerms := List(elemsQ, q -> Image(hom,q));
                phiId := HP75PhiImageIdFromPerms(imgPerms);
                Add(results, rec(
                    phiCodes := codes,
                    phiImageId := phiId
                ));
            fi;
        fi;
    od;

    return results;
end;

HP75MarkingIdFromElementsV5 := function(S, markDict, marking)
    local key;
    key := HP75MarkingKeyStringFromElements(S, marking);
    if IsBound(markDict.(key)) then
        return markDict.(key);
    fi;
    return fail;
end;

HP75AutPreIndexMapV5 := function(elemsS, aut)
    local preMap, i, im, j;
    preMap := [];
    for i in [1..Length(elemsS)] do
        im := Image(aut, elemsS[i]);
        j := Position(elemsS, im);
        if j = fail then
            Error("Image d'automorphisme introuvable dans Elements(S).");
        fi;
        preMap[j] := i;
    od;
    return preMap;
end;

HP75OutConjugationCodeMapV5 := function(o)
    local data, map, i, cp;
    data := HP75OutGroupData();
    map := [];
    for i in [1..24] do
        cp := data.elems[i].perm ^ o;
        map[i] := HP75OutIndexFromPermV5(cp);
    od;
    return map;
end;

HP75BuildTransformsV5 := function(S, autS, Z0, markingPacket)
    local stab, stabGens, outGens, markings, markDict, elemsS,
          outTransforms, autTransforms, o, A2, h3, markMap,
          i, m2, id2, codeMap, a, preMap;

    stab := StabilizerOfZ0InAutSHP75(autS, Z0);
    stabGens := GeneratorsOfGroup(stab);
    outGens := GeneratorsOfGroup(HP75OutGroupData().group);

    markings := markingPacket.markings;
    markDict := markingPacket.markingDict;
    elemsS := Elements(S);

    outTransforms := [];

    for o in outGens do
        A2 := HP75A2FromPerm(o);
        h3 := Block3FromGL2(InverseMat2HP75(A2));
        markMap := [];

        for i in [1..Length(markings)] do
            m2 := ApplyMatrixToMarkingC2Cube(markings[i], h3);
            id2 := HP75MarkingIdFromElementsV5(S, markDict, m2);
            if id2 = fail then
                Error("v5: l'action de Out(P) quitte les marquages admissibles.");
            fi;
            markMap[i] := id2;
        od;

        codeMap := HP75OutConjugationCodeMapV5(o);

        Add(outTransforms, rec(
            kind := "out",
            markingMap := markMap,
            codeMap := codeMap
        ));
    od;

    autTransforms := [];

    for a in stabGens do
        markMap := [];

        for i in [1..Length(markings)] do
            m2 := ImageOfMarkingByAutSHP75(markings[i], a);
            id2 := HP75MarkingIdFromElementsV5(S, markDict, m2);
            if id2 = fail then
                Error("v5: Stab_Aut(S)(Z0) quitte les marquages admissibles.");
            fi;
            markMap[i] := id2;
        od;

        preMap := HP75AutPreIndexMapV5(elemsS, a);

        Add(autTransforms, rec(
            kind := "autS",
            markingMap := markMap,
            preIndexMap := preMap
        ));
    od;

    return rec(
        outTransforms := outTransforms,
        autTransforms := autTransforms,
        numberOutGenerators := Length(outTransforms),
        numberAutGenerators := Length(autTransforms)
    );
end;

HP75MarkingOrbitRepsV5 := function(markingPacket, transforms)
    local n, unseen, reps, queue, qpos, start, cur, t, nxt, i;

    n := Length(markingPacket.markings);
    unseen := List([1..n], i -> true);
    reps := [];

    start := 1;

    while true do
        while start <= n and unseen[start] = false do
            start := start + 1;
        od;

        if start > n then
            break;
        fi;

        Add(reps, start);
        queue := [start];
        qpos := 1;
        unseen[start] := false;

        while qpos <= Length(queue) do
            cur := queue[qpos];
            qpos := qpos + 1;

            for t in transforms.outTransforms do
                nxt := t.markingMap[cur];
                if unseen[nxt] = true then
                    unseen[nxt] := false;
                    Add(queue,nxt);
                fi;
            od;

            for t in transforms.autTransforms do
                nxt := t.markingMap[cur];
                if unseen[nxt] = true then
                    unseen[nxt] := false;
                    Add(queue,nxt);
                fi;
            od;
        od;
    od;

    return reps;
end;

HP75PairStateKeyV5 := function(markingId, phiCodes)
    return Concatenation(
        "K", String(markingId), "_P", HP75PhiCodesStringV5(phiCodes)
    );
end;

HP75ApplyOutToCodesV5 := function(codes, codeMap)
    return List(codes, c -> codeMap[c]);
end;

HP75ApplyAutSToCodesV5 := function(codes, preMap)
    return List(preMap, i -> codes[i]);
end;

HP75MarkPairOrbitSeenV5 := function(
    startMarkingId, startCodes, transforms, globalSeen
)
    local queue, qpos, st, key, t, mid2, codes2, key2, orbitSize;

    queue := [rec(markingId := startMarkingId, phiCodes := startCodes)];
    qpos := 1;
    orbitSize := 0;

    while qpos <= Length(queue) do
        st := queue[qpos];
        qpos := qpos + 1;

        key := HP75PairStateKeyV5(st.markingId, st.phiCodes);

        if not IsBound(globalSeen.(key)) then
            globalSeen.(key) := true;
            orbitSize := orbitSize + 1;

            for t in transforms.outTransforms do
                mid2 := t.markingMap[st.markingId];
                codes2 := HP75ApplyOutToCodesV5(st.phiCodes, t.codeMap);
                key2 := HP75PairStateKeyV5(mid2,codes2);

                if not IsBound(globalSeen.(key2)) then
                    Add(queue, rec(markingId := mid2, phiCodes := codes2));
                fi;
            od;

            for t in transforms.autTransforms do
                mid2 := t.markingMap[st.markingId];
                codes2 := HP75ApplyAutSToCodesV5(
                    st.phiCodes, t.preIndexMap
                );
                key2 := HP75PairStateKeyV5(mid2,codes2);

                if not IsBound(globalSeen.(key2)) then
                    Add(queue, rec(markingId := mid2, phiCodes := codes2));
                fi;
            od;
        fi;
    od;

    return orbitSize;
end;

MarkedOrbitsForZ0RepHP75V5 := function(S, autS, Z0)
    local markingPacket, transforms, markReps, nat, Q, rId,
          globalSeen, classReps, stats, mid, marking, actionId,
          phis, pd, seedKey, orbitSize, datum, centralizerHistogram,
          p, row, found;

    markingPacket := HP75IntertwinerPacketsV5(S,Z0);
    transforms := HP75BuildTransformsV5(S,autS,Z0,markingPacket);
    markReps := HP75MarkingOrbitRepsV5(markingPacket,transforms);

    nat := NaturalHomomorphismByNormalSubgroup(S,Z0);
    Q := Image(nat);
    rId := IdGroupSafe(Q);

    globalSeen := rec();
    classReps := [];

    stats := rec(
        admissibleMarkings := markingPacket.numberAdmissibleMarkings,
        exactActionPackets := markingPacket.numberExactActions,
        markingOrbitReps := Length(markReps),
        compatiblePhiCalls := 0,
        phiSeeds := 0,
        pairOrbitStates := 0,
        zphiClasses := 0
    );

    centralizerHistogram := [];

    for p in markingPacket.exactActionPackets do
        found := false;
        for row in centralizerHistogram do
            if row[1] = p.actionId and row[2] = p.centralizerSize then
                row[3] := row[3] + 1;
                found := true;
                break;
            fi;
        od;
        if not found then
            Add(
                centralizerHistogram,
                [p.actionId, p.centralizerSize, 1]
            );
        fi;
    od;

    stats.centralizerHistogram := centralizerHistogram;

    for mid in markReps do
        marking := markingPacket.markings[mid];
        actionId := ActionImageIdHP75(S,marking);

        stats.compatiblePhiCalls := stats.compatiblePhiCalls + 1;

        phis := CompatiblePhiDataHP75V5(S,Z0,marking,nat,Q);
        stats.phiSeeds := stats.phiSeeds + Length(phis);

        for pd in phis do
            seedKey := HP75PairStateKeyV5(mid,pd.phiCodes);

            if not IsBound(globalSeen.(seedKey)) then
                orbitSize := HP75MarkPairOrbitSeenV5(
                    mid, pd.phiCodes, transforms, globalSeen
                );

                stats.pairOrbitStates :=
                    stats.pairOrbitStates + orbitSize;
                stats.zphiClasses := stats.zphiClasses + 1;

                datum := rec(
                    Z0 := Z0,
                    marking := marking,
                    RId := rId,
                    actionImageId := actionId,
                    phiImageId := pd.phiImageId,
                    phiList := HP75PhiListFromCodesV5(pd.phiCodes),
                    v5PairOrbitSize := orbitSize
                );

                Add(classReps, datum);
            fi;
        od;
    od;

    return rec(
        reps := classReps,
        stats := stats
    );
end;

MarkedOrbitsHP75InSmallGroupV5 := function(S)
    local autS, zReps, allReps, Z0, packet, stats, s;

    autS := AutomorphismGroup(S);
    zReps := NormalC2CubeSubgroupOrbitRepsHP75(S,autS);
    allReps := [];

    stats := rec(
        z0OrbitReps := Length(zReps),
        admissibleMarkings := 0,
        exactActionPackets := 0,
        markingOrbitReps := 0,
        compatiblePhiCalls := 0,
        phiSeeds := 0,
        pairOrbitStates := 0,
        zphiClasses := 0
    );

    for Z0 in zReps do
        packet := MarkedOrbitsForZ0RepHP75V5(S,autS,Z0);
        Append(allReps,packet.reps);

        s := packet.stats;
        stats.admissibleMarkings :=
            stats.admissibleMarkings + s.admissibleMarkings;
        stats.exactActionPackets :=
            stats.exactActionPackets + s.exactActionPackets;
        stats.markingOrbitReps :=
            stats.markingOrbitReps + s.markingOrbitReps;
        stats.compatiblePhiCalls :=
            stats.compatiblePhiCalls + s.compatiblePhiCalls;
        stats.phiSeeds :=
            stats.phiSeeds + s.phiSeeds;
        stats.pairOrbitStates :=
            stats.pairOrbitStates + s.pairOrbitStates;
        stats.zphiClasses :=
            stats.zphiClasses + s.zphiClasses;
    od;

    return rec(reps := allReps, stats := stats);
end;

ZPhiClassesHP75InSmallGroupV5 := function(ordS,idS)
    local S, packet, records, d;

    S := SmallGroup(ordS,idS);
    packet := MarkedOrbitsHP75InSmallGroupV5(S);
    records := [];

    for d in packet.reps do
        Add(records,ZPhiOrbitRecordHP75(S,d));
    od;

    return rec(
        records := records,
        stats := packet.stats
    );
end;

HP75V5OneNRaw := function(n)
    local ordS, nrS, idS, recordsAll, packet, recs, r,
          byR, byAction, byPhiImage, byRAction, byRPhiImage,
          byRActionPhi, t0, t1, stats, s;

    t0 := Runtime();

    ordS := 8*n;
    nrS := NumberSmallGroups(ordS);

    recordsAll := [];
    byR := [];
    byAction := [];
    byPhiImage := [];
    byRAction := [];
    byRPhiImage := [];
    byRActionPhi := [];

    stats := rec(
        z0OrbitReps := 0,
        admissibleMarkings := 0,
        exactActionPackets := 0,
        markingOrbitReps := 0,
        compatiblePhiCalls := 0,
        phiSeeds := 0,
        pairOrbitStates := 0,
        zphiClasses := 0
    );

    for idS in [1..nrS] do
        packet := ZPhiClassesHP75InSmallGroupV5(ordS,idS);
        recs := packet.records;
        s := packet.stats;

        stats.z0OrbitReps := stats.z0OrbitReps + s.z0OrbitReps;
        stats.admissibleMarkings :=
            stats.admissibleMarkings + s.admissibleMarkings;
        stats.exactActionPackets :=
            stats.exactActionPackets + s.exactActionPackets;
        stats.markingOrbitReps :=
            stats.markingOrbitReps + s.markingOrbitReps;
        stats.compatiblePhiCalls :=
            stats.compatiblePhiCalls + s.compatiblePhiCalls;
        stats.phiSeeds := stats.phiSeeds + s.phiSeeds;
        stats.pairOrbitStates :=
            stats.pairOrbitStates + s.pairOrbitStates;
        stats.zphiClasses :=
            stats.zphiClasses + s.zphiClasses;

        for r in recs do
            Add(recordsAll,r);
            AddOrIncreasePairCount(byR,r.RId,1);
            AddOrIncreasePairCount(byAction,r.actionImageId,1);
            AddOrIncreasePairCount(byPhiImage,r.phiImageId,1);
            AddOrIncreaseTripleCount(
                byRAction,r.RId,r.actionImageId,1
            );
            AddOrIncreaseTripleCount(
                byRPhiImage,r.RId,r.phiImageId,1
            );
            AddOrIncreaseQuadrupleCount(
                byRActionPhi,
                r.RId,r.actionImageId,r.phiImageId,1
            );
        od;
    od;

    SortPairCountList(byR);
    SortPairCountList(byAction);
    SortPairCountList(byPhiImage);
    SortTripleCountList(byRAction);
    SortTripleCountList(byRPhiImage);
    SortQuadrupleCountList(byRActionPhi);

    t1 := Runtime();

    if stats.zphiClasses <> Length(recordsAll) then
        Error(
            "Audit v5: stats.zphiClasses <> Length(recordsAll): ",
            stats.zphiClasses, " <> ", Length(recordsAll)
        );
    fi;

    return rec(
        n := n,
        orderS := ordS,
        orderExtension := 7680*n,
        numberSmallGroupsS := nrS,
        totalClasses := Length(recordsAll),
        byR := byR,
        byAction := byAction,
        byPhiImage := byPhiImage,
        byRAction := byRAction,
        byRPhiImage := byRPhiImage,
        byRActionPhi := byRActionPhi,
        records := recordsAll,
        runtimeMilliseconds := t1-t0,
        v5Stats := stats
    );
end;

ZPhiClasses_C2Cube_S4_NonFaithful_OneN := function(n)
    return HP75V5OneNRaw(n);
end;

ZPhiClasses_C2Cube_S4_NonFaithful_TableV5 := function(a,b)
    local table, n, res;

    if a < 1 then
        Error("La borne inferieure doit etre positive.");
    fi;

    table := [];

    for n in [a..b] do
        Print("\n============================================================\n");
        Print(
            "Calcul HP (7,5) v5, n=",n,
            ", ordre S=",8*n,
            ", ordre E=",7680*n,"\n"
        );
        Print("============================================================\n");

        res := ZPhiClasses_C2Cube_S4_NonFaithful_OneN(n);
        Add(table,res);

        Print(
            "n=",n,
            " totalClasses=",res.totalClasses,
            " runtimeMs=",res.runtimeMilliseconds,"\n"
        );
        Print("byR = ",res.byR,"\n");
        Print("byAction = ",res.byAction,"\n");
        Print("byPhiImage = ",res.byPhiImage,"\n");
        Print(
            "v5Stats: markings=",res.v5Stats.admissibleMarkings,
            " markOrbitReps=",res.v5Stats.markingOrbitReps,
            " phiCalls=",res.v5Stats.compatiblePhiCalls,
            " phiSeeds=",res.v5Stats.phiSeeds,
            " pairOrbitStates=",res.v5Stats.pairOrbitStates,
            "\n"
        );

        GASMAN("collect");
    od;

    return table;
end;

ZPhiClasses_C2Cube_S4_NonFaithful_Table := ZPhiClasses_C2Cube_S4_NonFaithful_TableV5;

HP75_Table_2_15 := function()
    return ZPhiClasses_C2Cube_S4_NonFaithful_Table(2,15);
end;

###

## Use case : PhiClasses_C2Cube_S4_NonFaithful_Table(2,15);
# counts extensions by groups of order n=2 to n=15 (Z(P)=2^3, Out(P)=Sym(4), 
#kernel of action is V4 <Sym(4)
# for a given n : ZPhiClasses_C2Cube_S4_NonFaithful_OneN(n);;
