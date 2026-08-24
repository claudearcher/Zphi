#############################################################################
##
##  source : zphi a method by Claude Archer, described in his PhD thesis
##  "Classification of Group Extensions", Université Libre de Bruxelles (2002)
##
##  ZPhiClasses_PG3840_5_V4_OutD8_trivial_GAP415.g
##
##  Groupe parfait d'ordre 3840, label Holt--Plesken (6,5) :
##
##      Z(P) = V4,       Out(P) = D8,
##
##  et l'action de Out(P) sur Z(P) est TRIVIALE. Ainsi
##
##      Ker( Out(P) -> Aut(Z(P)) ) = D8 tout entier.
##
##  Ce fichier compte les Zphi-classes pour tous les couplings
##
##      phi : R -> D8,
##
##  sans imposer que l'image soit D8. Chaque morphisme est traite comme
##  une surjection R -> U sur son image U, pour les huit classes de
##  conjugaison de sous-groupes U<=D8.
##
##  Si S est le supplement resoluble et Z=P cap S, alors
##
##      |Z|=4,  Z=V4,  Z <= Z(S),  S/Z = R,  |S|=4*|R|.
##
##  Pour f:S->D8 induit par phi, on pose N=Ker(f). Il faut donc
##
##      Z <= N,       S/N = U = Im(phi) <= D8.
##
##  DIFFERENCE IMPORTANTE AVEC LE CAS (6,4) :
##
##  Aut(P) agit trivialement sur Z(P). Il faut donc conserver dans les
##  donnees une identification ordonnee Z(P)->Z. Pour chaque Z=V4 il y a
##  six bases ordonnees possibles. Elles sont ensuite quotientées par
##  Aut(S), mais pas par une action de Aut(P) sur le centre.
##
##  Sur la cible D8, seuls les automorphismes interieurs proviennent de la
##  conjugaison par Aut(P) sur Out(P). Le calcul prend donc les orbites sous
##
##      Aut(S) x Inn(D8),
##
##  et NON sous Aut(S) x Aut(D8).
##
##  Convention : n=|R|, donc les groupes S examines ont ordre 4*n.
##
#############################################################################


#############################################################################
##  1. Modele canonique : D8 agit trivialement sur V4
#############################################################################

PG65_D8TrivialActionData := function()
    local r, s, D8, z1, z2, V4, idV4, trivialAut, rho, autD8, innerD8;

    r := (1,2,3,4);
    s := (2,4);
    D8 := Group(r,s);

    z1 := (1,2)(3,4);
    z2 := (1,3)(2,4);
    V4 := Group(z1,z2);

    idV4 := IdentityMapping(V4);
    trivialAut := Group(idV4);
    rho := GroupHomomorphismByImages(
        D8, trivialAut,
        [r,s],
        [idV4,idV4]
    );

    if Size(D8) <> 8 or IdGroup(D8) <> [8,3] then
        Error("Le modele canonique n'est pas D8");
    fi;
    if Kernel(rho) <> D8 or Size(Image(rho)) <> 1 then
        Error("L'action construite de D8 sur V4 n'est pas triviale");
    fi;

    autD8 := AutomorphismGroup(D8);
    innerD8 := Group(List(GeneratorsOfGroup(D8), x ->
        InnerAutomorphism(D8,x)
    ));

    if Size(autD8) <> 8 or Size(innerD8) <> 4 then
        Error("Aut(D8) ou Inn(D8) n'a pas l'ordre attendu");
    fi;

    return rec(
        D8             := D8,
        r              := r,
        s              := s,
        V4             := V4,
        v4Basis        := [z1,z2],
        action         := rho,
        actionImage    := Image(rho),
        kernel         := D8,
        autD8          := autD8,
        innerD8        := innerD8,
        kernelVerified := true
    );
end;


#############################################################################
##  2. Fonctions internes : V4, bases et morphismes
#############################################################################

PG65_IsV4 := function(G)
    return Size(G)=4
       and IsAbelian(G)
       and ForAll(Elements(G), x -> Order(x) <= 2);
end;


# Les six bases ordonnees de Z=V4. Une base [u,v] represente
# l'identification z1->u, z2->v depuis le V4 canonique.
PG65_OrderedBasesV4 := function(Z)
    local nontrivial, bases, u, v;

    nontrivial := Filtered(Elements(Z), x -> x <> One(Z));
    bases := [];
    for u in nontrivial do
        for v in nontrivial do
            if u <> v then
                Add(bases,[u,v]);
            fi;
        od;
    od;

    if Length(bases) <> 6 then
        Error("Un V4 doit fournir exactement six bases ordonnees");
    fi;
    return bases;
end;


PG65_SameMapOnGenerators := function(f, g, gens)
    return ForAll(gens, x -> Image(f,x)=Image(g,x));
end;


PG65_AddMapIfNew := function(maps, f, gens)
    if ForAll(maps, g -> not PG65_SameMapOnGenerators(f,g,gens)) then
        Add(maps,f);
        return true;
    fi;
    return false;
end;


# Un candidat contient :
#   Z      copie centrale de Z(P),
#   N      noyau de f:S->D8,
#   basis  identification ordonnee V4->Z,
#   f      morphisme oriente vers le D8 canonique.
PG65_CandidateEqual := function(c, d, gensS)
    return c.Z=d.Z
       and c.N=d.N
       and c.basis=d.basis
       and PG65_SameMapOnGenerators(c.f,d.f,gensS);
end;


PG65_AddCandidateIfNew := function(candidates, c, gensS)
    if ForAll(candidates, d -> not PG65_CandidateEqual(c,d,gensS)) then
        Add(candidates,c);
        return true;
    fi;
    return false;
end;


PG65_PositionCandidate := function(candidates, c, gensS)
    return PositionProperty(candidates, d ->
        PG65_CandidateEqual(c,d,gensS)
    );
end;


#############################################################################
##  3. Actions exactes definissant l'equivalence Zphi
#############################################################################

# Action de alpha dans Aut(S).
# Si f:S->D8, le morphisme transporte est alpha^-1*f, de noyau alpha(N).
# La base [u,v] devient [alpha(u),alpha(v)].
PG65_ActByAutS := function(c, alpha)
    return rec(
        Z     := Image(alpha,c.Z),
        N     := Image(alpha,c.N),
        basis := List(c.basis, x -> Image(alpha,x)),
        f     := alpha^-1 * c.f
    );
end;


# Action d'un automorphisme interieur beta de D8 : postcomposition f*beta.
# La base du centre ne change pas, car Aut(P) agit trivialement sur Z(P).
PG65_ActByInnerD8 := function(c, beta)
    return rec(
        Z     := c.Z,
        N     := c.N,
        basis := c.basis,
        f     := c.f * beta
    );
end;


# Comptage d'orbites sans construire un produit direct artificiel de groupes
# de mappings. Les generateurs de Aut(S) et Inn(D8) agissent successivement.
PG65_NumberZPhiOrbits := function(candidates, autS, innerD8, gensS)
    local autGens, innerGens, seen, number, i, queue, head, c, d, j,alpha, beta;

    if Length(candidates)=0 then
        return 0;
    fi;

    autGens := GeneratorsOfGroup(autS);
    innerGens := GeneratorsOfGroup(innerD8);
    seen := List([1..Length(candidates)], x -> false);
    number := 0;

    for i in [1..Length(candidates)] do
        if not seen[i] then
            number := number+1;
            queue := [i];
            seen[i] := true;
            head := 1;

            while head <= Length(queue) do
                c := candidates[queue[head]];
                head := head+1;

                for alpha in autGens do
                    d := PG65_ActByAutS(c,alpha);
                    j := PG65_PositionCandidate(candidates,d,gensS);
                    if j=fail then
                        Error("Le domaine des candidats n'est pas ferme sous Aut(S)");
                    fi;
                    if not seen[j] then
                        seen[j] := true;
                        Add(queue,j);
                    fi;
                od;

                for beta in innerGens do
                    d := PG65_ActByInnerD8(c,beta);
                    j := PG65_PositionCandidate(candidates,d,gensS);
                    if j=fail then
                        Error("Le domaine des candidats n'est pas ferme sous Inn(D8)");
                    fi;
                    if not seen[j] then
                        seen[j] := true;
                        Add(queue,j);
                    fi;
                od;
            od;
        fi;
    od;

    return number;
end;


#############################################################################
##  5. Construction des candidats pour un supplement S fixe
#############################################################################

ZPhiClasses_PG65_D8_FullImage_ForS := function(S)
    local data, gensS, centreS, normals, centralV4s, quotientMaps,allTargetAut, orientedMaps,
	f0, beta, f, N, Z, basis,candidates, autS, total;

    data := PG65_D8TrivialActionData();

    if Size(S) mod 32 <> 0 or not IsSolvableGroup(S) then
        return rec(
            summary := rec(
                centralV4                 := 0,
                quotientMapsModuloAutD8   := 0,
                orientedMaps              := 0,
                admissibleCandidates      := 0
            ),
            total := 0,
            totalClasses := 0
        );
    fi;

    gensS := GeneratorsOfGroup(S);
    centreS := Centre(S);
    normals := NormalSubgroups(S);
    centralV4s := Filtered(normals, Z ->
        PG65_IsV4(Z) and IsSubgroup(centreS,Z)
    );

    if Length(centralV4s)=0 then
        return rec(
            summary := rec(
                centralV4                 := 0,
                quotientMapsModuloAutD8   := 0,
                orientedMaps              := 0,
                admissibleCandidates      := 0
            ),
            total := 0,
            totalClasses := 0
        );
    fi;

    if not IsBound(GQuotients) then
        Error("La fonction GQuotients n'est pas disponible");
    fi;

    # GQuotients peut identifier les morphismes modulo Aut(D8). Or la
    # relation Zphi n'autorise ici que Inn(D8). On reconstitue donc toutes
    # les orientations par postcomposition avec Aut(D8), puis on dedoublonne.
    quotientMaps := GQuotients(S,data.D8);
    allTargetAut := Elements(data.autD8);
    orientedMaps := [];
    for f0 in quotientMaps do
        for beta in allTargetAut do
            f := f0*beta;
            PG65_AddMapIfNew(orientedMaps,f,gensS);
        od;
    od;

    candidates := [];
    for f in orientedMaps do
        N := Kernel(f);
        for Z in centralV4s do
            if IsSubgroup(N,Z) then
                for basis in PG65_OrderedBasesV4(Z) do
                    PG65_AddCandidateIfNew(candidates,rec(
                        Z     := Z,
                        N     := N,
                        basis := basis,
                        f     := f
                    ),gensS);
                od;
            fi;
        od;
    od;

    if Length(candidates)=0 then
        return rec(
            summary := rec(
                centralV4                 := Length(centralV4s),
                quotientMapsModuloAutD8   := Length(quotientMaps),
                orientedMaps              := Length(orientedMaps),
                admissibleCandidates      := 0
            ),
            total := 0,
            totalClasses := 0
        );
    fi;

    autS := AutomorphismGroup(S);
    total := PG65_NumberZPhiOrbits(
        candidates,autS,data.innerD8,gensS
    );

    return rec(
        summary := rec(
            centralV4                 := Length(centralV4s),
            quotientMapsModuloAutD8   := Length(quotientMaps),
            orientedMaps              := Length(orientedMaps),
            admissibleCandidates      := Length(candidates)
        ),
        total := total,
        totalClasses := total
    );
end;


#############################################################################
##  6. Enveloppes SmallGroups et resultats compacts summary/total
#############################################################################

# n=|R| et S=SmallGroup(4*n,i).
ZPhiClasses_PG65_D8_FullImage_SmallGroup := function(n,i)
    local S, ans;

    if n mod 8 <> 0 then
        Error("Pour une image D8 surjective, |R| doit etre divisible par 8");
    fi;

    S := SmallGroup(4*n,i);
    ans := ZPhiClasses_PG65_D8_FullImage_ForS(S);
    return rec(
        smallGroup := [4*n,i],
        summary := ans.summary,
        total := ans.total,
        totalClasses := ans.total
    );
end;


ZPhiClasses_PG65_D8_FullImage_AllS_FromTo := function(n,first,last)
    local number, summary, total, i, ans;

    if n mod 8 <> 0 then
        Error("Pour une image D8 surjective, |R| doit etre divisible par 8");
    fi;

    number := NumberSmallGroups(4*n);
    if first<1 or last<first or last>number then
        Error("Plage SmallGroups invalide");
    fi;

    summary := [];
    total := 0;
    for i in [first..last] do
        ans := ZPhiClasses_PG65_D8_FullImage_SmallGroup(n,i);
        if ans.total<>0 then
            Add(summary,[i,ans.total]);
            total := total+ans.total;
        fi;
    od;

    return rec(
        orderR := n,
        orderS := 4*n,
        range := [first,last],
        groupsTested := last-first+1,
        contributingGroups := Length(summary),
        summary := summary,
        total := total,
        totalClasses := total
    );
end;


ZPhiClasses_PG65_D8_FullImage_AllS := function(n)
    return ZPhiClasses_PG65_D8_FullImage_AllS_FromTo(
        n,1,NumberSmallGroups(4*n)
    );
end;


#############################################################################
##  7. Alias descriptifs
#############################################################################

ZPhiClasses_V4_D8_Trivial_FullImage_ForS :=
    ZPhiClasses_PG65_D8_FullImage_ForS;
ZPhiClasses_V4_D8_Trivial_FullImage_SmallGroup :=
    ZPhiClasses_PG65_D8_FullImage_SmallGroup;
ZPhiClasses_V4_D8_Trivial_FullImage_AllS_FromTo :=
    ZPhiClasses_PG65_D8_FullImage_AllS_FromTo;
ZPhiClasses_V4_D8_Trivial_FullImage_AllS :=
    ZPhiClasses_PG65_D8_FullImage_AllS;


#############################################################################
##  Exemples (non executes automatiquement)
##
##  Read("ZPhiClasses_PG65_D8_trivial.g");
##
##  d := PG65_D8TrivialActionData();;
##  d.actionImage;        # groupe trivial
##  d.kernel=d.D8;        # true
##
##  one := ZPhiClasses_PG65_D8_SmallGroup(8,1);;
##  one.summary;
##  one.total;
##
##  res := ZPhiClasses_PG65_D8_AllS(8);;
##  res.summary;          # [ [i,nombre_de_classes], ... ]
##  res.total;
##
##  # check.kernelIsAllD8;  # true
#############################################################################


#############################################################################
##
##  8. VERSION GENERALE : TOUTES LES IMAGES U <= D8
##
##  Les definitions publiques de la section 6, qui imposaient U=D8, sont
##  remplacees ci-dessous. Apres lecture complete du fichier, ce sont donc
##  les fonctions de cette section qui sont actives.
##
##  Toute application phi:R->D8 est une surjection R->U sur son image.
##  On choisit un representant U de chaque classe de conjugaison dans D8 :
##
##      1, <r^2>, <s>, <rs>, <r>, <r^2,s>, <r^2,rs>, D8.
##
##  Puisque D8 agit trivialement sur Z(P), la condition sur le supplement
##  est toujours
##
##      Z = V4 <= Z(S),       Z <= Ker(f),       f:S->U surjectif.
##
##  Une donnee comprend aussi une base ordonnee de Z, c'est-a-dire une
##  identification Z(P)->Z. Aut(P) fixant Z(P) point par point, cette base
##  n'est jamais modifiee par un element du normalisateur N_D8(U).
##
##  L'equivalence est engendree par :
##    * Aut(S), agissant simultanement sur Z, Ker(f), la base et f;
##    * N_D8(U), agissant sur f par conjugaison de U.
##
#############################################################################


PG65_D8ImageClasses := function(data)
    local D8, r, s;

    D8 := data.D8;
    r := data.r;
    s := data.s;

    return [
        rec(name:="1",       U:=TrivialSubgroup(D8)),
        rec(name:="C2_r2",   U:=Group(r^2)),
        rec(name:="C2_s",    U:=Group(s)),
        rec(name:="C2_rs",   U:=Group(r*s)),
        rec(name:="C4_r",    U:=Group(r)),
        rec(name:="V4_H",    U:=Group(r^2,s)),
        rec(name:="V4_Hbis", U:=Group(r^2,r*s)),
        rec(name:="D8",      U:=D8)
    ];
end;


PG65_GQuotientsIncludingTrivial := function(S,U)
    local gensS, oneU, images;

    if Size(U)>1 then
        return GQuotients(S,U);
    fi;

    gensS := GeneratorsOfGroup(S);
    oneU := One(U);
    images := List(gensS, x -> oneU);
    return [GroupHomomorphismByImages(S,U,gensS,images)];
end;


# Action d'un element g de N_D8(U). La conjugaison par g induit un
# automorphisme de U. La base de Z ne change pas puisque rho(g)=1.
PG65_ActByNormalizerGeneral := function(c,g,U)
    local beta;

    beta := ConjugatorAutomorphism(U,g);
    return rec(
        Z     := c.Z,
        N     := c.N,
        basis := c.basis,
        f     := c.f*beta
    );
end;


PG65_NumberGeneralOrbits := function(candidates,autS,normalizer,U,gensS)
    local autGens, normGens, seen, number, i, queue, head, c, d, j,alpha, g;

    if Length(candidates)=0 then
        return 0;
    fi;

    autGens := GeneratorsOfGroup(autS);
    normGens := GeneratorsOfGroup(normalizer);
    seen := List([1..Length(candidates)], x -> false);
    number := 0;

    for i in [1..Length(candidates)] do
        if not seen[i] then
            number := number+1;
            queue := [i];
            seen[i] := true;
            head := 1;

            while head<=Length(queue) do
                c := candidates[queue[head]];
                head := head+1;

                for alpha in autGens do
                    d := PG65_ActByAutS(c,alpha);
                    j := PG65_PositionCandidate(candidates,d,gensS);
                    if j=fail then
                        Error("Domaine non ferme sous Aut(S)");
                    fi;
                    if not seen[j] then
                        seen[j] := true;
                        Add(queue,j);
                    fi;
                od;

                for g in normGens do
                    d := PG65_ActByNormalizerGeneral(c,g,U);
                    j := PG65_PositionCandidate(candidates,d,gensS);
                    if j=fail then
                        Error("Domaine non ferme sous N_D8(U)");
                    fi;
                    if not seen[j] then
                        seen[j] := true;
                        Add(queue,j);
                    fi;
                od;
            od;
        fi;
    od;

    return number;
end;


ZPhiClasses_PG65_D8_ForS_Image := function(S,imageData)
    local data, U, gensS, centreS, normals, centralV4s, quotientMaps,
     autU, orientedMaps, f0, beta, f, N, Z, basis, candidates,
     autS, normalizer, total;

    data := PG65_D8TrivialActionData();
    U := imageData.U;
    gensS := GeneratorsOfGroup(S);

    if not IsSolvableGroup(S) then
        return rec(name:=imageData.name, imageOrder:=Size(U),
                   centralV4:=0, candidates:=0, total:=0);
    fi;

    centreS := Centre(S);
    normals := NormalSubgroups(S);
    centralV4s := Filtered(normals, Z ->
        PG65_IsV4(Z) and IsSubgroup(centreS,Z)
    );

    quotientMaps := PG65_GQuotientsIncludingTrivial(S,U);

    # GQuotients peut ne donner qu'un representant modulo Aut(U).
    # On recree toutes les orientations, puis l'equivalence exacte sera
    # prise sous le sous-groupe induit par N_D8(U).
    autU := AutomorphismGroup(U);
    orientedMaps := [];
    for f0 in quotientMaps do
        for beta in Elements(autU) do
            f := f0*beta;
            PG65_AddMapIfNew(orientedMaps,f,gensS);
        od;
    od;

    candidates := [];
    for f in orientedMaps do
        N := Kernel(f);
        for Z in centralV4s do
            if IsSubgroup(N,Z) then
                for basis in PG65_OrderedBasesV4(Z) do
                    PG65_AddCandidateIfNew(candidates,rec(
                        Z     := Z,
                        N     := N,
                        basis := basis,
                        f     := f
                    ),gensS);
                od;
            fi;
        od;
    od;

    if Length(candidates)=0 then
        return rec(
            name:=imageData.name,
            imageOrder:=Size(U),
            action:="trivial",
            centralV4:=Length(centralV4s),
            quotientMaps:=Length(quotientMaps),
            orientedMaps:=Length(orientedMaps),
            candidates:=0,
            total:=0
        );
    fi;

    autS := AutomorphismGroup(S);
    normalizer := Normalizer(data.D8,U);
    total := PG65_NumberGeneralOrbits(
        candidates,autS,normalizer,U,gensS
    );

    return rec(
        name:=imageData.name,
        imageOrder:=Size(U),
        action:="trivial",
        centralV4:=Length(centralV4s),
        quotientMaps:=Length(quotientMaps),
        orientedMaps:=Length(orientedMaps),
        candidates:=Length(candidates),
        total:=total
    );
end;


# Fonction publique generale pour un supplement S fixe.
ZPhiClasses_PG65_D8_ForS := function(S)
    local data, classes, byImage, c, ans, total;

    data := PG65_D8TrivialActionData();
    classes := PG65_D8ImageClasses(data);
    byImage := [];
    total := 0;

    for c in classes do
        if (Size(S)/4) mod Size(c.U)=0 then
            ans := ZPhiClasses_PG65_D8_ForS_Image(S,c);
            Add(byImage,ans);
            total := total+ans.total;
        fi;
    od;

    return rec(
        byImage:=byImage,
        summary:=List(Filtered(byImage,x->x.total<>0),
                      x->[x.name,x.total]),
        total:=total,
        totalClasses:=total
    );
end;


# n=|R| et S=SmallGroup(4*n,i). Aucune divisibilite par 8 n'est imposee.
ZPhiClasses_PG65_D8_SmallGroup := function(n,i)
    local ans;

    ans := ZPhiClasses_PG65_D8_ForS(SmallGroup(4*n,i));
    return rec(
        smallGroup:=[4*n,i],
        byImage:=ans.byImage,
        summary:=ans.summary,
        total:=ans.total,
        totalClasses:=ans.total
    );
end;


ZPhiClasses_PG65_D8_AllS_FromTo := function(n,first,last)
    local number, data, classes, totals, summary, total, i, ans, j;

    number := NumberSmallGroups(4*n);
    if first<1 or last<first or last>number then
        Error("Plage SmallGroups invalide");
    fi;

    data := PG65_D8TrivialActionData();
    classes := Filtered(PG65_D8ImageClasses(data), c ->
        n mod Size(c.U)=0
    );
    totals := List(classes, c -> 0);
    summary := [];
    total := 0;

    for i in [first..last] do
        ans := ZPhiClasses_PG65_D8_SmallGroup(n,i);
        if ans.total<>0 then
            Add(summary,[i,ans.total]);
            total := total+ans.total;
        fi;
        for j in [1..Length(ans.byImage)] do
            totals[j] := totals[j]+ans.byImage[j].total;
        od;
    od;

    return rec(
        orderR:=n,
        orderS:=4*n,
        range:=[first,last],
        groupsTested:=last-first+1,
        contributingGroups:=Length(summary),
        byImageTotals:=List([1..Length(classes)], j ->
            [classes[j].name,totals[j]]
        ),
        summary:=summary,
        total:=total,
        totalClasses:=total
    );
end;


ZPhiClasses_PG65_D8_AllS := function(n)
    return ZPhiClasses_PG65_D8_AllS_FromTo(
        n,1,NumberSmallGroups(4*n)
    );
end;


# Somme limitee aux trois classes d'images C2 non triviales.
ZPhiClasses_PG65_D8_C2Images_AllS := function(n)
    local ans, wanted;

    ans := ZPhiClasses_PG65_D8_AllS(n);
    wanted := Filtered(ans.byImageTotals, x ->
        x[1]="C2_r2" or x[1]="C2_s" or x[1]="C2_rs"
    );
    return rec(
        orderR:=n,
        byImageTotals:=wanted,
        total:=Sum(wanted,x->x[2]),
        totalClasses:=Sum(wanted,x->x[2])
    );
end;


# Renouvellement des alias apres redefinition des fonctions publiques.
ZPhiClasses_V4_D8_Trivial_ForS := ZPhiClasses_PG65_D8_ForS;
ZPhiClasses_V4_D8_Trivial_SmallGroup :=
    ZPhiClasses_PG65_D8_SmallGroup;
ZPhiClasses_V4_D8_Trivial_AllS_FromTo :=
    ZPhiClasses_PG65_D8_AllS_FromTo;
ZPhiClasses_V4_D8_Trivial_AllS := ZPhiClasses_PG65_D8_AllS;


#############################################################################
##  Exemples generaux :
##
##  res := ZPhiClasses_PG65_D8_AllS(2);;
##  res.byImageTotals;  # 1, C2_r2, C2_s, C2_rs
##  res.summary;        # [i,total] pour SmallGroup(8,i)
##  res.total;
##
##  c2 := ZPhiClasses_PG65_D8_C2Images_AllS(2);;
##  c2.byImageTotals;
##  c2.total;
##
##  res8 := ZPhiClasses_PG65_D8_AllS(8);;
##  res8.byImageTotals; # les huit classes d'images possibles
##  res8.total;
#############################################################################


#############################################################################
##
##  9. MOTEUR INDEXE RAPIDE (remplace le moteur de la section 8)
##
##  L'ancien moteur cherchait chaque candidat transforme par un balayage
##  lineaire de toute la liste des candidats. Pour S=C2^5 et une image C2,
##  cette liste contient deja plusieurs milliers d'elements. La complexite
##  devenait donc essentiellement quadratique.
##
##  Ici un candidat est code directement par trois indices
##
##      (numero du morphisme, numero du V4 central, numero de la base),
##
##  et les actions sont precalculees sous forme de tables d'entiers. On ne
##  recalcule en outre Centre(S), les V4 centraux et Aut(S) qu'une seule fois
##  pour chaque groupe S, et non une fois par classe d'image dans D8.
##
#############################################################################


# Enumere directement les V4 du centre, sans calculer NormalSubgroups(S).
PG65_CentralV4SubgroupsFast := function(S)
    local C, involutions, result, i, j, Z;

    C := Centre(S);
    involutions := Filtered(Elements(C), x ->
        x <> One(C) and Order(x)=2
    );
    result := [];

    for i in [1..Length(involutions)] do
        for j in [i+1..Length(involutions)] do
            Z := Group(involutions[i],involutions[j]);
            if Size(Z)=4 and not Z in result then
                Add(result,Z);
            fi;
        od;
    od;

    return result;
end;


# Code entier d'un morphisme par les images d'un systeme de generateurs.
PG65_MapCodeFast := function(f,gensS,elementsU)
    return List(gensS, x -> Position(elementsU,Image(f,x)));
end;


# Tous les epimorphismes orientes S -> U.
# GQuotients donne les noyaux/quotients modulo Aut(U); on developpe ensuite
# les orientations, mais on dedoublonne par un petit code entier.
PG65_OrientedMapsFast := function(S,U,gensS)
    local quotientMaps, autU, autElements, elementsU, maps, codes,
          f0, beta, f, code;

    quotientMaps := PG65_GQuotientsIncludingTrivial(S,U);
    autU := AutomorphismGroup(U);
    autElements := Elements(autU);
    elementsU := Elements(U);
    maps := [];
    codes := [];

    for f0 in quotientMaps do
        for beta in autElements do
            f := f0*beta;
            code := PG65_MapCodeFast(f,gensS,elementsU);
            if Position(codes,code)=fail then
                Add(maps,f);
                Add(codes,code);
            fi;
        od;
    od;

    return rec(
        quotientMaps := quotientMaps,
        maps         := maps,
        codes        := codes,
        elementsU    := elementsU
    );
end;


# Donnees relatives a S, calculees une seule fois pour toutes les images U.
PG65_PrepareSContextFast := function(S)
    local gensS, centralV4s, bases, autS, autGens, autZ, autBasis,
          alpha, rowZ, rowBasis, zi, bi, Z2, z2, basis2, b2, bRow;

    if not IsSolvableGroup(S) or Size(S) mod 4 <> 0 then
        return rec(valid:=false,centralV4s:=[]);
    fi;

    gensS := GeneratorsOfGroup(S);
    centralV4s := PG65_CentralV4SubgroupsFast(S);
    if Length(centralV4s)=0 then
        return rec(
            valid       := true,
            gensS       := gensS,
            centralV4s  := [],
            bases       := [],
            autGens     := [],
            autZ        := [],
            autBasis    := []
        );
    fi;

    bases := List(centralV4s,Z -> PG65_OrderedBasesV4(Z));
    autS := AutomorphismGroup(S);
    autGens := GeneratorsOfGroup(autS);
    autZ := [];
    autBasis := [];

    for alpha in autGens do
        rowZ := [];
        rowBasis := [];
        for zi in [1..Length(centralV4s)] do
            Z2 := Image(alpha,centralV4s[zi]);
            z2 := Position(centralV4s,Z2);
            if z2=fail then
                Error("Les V4 centraux ne sont pas fermes sous Aut(S)");
            fi;
            Add(rowZ,z2);

            bRow := [];
            for bi in [1..6] do
                basis2 := List(bases[zi][bi], b -> Image(alpha,b));
                b2 := Position(bases[z2],basis2);
                if b2=fail then
                    Error("Les bases de V4 ne sont pas fermees sous Aut(S)");
                fi;
                Add(bRow,b2);
            od;
            Add(rowBasis,bRow);
        od;
        Add(autZ,rowZ);
        Add(autBasis,rowBasis);
    od;

    return rec(
        valid       := true,
        gensS       := gensS,
        centralV4s  := centralV4s,
        bases       := bases,
        autS        := autS,
        autGens     := autGens,
        autZ        := autZ,
        autBasis    := autBasis
    );
end;


# Tables d'action sur les morphismes orientes.
PG65_MapActionTablesFast := function(context,mapData,data,U)
    local maps, codes, elementsU, autMap, normMap, alpha, row, f,
          code, pos, normalizer, normGens, g, beta;

    maps := mapData.maps;
    codes := mapData.codes;
    elementsU := mapData.elementsU;
    autMap := [];

    for alpha in context.autGens do
        row := [];
        for f in maps do
            code := PG65_MapCodeFast(alpha^-1*f,
                                     context.gensS,elementsU);
            pos := Position(codes,code);
            if pos=fail then
                Error("Les morphismes ne sont pas fermes sous Aut(S)");
            fi;
            Add(row,pos);
        od;
        Add(autMap,row);
    od;

    normalizer := Normalizer(data.D8,U);
    normGens := GeneratorsOfGroup(normalizer);
    normMap := [];
    for g in normGens do
        beta := ConjugatorAutomorphism(U,g);
        row := [];
        for f in maps do
            code := PG65_MapCodeFast(f*beta,
                                     context.gensS,elementsU);
            pos := Position(codes,code);
            if pos=fail then
                Error("Les morphismes ne sont pas fermes sous N_D8(U)");
            fi;
            Add(row,pos);
        od;
        Add(normMap,row);
    od;

    return rec(
        autMap    := autMap,
        normMap   := normMap,
        normalizer:= normalizer,
        normGens  := normGens
    );
end;


# Identifiant direct du candidat (m,z,b), avec 1<=b<=6.
PG65_CandidateIdFast := function(m,z,b,numberZ)
    return ((m-1)*numberZ+(z-1))*6+b;
end;


PG65_CountImageFast := function(S,context,imageData,data)
    local start, U, mapData, maps, numberMaps, numberZ, denseSize,
          active, seen, candidateCount, m, z, b, id, actionTables,
          number, queue, head, tmp, m0, z0, b0, k, m2, z2, b2, id2,
          oneU;

    start := Runtime();
    U := imageData.U;
    numberZ := Length(context.centralV4s);

    if not context.valid or numberZ=0 then
        return rec(
            name:=imageData.name,
            imageOrder:=Size(U),
            action:="trivial",
            centralV4:=numberZ,
            quotientMaps:=0,
            orientedMaps:=0,
            candidates:=0,
            total:=0,
            runtimeMs:=Runtime()-start
        );
    fi;

    mapData := PG65_OrientedMapsFast(S,U,context.gensS);
    maps := mapData.maps;
    numberMaps := Length(maps);
    denseSize := numberMaps*numberZ*6;

    if numberMaps=0 then
        return rec(
            name:=imageData.name,
            imageOrder:=Size(U),
            action:="trivial",
            centralV4:=numberZ,
            quotientMaps:=Length(mapData.quotientMaps),
            orientedMaps:=0,
            candidates:=0,
            total:=0,
            runtimeMs:=Runtime()-start
        );
    fi;

    active := List([1..denseSize],x -> false);
    candidateCount := 0;
    oneU := One(U);

    for m in [1..numberMaps] do
        for z in [1..numberZ] do
            if ForAll(GeneratorsOfGroup(context.centralV4s[z]), x ->
                Image(maps[m],x)=oneU
            ) then
                for b in [1..6] do
                    id := PG65_CandidateIdFast(m,z,b,numberZ);
                    active[id] := true;
                    candidateCount := candidateCount+1;
                od;
            fi;
        od;
    od;

    if candidateCount=0 then
        return rec(
            name:=imageData.name,
            imageOrder:=Size(U),
            action:="trivial",
            centralV4:=numberZ,
            quotientMaps:=Length(mapData.quotientMaps),
            orientedMaps:=numberMaps,
            candidates:=0,
            total:=0,
            runtimeMs:=Runtime()-start
        );
    fi;

    actionTables := PG65_MapActionTablesFast(context,mapData,data,U);
    seen := List([1..denseSize],x -> false);
    number := 0;

    for id in [1..denseSize] do
        if active[id] and not seen[id] then
            number := number+1;
            queue := [id];
            seen[id] := true;
            head := 1;

            while head<=Length(queue) do
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
                    id2 := PG65_CandidateIdFast(m2,z2,b2,numberZ);
                    if not active[id2] then
                        Error("L'action de Aut(S) quitte les candidats admissibles");
                    fi;
                    if not seen[id2] then
                        seen[id2] := true;
                        Add(queue,id2);
                    fi;
                od;

                for k in [1..Length(actionTables.normGens)] do
                    m2 := actionTables.normMap[k][m0];
                    id2 := PG65_CandidateIdFast(m2,z0,b0,numberZ);
                    if not active[id2] then
                        Error("L'action de N_D8(U) quitte les candidats admissibles");
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
        name:=imageData.name,
        imageOrder:=Size(U),
        action:="trivial",
        centralV4:=numberZ,
        quotientMaps:=Length(mapData.quotientMaps),
        orientedMaps:=numberMaps,
        candidates:=candidateCount,
        total:=number,
        runtimeMs:=Runtime()-start
    );
end;


PG65_ForSWithDataFast := function(S,data)
    local start, context, classes, byImage, c, ans, total, n;

    start := Runtime();
    if Size(S) mod 4 <> 0 then
        return rec(byImage:=[],summary:=[],total:=0,totalClasses:=0,
                   runtimeMs:=Runtime()-start);
    fi;

    n := Size(S)/4;
    context := PG65_PrepareSContextFast(S);
    classes := Filtered(PG65_D8ImageClasses(data), c ->
        n mod Size(c.U)=0
    );
    byImage := [];
    total := 0;

    for c in classes do
        ans := PG65_CountImageFast(S,context,c,data);
        Add(byImage,ans);
        total := total+ans.total;
    od;

    return rec(
        byImage:=byImage,
        summary:=List(Filtered(byImage,x -> x.total<>0),
                      x -> [x.name,x.total]),
        total:=total,
        totalClasses:=total,
        runtimeMs:=Runtime()-start
    );
end;


# Redefinition des fonctions publiques : elles utilisent maintenant le moteur
# indexe et partagent les calculs couteux entre toutes les images U.
ZPhiClasses_PG65_D8_ForS_Image := function(S,imageData)
    local data, context;
    data := PG65_D8TrivialActionData();
    context := PG65_PrepareSContextFast(S);
    return PG65_CountImageFast(S,context,imageData,data);
end;


ZPhiClasses_PG65_D8_ForS := function(S)
    return PG65_ForSWithDataFast(S,PG65_D8TrivialActionData());
end;


ZPhiClasses_PG65_D8_SmallGroup := function(n,i)
    local ans;
    ans := ZPhiClasses_PG65_D8_ForS(SmallGroup(4*n,i));
    return rec(
        smallGroup:=[4*n,i],
        byImage:=ans.byImage,
        summary:=ans.summary,
        total:=ans.total,
        totalClasses:=ans.total,
        runtimeMs:=ans.runtimeMs
    );
end;


ZPhiClasses_PG65_D8_AllS_FromTo := function(n,first,last)
    local start, numberGroups, data, classes, totals, summary, total,
          i, ans, j;

    start := Runtime();
    numberGroups := NumberSmallGroups(4*n);
    if first<1 or last<first or last>numberGroups then
        Error("Plage SmallGroups invalide");
    fi;

    data := PG65_D8TrivialActionData();
    classes := Filtered(PG65_D8ImageClasses(data), c ->
        n mod Size(c.U)=0
    );
    totals := List(classes,c -> 0);
    summary := [];
    total := 0;

    for i in [first..last] do
        ans := PG65_ForSWithDataFast(SmallGroup(4*n,i),data);
        if ans.total<>0 then
            Add(summary,[i,ans.total]);
            total := total+ans.total;
        fi;
        for j in [1..Length(ans.byImage)] do
            totals[j] := totals[j]+ans.byImage[j].total;
        od;
    od;

    return rec(
        orderR:=n,
        orderS:=4*n,
        range:=[first,last],
        groupsTested:=last-first+1,
        contributingGroups:=Length(summary),
        byImageTotals:=List([1..Length(classes)], j ->
            [classes[j].name,totals[j]]
        ),
        summary:=summary,
        total:=total,
        totalClasses:=total,
        runtimeMs:=Runtime()-start
    );
end;


ZPhiClasses_PG65_D8_AllS := function(n)
    return ZPhiClasses_PG65_D8_AllS_FromTo(
        n,1,NumberSmallGroups(4*n)
    );
end;


ZPhiClasses_PG65_D8_C2Images_AllS := function(n)
    local ans, wanted;
    ans := ZPhiClasses_PG65_D8_AllS(n);
    wanted := Filtered(ans.byImageTotals,x ->
        x[1]="C2_r2" or x[1]="C2_s" or x[1]="C2_rs"
    );
    return rec(
        orderR:=n,
        byImageTotals:=wanted,
        total:=Sum(wanted,x -> x[2]),
        totalClasses:=Sum(wanted,x -> x[2]),
        runtimeMs:=ans.runtimeMs
    );
end;


# La version "image D8" utilise elle aussi le moteur rapide.
ZPhiClasses_PG65_D8_FullImage_ForS := function(S)
    local data, context, imageData;
    data := PG65_D8TrivialActionData();
    context := PG65_PrepareSContextFast(S);
    imageData := First(PG65_D8ImageClasses(data),c -> c.name="D8");
    return PG65_CountImageFast(S,context,imageData,data);
end;


ZPhiClasses_PG65_D8_FullImage_SmallGroup := function(n,i)
    local ans;
    if n mod 8 <> 0 then
        Error("Pour une image D8 surjective, |R| doit etre divisible par 8");
    fi;
    ans := ZPhiClasses_PG65_D8_FullImage_ForS(SmallGroup(4*n,i));
    return rec(
        smallGroup:=[4*n,i],
        summary:=rec(
            centralV4:=ans.centralV4,
            quotientMapsModuloAutD8:=ans.quotientMaps,
            orientedMaps:=ans.orientedMaps,
            admissibleCandidates:=ans.candidates
        ),
        total:=ans.total,
        totalClasses:=ans.total,
        runtimeMs:=ans.runtimeMs
    );
end;


ZPhiClasses_PG65_D8_FullImage_AllS_FromTo := function(n,first,last)
    local start, numberGroups, summary, total, i, ans;
    if n mod 8 <> 0 then
        Error("Pour une image D8 surjective, |R| doit etre divisible par 8");
    fi;
    numberGroups := NumberSmallGroups(4*n);
    if first<1 or last<first or last>numberGroups then
        Error("Plage SmallGroups invalide");
    fi;
    start := Runtime();
    summary := [];
    total := 0;
    for i in [first..last] do
        ans := ZPhiClasses_PG65_D8_FullImage_SmallGroup(n,i);
        if ans.total<>0 then
            Add(summary,[i,ans.total]);
            total := total+ans.total;
        fi;
    od;
    return rec(
        orderR:=n,
        orderS:=4*n,
        range:=[first,last],
        groupsTested:=last-first+1,
        contributingGroups:=Length(summary),
        summary:=summary,
        total:=total,
        totalClasses:=total,
        runtimeMs:=Runtime()-start
    );
end;


ZPhiClasses_PG65_D8_FullImage_AllS := function(n)
    return ZPhiClasses_PG65_D8_FullImage_AllS_FromTo(
        n,1,NumberSmallGroups(4*n)
    );
end;


# Alias renouveles apres les redefinitions rapides.
ZPhiClasses_V4_D8_Trivial_ForS := ZPhiClasses_PG65_D8_ForS;
ZPhiClasses_V4_D8_Trivial_SmallGroup :=
    ZPhiClasses_PG65_D8_SmallGroup;
ZPhiClasses_V4_D8_Trivial_AllS_FromTo :=
    ZPhiClasses_PG65_D8_AllS_FromTo;
ZPhiClasses_V4_D8_Trivial_AllS := ZPhiClasses_PG65_D8_AllS;
ZPhiClasses_V4_D8_Trivial_FullImage_ForS :=
    ZPhiClasses_PG65_D8_FullImage_ForS;
ZPhiClasses_V4_D8_Trivial_FullImage_SmallGroup :=
    ZPhiClasses_PG65_D8_FullImage_SmallGroup;
ZPhiClasses_V4_D8_Trivial_FullImage_AllS_FromTo :=
    ZPhiClasses_PG65_D8_FullImage_AllS_FromTo;
ZPhiClasses_V4_D8_Trivial_FullImage_AllS :=
    ZPhiClasses_PG65_D8_FullImage_AllS;
