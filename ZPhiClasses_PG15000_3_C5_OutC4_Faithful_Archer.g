#############################################################################
##
##  ZPhiClasses_PG15000_3_C5_OutC4_Faithful_Archer.g
##
##  GAP 4.15 script for the Schur cover
##
##      P = PerfectGroup(15000,3),
##      Z(P) ~= C5,
##      P/Z(P) ~= PerfectGroup(3000,1),
##      Out(P) ~= C4,
##      Out(P) -> Aut(Z(P)) ~= C4 is faithful and onto.
##
##  Claude Archer
##  Results for extensions of P of order up to 1 905 000 elements (127*|P|)
##  are stored in file
##  PG15000_3_Zphi_n2_n127_summary_Claude_Archer_E.csv
##
##  Usage + example :
##
##    Read("ZPhiClasses_PG15000_3_C5_OutC4_Faithful_Archer.g");
##    res := ZPhiClasses_PG15000_3_C5_OutC4_Faithful_AllS(8);;
##
##  The command above returns the exact number of extensions of
##  PerfectGroup(15000,3) by groups of order 8. Since |Z(P)| = 5 and
##  |Out(P)| = 4 are coprime, these extensions are classified by the
##  corresponding Zphi-classes.
##
##  Reference:
##    Claude Archer, "Classification of Group Extensions", PhD thesis,
##    2002; arXiv:2608.26491
##    https://arxiv.org/abs/2608.26491
##
##    
##
#############################################################################

PG15000C5_PositionSubgroup := function(list, H)
    local i;
    for i in [1..Length(list)] do
        if list[i] = H then
            return i;
        fi;
    od;
    return fail;
end;

PG15000C5_AddSubgroupIfNew := function(list, H)
    if PG15000C5_PositionSubgroup(list, H) = fail then
        Add(list, H);
    fi;
end;

PG15000C5_ZeroByImageRecord := function()
    return rec(order1 := 0, order2 := 0, order4 := 0);
end;

PG15000C5_AddByImage := function(r, imageOrder)
    if imageOrder = 1 then
        r.order1 := r.order1 + 1;
    elif imageOrder = 2 then
        r.order2 := r.order2 + 1;
    elif imageOrder = 4 then
        r.order4 := r.order4 + 1;
    else
        Error("PG15000C5: unexpected image order");
    fi;
end;

PG15000C5_NormalC5Subgroups := function(S)
    local subs, x, H;
    subs := [];
    for x in Elements(S) do
        if Order(x) = 5 then
            H := Subgroup(S, [x]);
            if IsNormal(S, H) then
                PG15000C5_AddSubgroupIfNew(subs, H);
            fi;
        fi;
    od;
    return subs;
end;

PG15000C5_AutOrbitsOnSubgroups := function(S, subs)
    local AutS, gens, actions, unused, orbits,
     H, orb, queue, K, alpha, L, pos;

    if Length(subs) = 0 then
        return [];
    fi;

    AutS := AutomorphismGroup(S);
    gens := GeneratorsOfGroup(AutS);
    actions := Concatenation(gens, List(gens, alpha -> alpha^-1));

    unused := ShallowCopy(subs);
    orbits := [];

    while Length(unused) > 0 do
        H := unused[1];
        orb := [H];
        queue := [H];
        Remove(unused, 1);

        while Length(queue) > 0 do
            K := queue[1];
            Remove(queue, 1);

            for alpha in actions do
                L := Image(alpha, K);

                if PG15000C5_PositionSubgroup(orb, L) = fail then
                    Add(orb, L);
                    Add(queue, L);

                    pos := PG15000C5_PositionSubgroup(unused, L);
                    if pos <> fail then
                        Remove(unused, pos);
                    fi;
                fi;
            od;
        od;

        Add(orbits, orb);
    od;

    return orbits;
end;

PG15000C5_ExponentOnC5Generator := function(a, b)
    local k;
    for k in [1..4] do
        if a^k = b then
            return k;
        fi;
    od;
    Error("PG15000C5: conjugate is not a power of the C5 generator");
end;

PG15000C5_MultOrderMod5Unit := function(k)
    if k mod 5 = 1 then
        return 1;
    elif k mod 5 = 4 then
        return 2;
    elif k mod 5 = 2 or k mod 5 = 3 then
        return 4;
    fi;
    Error("PG15000C5: non-unit exponent modulo 5");
end;

PG15000C5_ConjugationImageOrderOnC5 := function(S, A)
    local a, gensS, exps, s, b, k, orders;

    a := First(Elements(A), x -> Order(x) = 5);
    gensS := GeneratorsOfGroup(S);
    exps := [];

    for s in gensS do
        b := a^s;
        k := PG15000C5_ExponentOnC5Generator(a, b);
        AddSet(exps, k);
    od;

    orders := List(exps, k -> PG15000C5_MultOrderMod5Unit(k));
    return Lcm(orders);
end;

PG15000C5_SmallGroupCount := function(n, id)
    local S, subs, orbits, byImage, orb, imageOrder;

    S := SmallGroup(5*n, id);
    subs := PG15000C5_NormalC5Subgroups(S);

    if Length(subs) = 0 then
        return rec(
            normalC5Subgroups := 0,
            autOrbitsNormalC5 := 0,
            totalClasses := 0,
            byImage := PG15000C5_ZeroByImageRecord()
        );
    fi;

    orbits := PG15000C5_AutOrbitsOnSubgroups(S, subs);
    byImage := PG15000C5_ZeroByImageRecord();

    for orb in orbits do
        imageOrder := PG15000C5_ConjugationImageOrderOnC5(S, orb[1]);
        PG15000C5_AddByImage(byImage, imageOrder);
    od;

    return rec(
        normalC5Subgroups := Length(subs),
        autOrbitsNormalC5 := Length(orbits),
        totalClasses := Length(orbits),
        byImage := byImage
    );
end;

ZPhiClasses_PG15000_3_C5_OutC4_Faithful_AllS := function(n)
    local orderS, number, id, sr, byImage, totalClasses,
    normalC5Subgroups, autOrbitsNormalC5, t0, elapsed, r;

    orderS := 5*n;
    number := NumberSmallGroups(orderS);

    byImage := PG15000C5_ZeroByImageRecord();
    totalClasses := 0;
    normalC5Subgroups := 0;
    autOrbitsNormalC5 := 0;

    t0 := Runtime();

    for id in [1..number] do
        sr := PG15000C5_SmallGroupCount(n, id);

        normalC5Subgroups :=
            normalC5Subgroups + sr.normalC5Subgroups;
        autOrbitsNormalC5 :=
            autOrbitsNormalC5 + sr.autOrbitsNormalC5;
        totalClasses :=
            totalClasses + sr.totalClasses;

        byImage.order1 := byImage.order1 + sr.byImage.order1;
        byImage.order2 := byImage.order2 + sr.byImage.order2;
        byImage.order4 := byImage.order4 + sr.byImage.order4;
    od;

    elapsed := Runtime() - t0;

    r := rec(
        n := n,
        orderS := orderS,
        smallGroupsTested := number,
        normalC5Subgroups := normalC5Subgroups,
        autOrbitsNormalC5 := autOrbitsNormalC5,
        byImage := byImage,
        totalClasses := totalClasses,
        runtimeMs := elapsed
    );

    Print(
        "n=", r.n,
        " |S|=", r.orderS,
        " image1=", r.byImage.order1,
        " imageC2=", r.byImage.order2,
        " imageC4=", r.byImage.order4,
        " total=", r.totalClasses,
        " runtimeMs=", r.runtimeMs,
        "\n"
    );

    return r;
end;
