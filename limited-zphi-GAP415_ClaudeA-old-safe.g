#############################################################################
##
#F  TwoFusions( sag )
##
## Zphi-limited method (Z(P)=2 and Out(P)=2) by Claude Archer
##  GAP 4.15+ optimized version 2026 ( Claude Archer)
##
##  Computes Aut(sag)-orbits on:
##    - normal subgroups Z of order 2;
##    - normal subgroups K of index 2;
##    - pairs [Z,K] with Z <= K.
##
##  Return format:
##      [ "fusz2", fusz2, "fusind2", fusind2, "fuspair", fuspair ]
##
##  Optimisations in this version:
##    1.  No call to NormalSubgroups(sag) in the main computation.
##    2.  Normal subgroups of order 2 are found via CentralInvolutions(sag).
##    3.  If sag is a 2-group, index-2 subgroups are found via MaximalSubgroups(sag),
##        because all maximals of a 2-group have index 2 and are normal.
##    4.  If sag is not a 2-group, index-2 subgroups are found as kernels of
##        epimorphisms sag -> C2 using GQuotients(sag,CyclicGroup(2)).
##    5.  The orbit computation still uses the structural action by Image(alpha,U),
##        not a permutation action on the elements of sag.  This keeps memory use low.
##
#############################################################################
#############################################################################
## CentralInvolutions(G)
##
## Return the non-trivial elements of Omega_1(Z(G)), i.e. the central
## involutions of G.
##
## For a 2-group, Omega_1(Z(G)) is an elementary abelian 2-group.  Its
## non-identity elements are exactly the central elements of order 2.
#############################################################################
CentralInvolutions := function(G)
    local one;

    one := One(G);

    return Filtered(Elements(Centre(G)),
                    z -> z <> one and z^2 = one);
end;

#############################################################################

LoadPackage( "polycyclic" );

#############################################################################
## Auxiliaries
#############################################################################

TwoFusions_IsPowerOfTwoInt := function( n )
    if n < 1 then
        return false;
    fi;

    while n mod 2 = 0 do
        n := QuoInt( n, 2 );
    od;

    return n = 1;
end;

TwoFusions_AddIfNewByEquality := function( list, obj )
    if not ForAny( list, x -> x = obj ) then
        Add( list, obj );
    fi;
end;

TwoFusions_NormalOrder2Subgroups := function( G )
    # Any normal subgroup of order 2 is minimal normal.
    # Conversely, a minimal normal subgroup of size 2 is exactly such a subgroup.
    #return Filtered( MinimalNormalSubgroups( G ), N -> Size( N ) = 2 );
	return CentralInvolutions(G);
end;

TwoFusions_NormalIndex2Subgroups := function( G )
    local epis, out, epi, K, maxs, M;

    if TwoFusions_IsPowerOfTwoInt( Size( G ) ) then
        # In a 2-group, every maximal subgroup has index 2 and is normal.
        return MaximalSubgroups( G );
    fi;

    # In an arbitrary finite group, subgroups of index 2 are exactly kernels
    # of epimorphisms onto C2.  This avoids computing all maximal subgroups.
    epis := GQuotients( G, CyclicGroup( 2 ) );
    out := [];

    if epis <> fail then
        for epi in epis do
            K := Kernel( epi );
            if Size( K ) * 2 = Size( G ) then
                TwoFusions_AddIfNewByEquality( out, K );
            fi;
        od;
        return out;
    fi;

    # Safety fallback for group types where GQuotients is not available.
    # We still avoid NormalSubgroups(G): we only filter maximal subgroups.
    maxs := MaximalSubgroups( G );
    for M in maxs do
        if Size( M ) * 2 = Size( G ) then
            TwoFusions_AddIfNewByEquality( out, M );
        fi;
    od;

    return out;
end;

#############################################################################
## Main function
#############################################################################

TwoFusions := function( sag )
    local size, syl2, comps, c,
          aut, norm_2, norm_ind2, pairs, i, j,z,K,
          fusz2, fusind2, fuspair;

    size := Size( sag );
	
	#########################################################################
    ## Elementary abelian 2-groups.
    ##
    ## If sag is elementary abelian of order 2^d, then Aut(sag)=GL(d,2).
    ## This group is transitive on:
    ##   - non-zero vectors of sag;
    ##   - hyperplanes of sag;
    ##   - incident pairs (z,K) with z in K.
    ##
    ## Therefore fusz2 = fusind2 = fuspair = 1, and there is no need to
    ## construct Aut(sag), which would be the large GL(d,2).
    #########################################################################
    if TwoFusions_IsPowerOfTwoInt( size ) and size > 2
       and IsElementaryAbelian( sag ) then
        return [ "fusz2", 1, "fusind2", 1, "fuspair", 1 ];
    fi;
	
	#########################################################################
    ## 1. Odd order: no subgroup of order 2 and no subgroup of index 2.
    #########################################################################
    if size mod 2 = 1 then
        return [ "fusz2", 0, "fusind2", 0, "fuspair", 0 ];
    fi;

    syl2 := SylowSubgroup( sag, 2 );

    #########################################################################
    ## 2. Case |Sylow_2| = 2, i.e. |sag| = 2*m with m odd.
    ##    This keeps the logic of the earlier optimized version.
    #########################################################################
    if ( QuoInt( size, 2 ) mod 2 ) = 1 then
        if IsNormal( sag, syl2 ) then
            return [ "fusz2", 1, "fusind2", 1, "fuspair", 0 ];
        else
            return [ "fusz2", 0, "fusind2", 1, "fuspair", 0 ];
        fi;
    fi;

    #########################################################################
    ## 3. Reduction to the Sylow 2-subgroup when there is a normal odd
    ##    complement.  Then sag is a direct product of its Sylow 2-subgroup
    ##    and an odd normal complement, so all 2-data come from the Sylow 2 part.
    #########################################################################
    if IsNormal( sag, syl2 ) then
        comps := ComplementClassesRepresentatives( sag, syl2 );
        if comps <> fail and Length( comps ) > 0 then
            if ForAny( comps, c -> IsNormal( sag, c ) ) then
                sag := syl2;
            fi;
        fi;
    fi;

    #########################################################################
    ## 4. Targeted subgroup extraction.
    ##
    ##    No NormalSubgroups(sag) here.
    #########################################################################
    norm_2 := TwoFusions_NormalOrder2Subgroups( sag );
    norm_ind2 := TwoFusions_NormalIndex2Subgroups( sag );

    aut := AutomorphismGroup( sag );

    #########################################################################
    ## 5. Orbit calculations by structural action Image(alpha,U).
    ##
    ##    This is deliberately not an action on Elements(sag).  It keeps the
    ##    method much lighter in memory.
    #########################################################################
    #fusz2 := Length( Orbits( aut, norm_2, function( U, alpha )
    #    return Image( alpha, U );
    #end ) );
	
	#########################################################################
## 5. Orbit calculations by structural action.
##
##    Here norm_2 is now a list of central involutions z, not subgroups <z>.
##    This remains equivalent to counting central subgroups of order 2,
##    since z <-> <z> is bijective for involutions.
#########################################################################

	fusz2 := Length( Orbits( aut, norm_2, function( z, alpha )
		return Image( alpha, z );
	end ) );

    fusind2 := Length( Orbits( aut, norm_ind2, function( U, alpha )
        return Image( alpha, U );
    end ) );

    #########################################################################
    ## 6. Pairs [Z,K] with |Z|=2, [sag:K]=2 and Z <= K.
	## is now replaced by CentralInvolutions z (z^2=1) z in K
    #########################################################################
    #pairs := [];
    #for i in [ 1 .. Length( norm_ind2 ) ] do
    #    for j in [ 1 .. Length( norm_2 ) ] do
    #        if IsSubset( norm_ind2[i], norm_2[j] ) then
    #            Add( pairs, [ norm_2[j], norm_ind2[i] ] );
    #        fi;
    #    od;
    #od;
	
	################################""
	pairs := [];
	for z in norm_2 do
    for K in norm_ind2 do
        if z in K then
            Add( pairs, [ z, K ] );
        fi;
    od;
od;
#########################
#########################

    fuspair := Length( Orbits( aut, pairs, function( pair, alpha )
        return [ Image( alpha, pair[1] ), Image( alpha, pair[2] ) ];
    end ) );

    return [ "fusz2", fusz2, "fusind2", fusind2, "fuspair", fuspair ];
end;

SumTwoFusionsForOrder_FromTo := function( n, start_index, end_index )

    local nr, i, G, data, fusz2, fusind2, fuspair,
          totalFusz2, totalFusind2, totalFuspair,
          filename, line, t0, t1;

    #########################################################################
    ## Check the SmallGroups range.
    #########################################################################

    nr := NumberSmallGroups(n);

    if not IsInt(start_index) or not IsInt(end_index) then
        Error("start_index and end_index must be integers");
    fi;

    if start_index < 1 then
        Error("start_index must be at least 1");
    fi;

    if end_index > nr then
        Error("end_index is larger than NumberSmallGroups(n)");
    fi;

    if start_index > end_index then
        Error("start_index must be less than or equal to end_index");
    fi;


    #########################################################################
    ## Output filename.
    ##
    ## Each run creates a small precomputed table containing only the three
    ## orbit counts fusz2, fusind2 and fuspair for each SmallGroup(n,i) in
    ## the selected range.
    #########################################################################

    filename := Concatenation(
        "results_optimal_twofusions_order_",
        String(n),
        "_from_",
        String(start_index),
        "_to_",
        String(end_index),
        ".txt"
    );

    PrintTo(
        filename,
        Concatenation(
            "# TwoFusions results for SmallGroups of order ",
            String(n),
            "\n"
        )
    );

    AppendTo(
        filename,
        Concatenation(
            "# Range: SmallGroup(",
            String(n),
            ",",
            String(start_index),
            ") to SmallGroup(",
            String(n),
            ",",
            String(end_index),
            ")\n"
        )
    );

    AppendTo(
        filename,
        Concatenation(
            "# Total number of groups of order ",
            String(n),
            " = ",
            String(nr),
            "\n\n"
        )
    );

    AppendTo(
        filename,
        "# Format: IdSmallGroup(G) ; fusz2 ; fusind2 ; fuspair\n\n"
    );

    #########################################################################
    ## Initialize totals.
    #########################################################################

    totalFusz2 := 0;
    totalFusind2 := 0;
    totalFuspair := 0;

    t0 := Runtime();

    #########################################################################
    ## Main loop over SmallGroup(n,i).
    #########################################################################

    for i in [start_index .. end_index] do

        G := SmallGroup(n, i);

        data := TwoFusions(G);

        #####################################################################
        ## TwoFusions returns:
        ##
        ##     [ "fusz2", fusz2, "fusind2", fusind2, "fuspair", fuspair ]
        #####################################################################

        fusz2 := data[2];
        fusind2 := data[4];
        fuspair := data[6];

        totalFusz2 := totalFusz2 + fusz2;
        totalFusind2 := totalFusind2 + fusind2;
        totalFuspair := totalFuspair + fuspair;

        line := Concatenation(
            "IdSmallGroup(G) = ",
            String(IdSmallGroup(G)),
            " ; fusz2 = ",
            String(fusz2),
            " ; fusind2 = ",
            String(fusind2),
            " ; fuspair = ",
            String(fuspair),
            "\n"
        );

        #####################################################################
        ## Write immediately after each group.
        #####################################################################

        AppendTo(filename, line);

        #####################################################################
        ## Release references to the current group and its computed data.
        ## The large objects created inside TwoFusions, such as Aut(G),
        ## Aut(G), CentralInvolutions(G), MaximalSubgroups/GQuotients,
        ## are local to TwoFusions and become collectible after it returns.
        ##
        ## We still clear the references held in this loop, and every 500
        ## groups we explicitly ask GAP's garbage collector to run.
        #####################################################################

        G := fail;
        data := fail;

        if i mod 500 = 0 then
            GASMAN("collect");
        fi;

    od;

    t1 := Runtime();

    #########################################################################
    ## Final summary.
    #########################################################################

    AppendTo(filename, "\n");
    AppendTo(filename, "Summary for this range\n");

    AppendTo(
        filename,
        Concatenation(
            "Total fusz2 = ",
            String(totalFusz2),
            "\n"
        )
    );

    AppendTo(
        filename,
        Concatenation(
            "Total fusind2 = ",
            String(totalFusind2),
            "\n"
        )
    );

    AppendTo(
        filename,
        Concatenation(
            "Total fuspair = ",
            String(totalFuspair),
            "\n"
        )
    );

    AppendTo(
        filename,
        Concatenation(
            "CPU time in seconds = ",
            String(Float((t1-t0)/1000)),
            "\n"
        )
    );

    Print("\nFinished order ", n, " from index ", start_index, " to ", end_index, ".\n");
    Print("Total number of groups of order ", n, " = ", nr, "\n");
    Print("Total fusz2 = ", totalFusz2, "\n");
    Print("Total fusind2 = ", totalFusind2, "\n");
    Print("Total fuspair = ", totalFuspair, "\n");
    Print("CPU time in seconds = ", Float((t1-t0)/1000), "\n");
    Print("Results written to file: ", filename, "\n");

    return rec(
        order := n,
        numberGroups := nr,
        startIndex := start_index,
        endIndex := end_index,
        totalFusz2 := totalFusz2,
        totalFusind2 := totalFusind2,
        totalFuspair := totalFuspair,
        filename := filename,
        cpuTimeSeconds := Float((t1-t0)/1000)
    );

end;


#############################################################################
##
#F  SumTwoFusionsForOrder_From( n, start_index )
##
##  Continue the computation from SmallGroup(n,start_index) to the last
##  SmallGroup of order n.
##
##  Example:
##
##      SumTwoFusionsForOrder_From(512, 74580);
##
#############################################################################

SumTwoFusionsForOrder_From := function( n, start_index )

    return SumTwoFusionsForOrder_FromTo(
        n,
        start_index,
        NumberSmallGroups(n)
    );

end;


#############################################################################
##
#F  SumTwoFusionsForOrder( n )
##
##  Compute and sum TwoFusions(G) for all SmallGroups of order n.
##
##  Example:
##
##      SumTwoFusionsForOrder(32);
##
#############################################################################

SumTwoFusionsForOrder := function( n )

    return SumTwoFusionsForOrder_FromTo(
        n,
        1,
        NumberSmallGroups(n)
    );

end;



#############################################################################
##
# End of file.
##
## Use:
##     TwoFusions( G );
##     SumTwoFusionsForOrder( n );
##     SumTwoFusionsForOrder_FromTo( n, start_index, end_index );
##
#############################################################################

## Usage Documentation : case study 
## Counting up to isomorphism all insoluble groups of order 1920
##
#############################################################################
##
#F  SumTwoFusionsForOrder( n )
##
##  Compute and sum TwoFusions(G) for all SmallGroups of order n.
##
##  Example:
##
##      SumTwoFusionsForOrder(32);
##
##  The output should look like this:
##
##      Finished order 32 from index 1 to 51.
##      Total number of groups of order 32 = 51
##      Total fusz2 = 95
##      Total fusind2 = 144
##      Total fuspair = 286
##      CPU time in seconds = 9.141
##      Results written to file: results_optimal_twofusions_order_32_from_1_to_51.txt
##      rec( cpuTimeSeconds := 9.141, endIndex := 51,
##        filename := "results_optimal_twofusions_order_32_from_1_to_51.txt",
##        numberGroups := 51, order := 32, startIndex := 1,
##        totalFusind2 := 144, totalFuspair := 286, totalFusz2 := 95 )
##
##  Application example: nonsolvable groups of order 1920 = 60 * 32.
##
##  Suppose that we want to count the nonsolvable groups of order 1920
##  which are extensions of AlternatingGroup(5) or of SL(2,5) by a solvable
##  group.  The command SumTwoFusionsForOrder(32) gives the three numbers
##  needed for the part controlled by groups of order 32.
##
##  There are 51 direct products A5 x R, one for each group R of order 32.
##  In addition, fusz2 = 95 counts the other extensions of A5 obtained from
##  central involutions, fusind2 = 144 counts central products of SL(2,5)
##  with groups of order 32, and fuspair = 286 counts the remaining extensions
##  of SL(2,5) by groups of order 16 arising from incident pairs (Z,K).
##
##  Thus this part gives
##
##      51 + 95 + 144 + 286 = 576
##
##  nonsolvable groups of order 1920 which are extensions of A5 or SL(2,5).
##
##  There are only 12 further nonsolvable groups of order 1920.  They come from
##  the perfect groups themselves: there are 7 perfect groups of order 1920,
##  and 2 perfect groups P of order 960.  The latter give 2 direct products 
##  P x 2 and 3 additional
##  extensions by a group of order 2, computed with ExtensionsByGroupNoCentre
##  from the GAP package grpconst.
##
##  Therefore about 10 seconds of computation are enough to recover all
##  588 nonsolvable groups of order 1920 stored in the SmallGroups library, up to
##  isomorphism.
##
#############################################################################

######################################""""
## Precomputed Tables :
#############################################################################
##
#F  SumTwoFusionsForOrder_FromTo( n, start_index, end_index )
##
##  Compute TwoFusions(G) for all SmallGroups G = SmallGroup(n,i), with
##  start_index <= i <= end_index, and write the three numerical invariants
##
##      fusz2, fusind2, fuspair
##
##  to a text file.
##
##  The output file is deliberately a very small precomputed table.  It does
##  not store the groups themselves, nor their automorphism groups, nor the
##  actual orbits.  It only stores, for each SmallGroup identifier [n,i], the
##  three orbit counts needed later for the enumeration of nonsolvable
##  extensions involving A5 and SL(2,5) or any group P whose extensions 
##  can be counted up to isomorphisms by the Zphi-method for Out(P)=2 and
##  the centre Z(P) is of order 2 or 1.
##
##
##  The file name has the form
##
##      results_optimal_twofusions_order_<n>_from_<start>_to_<end>.txt
##
##  For example,
##
##      SumTwoFusionsForOrder_FromTo(256,1,20000);
##
##  creates a file named
##
##      results_optimal_twofusions_order_256_from_1_to_20000.txt
##
##  whose lines have the format
##
##      IdSmallGroup(G) = [ 256, i ] ; fusz2 = a ; fusind2 = b ; fuspair = c
##
##  These files can be regarded as precomputed tables of the local contribution
##  of each solvable group S of order n to the nonsolvable extension count.