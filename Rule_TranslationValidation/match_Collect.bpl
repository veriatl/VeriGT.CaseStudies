procedure match_Collect() returns (res: Seq ref)
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect($srcHeap)))==>	
!(  read($srcHeap,Seq#Index(Seq#Index(findPatterns_Collect($srcHeap),i),0),pacman$GameState.STATE) == 5
));
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_Collect($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
;

{
var $i: int;

var s#9: ref;
var rec#9: ref;
var pac#9: ref;
var gem#9: ref;
var grid#9: ref;
var recordNew#9: ref;

var P#9: Seq (Seq ref);
var b#9: bool;

var cursor: Seq ref;

		P#9 := findPatterns_Collect($srcHeap);
		$i := 0;
		res := Seq#Empty();
		while($i < Seq#Length(P#9))
			invariant $i <= Seq#Length(P#9);
			invariant (forall i: int :: inRange(i,0,$i)==>	
		      !(read($srcHeap,Seq#Index(Seq#Index(P#9,i),0),pacman$GameState.STATE) == 5)
			);
		{

			cursor := Seq#Index(P#9, $i);
			
			s#9 := Seq#Index(cursor,0);
			rec#9 := Seq#Index(cursor,1);
			pac#9 := Seq#Index(cursor,2);
			gem#9 := Seq#Index(cursor,3);
			grid#9 := Seq#Index(cursor,4);


			// conditional filter
			call b#9 := match_filter_Collect(s#9,rec#9,pac#9,gem#9,grid#9);	
			
			// check filter and NAC;

			if(b#9){res := cursor; break;}
			$i := $i+1;
		}

}


procedure match_filter_Collect(s:ref, rec:ref, pac:ref, gem:ref, grid:ref) returns(r: bool);
 requires s != null && read($srcHeap,s,alloc) && dtype(s) == pacman$GameState;
 requires rec != null && read($srcHeap,rec,alloc) && dtype(rec) == pacman$Record;
 requires pac != null && read($srcHeap,pac,alloc) && dtype(pac) == pacman$Pacman;
 requires gem != null && read($srcHeap,gem,alloc) && dtype(gem) == pacman$Gem;
 requires grid != null && read($srcHeap,grid,alloc) && dtype(grid) == pacman$Grid;
 requires read($srcHeap,s,pacman$GameState.record) == rec;
 requires read($srcHeap,grid,pacman$Grid.hasPlayer) == pac;
 requires read($srcHeap,grid,pacman$Grid.hasGem) == gem;
 ensures r <==> ( 
		read($srcHeap,s,pacman$GameState.STATE) == 5);
		


