procedure match_GhostMoveLeft() returns (res: Seq ref)
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),0),pacman$GameState.STATE) == 4
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),5),pacman$Action.DONEBY) == 2
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),5),pacman$Action.DIRECTION)==1)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_GhostMoveLeft($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 4
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DONEBY) == 2
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DIRECTION)==1
;
{
var $i: int;

var s#5: ref;
var rec#5: ref;
var ghost#5: ref;
var grid1#5: ref;
var grid2#5: ref;
var act#5: ref;

var P#5: Seq (Seq ref);
var b#5: bool;

var cursor: Seq ref;


		P#5 := findPatterns_GhostMoveLeft($srcHeap);

		$i := 0;
		res := Seq#Empty();
		while($i < Seq#Length(P#5))
			invariant $i <= Seq#Length(P#5);
			invariant (forall i: int :: inRange(i,0,$i)==>	
		      !(read($srcHeap,Seq#Index(Seq#Index(P#5,i),0),pacman$GameState.STATE) == 4
			 && read($srcHeap,Seq#Index(Seq#Index(P#5,i),5),pacman$Action.DONEBY) == 2
			 && read($srcHeap,Seq#Index(Seq#Index(P#5,i),5),pacman$Action.FRAME) == 
					read($srcHeap, Seq#Index(Seq#Index(P#5,i),1), pacman$Record.FRAME)
			 && read($srcHeap,Seq#Index(Seq#Index(P#5,i),5),pacman$Action.DIRECTION)==1)
			);
		{

			cursor := Seq#Index(P#5, $i);
			
			s#5 := Seq#Index(cursor,0);
			rec#5 := Seq#Index(cursor,1);
			ghost#5 := Seq#Index(cursor,2);
			grid2#5 := Seq#Index(cursor,3);
			grid1#5 := Seq#Index(cursor,4);
			act#5 := Seq#Index(cursor,5);

			// conditional filter
			call b#5 := match_filter_GhostMoveLeft(s#5,rec#5,ghost#5,grid2#5,grid1#5,act#5);		
			
			// check filter and NAC;

			if(b#5){res := cursor; break;}
			$i := $i+1;
		}


}





procedure match_filter_GhostMoveLeft(s:ref, rec:ref, ghost:ref, grid2:ref, grid1:ref, act:ref) returns(r: bool);
 requires s != null && read($srcHeap,s,alloc) && dtype(s) == pacman$GameState;
 requires rec != null && read($srcHeap,rec,alloc) && dtype(rec) == pacman$Record;
 requires ghost != null && read($srcHeap,ghost,alloc) && dtype(ghost) == pacman$Ghost;
 requires grid2 != null && read($srcHeap,grid2,alloc) && dtype(grid2) == pacman$Grid;
 requires grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid;
 requires act != null && read($srcHeap,act,alloc) && dtype(act) == pacman$Action;
 requires grid1!=grid2;
 requires read($srcHeap,s,pacman$GameState.record) == rec;
 requires read($srcHeap,grid1,pacman$Grid.hasEnemy) == ghost;
 requires read($srcHeap,grid1,pacman$Grid.left) == grid2;
 ensures r <==> ( 
		read($srcHeap,s,pacman$GameState.STATE) == 4
	 && read($srcHeap,act,pacman$Action.DONEBY) == 2
	 && read($srcHeap,act,pacman$Action.FRAME) == read($srcHeap, rec, pacman$Record.FRAME)
	 && read($srcHeap,act,pacman$Action.DIRECTION)==1);
	 
	 

	
