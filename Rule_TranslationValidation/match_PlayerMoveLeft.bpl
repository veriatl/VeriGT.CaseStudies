procedure match_PlayerMoveLeft() returns (res: Seq ref)
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),0),pacman$GameState.STATE) == 3
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.DONEBY) == 1
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.DIRECTION)==1)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_PlayerMoveLeft($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 3
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DONEBY) == 1
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DIRECTION)==1
;
{
var $i: int;

var s#0: ref;
var rec#0: ref;
var pac#0: ref;
var grid1#0: ref;
var grid2#0: ref;
var act#0: ref;

var P#0: Seq (Seq ref);
var b#0: bool;

var cursor: Seq ref;


		P#0 := findPatterns_PlayerMoveLeft($srcHeap);

		$i := 0;
		res := Seq#Empty();
		while($i < Seq#Length(P#0))
			invariant $i <= Seq#Length(P#0);
			invariant (forall i: int :: inRange(i,0,$i)==>	
		      !(read($srcHeap,Seq#Index(Seq#Index(P#0,i),0),pacman$GameState.STATE) == 3
			 && read($srcHeap,Seq#Index(Seq#Index(P#0,i),5),pacman$Action.DONEBY) == 1
			 && read($srcHeap,Seq#Index(Seq#Index(P#0,i),5),pacman$Action.FRAME) == 
					read($srcHeap, Seq#Index(Seq#Index(P#0,i),1), pacman$Record.FRAME)
			 && read($srcHeap,Seq#Index(Seq#Index(P#0,i),5),pacman$Action.DIRECTION)==1)
			);
		{

			cursor := Seq#Index(P#0, $i);
			
			s#0 := Seq#Index(cursor,0);
			rec#0 := Seq#Index(cursor,1);
			pac#0 := Seq#Index(cursor,2);
			grid2#0 := Seq#Index(cursor,3);
			grid1#0 := Seq#Index(cursor,4);
			act#0 := Seq#Index(cursor,5);

			// conditional filter
			call b#0 := match_filter_PlayerMoveLeft(s#0,rec#0,pac#0,grid2#0,grid1#0,act#0);	
			
			// check filter and NAC;

			if(b#0){res := cursor; break;}
			$i := $i+1;
		}


}





procedure match_filter_PlayerMoveLeft(s:ref, rec:ref, pac:ref, grid2:ref, grid1:ref, act:ref) returns(r: bool);
 requires s != null && read($srcHeap,s,alloc) && dtype(s) == pacman$GameState;
 requires rec != null && read($srcHeap,rec,alloc) && dtype(rec) == pacman$Record;
 requires pac != null && read($srcHeap,pac,alloc) && dtype(pac) == pacman$Pacman;
 requires grid2 != null && read($srcHeap,grid2,alloc) && dtype(grid2) == pacman$Grid;
 requires grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid;
 requires act != null && read($srcHeap,act,alloc) && dtype(act) == pacman$Action;
 requires grid1!=grid2;
 requires read($srcHeap,s,pacman$GameState.record) == rec;
 requires read($srcHeap,grid1,pacman$Grid.hasPlayer) == pac;
 requires read($srcHeap,grid1,pacman$Grid.left) == grid2;
 ensures r <==> ( 
		read($srcHeap,s,pacman$GameState.STATE) == 3
	 && read($srcHeap,act,pacman$Action.DONEBY) == 1
	 && read($srcHeap,act,pacman$Action.FRAME) == read($srcHeap, rec, pacman$Record.FRAME)
	 && read($srcHeap,act,pacman$Action.DIRECTION)==1);
	 

