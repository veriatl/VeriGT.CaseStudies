procedure match_KillTest() returns (res: Seq ref)
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill($srcHeap)))==>	
!(  read($srcHeap,Seq#Index(Seq#Index(findPatterns_Kill($srcHeap),i),0),pacman$GameState.STATE) == 5
));
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_Kill($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
;

{
var $i: int;

var s#10: ref;
var ghost#10: ref;
var pac#10: ref;
var grid#10: ref;

var P#10: Seq (Seq ref);
var b#10: bool;

var cursor: Seq ref;

		P#10 := findPatterns_Kill($srcHeap);
		$i := 0;
		res := Seq#Empty();
		

		while($i < Seq#Length(P#10))
			invariant $i <= Seq#Length(P#10);
			invariant (forall i: int :: inRange(i,0,$i)==>	
		      !(read($srcHeap,Seq#Index(Seq#Index(P#10,i),0),pacman$GameState.STATE) == 5)
			);
		{

			cursor := Seq#Index(P#10, $i);
			
			s#10 := Seq#Index(cursor,0);
			ghost#10 := Seq#Index(cursor,1);
			pac#10 := Seq#Index(cursor,2);
			grid#10 := Seq#Index(cursor,3);


			// conditional filter
			call b#10 := match_filter_Kill(s#10,ghost#10,pac#10,grid#10);	
			
			// check filter and NAC;

			if(b#10){res := cursor; break;}
			$i := $i+1;
		}
}

procedure match_filter_Kill(s:ref, ghost:ref, pac:ref, grid:ref) returns(r: bool)
 requires s != null && read($srcHeap,s,alloc) && dtype(s) == pacman$GameState;
 requires ghost != null && read($srcHeap,ghost,alloc) && dtype(ghost) == pacman$Ghost;
 requires pac != null && read($srcHeap,pac,alloc) && dtype(pac) == pacman$Pacman;
 requires grid != null && read($srcHeap,grid,alloc) && dtype(grid) == pacman$Grid;
 requires read($srcHeap,grid,pacman$Grid.hasPlayer) == pac;
 requires read($srcHeap,grid,pacman$Grid.hasEnemy) == ghost;
 ensures r <==> ( 
		read($srcHeap,s,pacman$GameState.STATE) == 5);
{
var s#10: ref;
var ghost#10: ref;
var pac#10: ref;
var grid#10: ref;

var stk: Seq BoxType;

s#10,ghost#10,pac#10,grid#10 := s,ghost,pac,grid;

stk := OpCode#Aux#InitStk();

call stk := OpCode#Load(stk, s#10);

// get GameState.State
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$STATE): Field (int)]));

// push 5
call stk := OpCode#Pushi(stk, 5);

// invoke =~
call stk := Native#OCLOperation#MatchingOperator
	(stk, 
	$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): int,
	$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): int);

r:= $Unbox(OpCode#Top(stk));
call stk := OpCode#Pop(stk);

}