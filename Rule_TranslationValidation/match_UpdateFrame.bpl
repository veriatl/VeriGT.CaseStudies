procedure match_UpdateFrameTest() returns (res: Seq ref)
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_UpdateFrame($srcHeap)))==>	
!(  read($srcHeap,Seq#Index(Seq#Index(findPatterns_UpdateFrame($srcHeap),i),0),pacman$GameState.STATE) == 5
));
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_UpdateFrame($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
;
{
var $i: int;

var s#11: ref;
var rec#11: ref;
var pac#11: ref;
var recordNew#11: ref;

var P#11: Seq (Seq ref);
var b#11: bool;

var cursor: Seq ref;

		P#11 := findPatterns_UpdateFrame($srcHeap);	
		$i := 0;
		res := Seq#Empty();
		while($i < Seq#Length(P#11))
			invariant $i <= Seq#Length(P#11);
			invariant (forall i: int :: inRange(i,0,$i)==>	
		      !(read($srcHeap,Seq#Index(Seq#Index(P#11,i),0),pacman$GameState.STATE) == 5)
			);
		{

			cursor := Seq#Index(P#11, $i);
			
			s#11 := Seq#Index(cursor,0);
			rec#11 := Seq#Index(cursor,1);
			pac#11 := Seq#Index(cursor,2);


			// conditional filter
			call b#11 := match_filter_UpdateFrame(s#11,rec#11,pac#11);	
			
			// check filter and NAC;

			if(b#11){res := cursor; break;}
			$i := $i+1;
		}
}		

procedure match_filter_UpdateFrame(s:ref, rec:ref, pac:ref) returns(r: bool)
 requires s != null && read($srcHeap,s,alloc) && dtype(s) == pacman$GameState;
 requires rec != null && read($srcHeap,rec,alloc) && dtype(rec) == pacman$Record;
 requires pac != null && read($srcHeap,pac,alloc) && dtype(pac) == pacman$Pacman;
 requires read($srcHeap,s,pacman$GameState.record) == rec;
 ensures r <==> ( 
		read($srcHeap,s,pacman$GameState.STATE) == 5);
{
var s#11: ref;
var rec#11: ref;
var pac#11: ref;

var stk: Seq BoxType;

s#11,rec#11,pac#11 := s,rec,pac;
stk := OpCode#Aux#InitStk();

call stk := OpCode#Load(stk, s#11);

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