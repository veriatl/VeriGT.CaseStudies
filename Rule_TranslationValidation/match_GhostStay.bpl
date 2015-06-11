procedure match_GhostStayTest() returns (res: Seq ref)
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostStay($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),0),pacman$GameState.STATE) == 4
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),4),pacman$Action.DONEBY) == 2
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),4),pacman$Action.DIRECTION)==5)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_GhostStay($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 4
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DONEBY) == 2
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DIRECTION)==5
;
{
var $i: int;

var s#8: ref;
var rec#8: ref;
var ghost#8: ref;
var grid1#8: ref;
var act#8: ref;

var P#8: Seq (Seq ref);
var b#8: bool;

var cursor: Seq ref;


		P#8 := findPatterns_GhostStay($srcHeap);

		$i := 0;
		res := Seq#Empty();
		while($i < Seq#Length(P#8))
			invariant $i <= Seq#Length(P#8);
			invariant (forall i: int :: inRange(i,0,$i)==>	
		      !(read($srcHeap,Seq#Index(Seq#Index(P#8,i),0),pacman$GameState.STATE) == 4
			 && read($srcHeap,Seq#Index(Seq#Index(P#8,i),4),pacman$Action.DONEBY) == 2
			 && read($srcHeap,Seq#Index(Seq#Index(P#8,i),4),pacman$Action.FRAME) == 
					read($srcHeap, Seq#Index(Seq#Index(P#8,i),1), pacman$Record.FRAME)
			 && read($srcHeap,Seq#Index(Seq#Index(P#8,i),4),pacman$Action.DIRECTION)==5)
			);
		{

			cursor := Seq#Index(P#8, $i);
			
			s#8 := Seq#Index(cursor,0);
			rec#8 := Seq#Index(cursor,1);
			ghost#8 := Seq#Index(cursor,2);
			grid1#8 := Seq#Index(cursor,3);
			act#8 := Seq#Index(cursor,4);

			// conditional filter
			call b#8 := match_filter_GhostStay(s#8,rec#8,ghost#8,grid1#8,act#8);		
			
			// check filter and NAC;

			if(b#8){res := cursor; break;}
			$i := $i+1;
		}


}





procedure match_filter_GhostStay(s:ref, rec:ref, ghost:ref, grid1:ref, act:ref) returns(r: bool)
 requires s != null && read($srcHeap,s,alloc) && dtype(s) == pacman$GameState;
 requires rec != null && read($srcHeap,rec,alloc) && dtype(rec) == pacman$Record;
 requires ghost != null && read($srcHeap,ghost,alloc) && dtype(ghost) == pacman$Ghost;
 requires grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid;
 requires act != null && read($srcHeap,act,alloc) && dtype(act) == pacman$Action;
 requires read($srcHeap,s,pacman$GameState.record) == rec;
 requires read($srcHeap,grid1,pacman$Grid.hasEnemy) == ghost;
 ensures r <==> ( 
		read($srcHeap,s,pacman$GameState.STATE) == 4
	 && read($srcHeap,act,pacman$Action.DONEBY) == 2
	 && read($srcHeap,act,pacman$Action.FRAME) == read($srcHeap, rec, pacman$Record.FRAME)
	 && read($srcHeap,act,pacman$Action.DIRECTION)==5);
{

var s#8: ref;
var rec#8: ref;
var ghost#8: ref;
var grid1#8: ref;
var act#8: ref;
var stk: Seq BoxType;

var b#4: bool;
var b#11: bool;
var b#19: bool;

var b#4#Box: BoxType;
var b#11#Box: BoxType;
var b#19#Box: BoxType;

s#8,rec#8,ghost#8,grid1#8,act#8 := s, rec, ghost, grid1, act;

stk := OpCode#Aux#InitStk();

Label_0:
	 // 0: LOAD 0, 0 (s: P!GameState)
	call stk := OpCode#Load(stk, s#8);
	 // 1: GET (fieldname: STATE)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$STATE): Field (int)]));
	 // 2: PUSH (intValue: 4)
	call stk := OpCode#Pushi(stk, 4);
	 // 3: INVOKE (argcount: 1) (opname: =~)
	call stk := Native#OCLOperation#MatchingOperator
		(stk, 
		$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): int,
		$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): int);
	 // 4: IFN 10
	b#4 := $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
	if(!b#4){goto Label_10;}
	 // 5: LOAD 0, 5 (act: P!Action)
	call stk := OpCode#Load(stk, act#8);
	 // 6: GET (fieldname: DONEBY)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$DONEBY): Field (int)]));
	 // 7: PUSH (intValue: 2)
	call stk := OpCode#Pushi(stk, 2);
	 // 8: INVOKE (argcount: 1) (opname: =~)
	call stk := Native#OCLOperation#MatchingOperator
		(stk, 
		$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): int,
		$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): int);
	 // 9: GOTO 11
	goto Label_11;
Label_10:
	// 10: PUSHF
	call stk := OpCode#Pushf(stk);
Label_11:
	// 11: IFN 18
	b#11 := $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
	if(!b#11){goto Label_18;}
	// 12: LOAD 0, 5 (act: P!Action)
	call stk := OpCode#Load(stk, act#8);
	// 13: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 14: LOAD 0, 1 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#8);
	// 15: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 16: INVOKE (argcount: 1) (opname: =~)
	call stk := Native#OCLOperation#MatchingOperator
		(stk, 
		$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): int,
		$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): int);
	// 17: GOTO 19
	goto Label_19;
Label_18:
	// 18: PUSHF
	call stk := OpCode#Pushf(stk);
Label_19:
	// 19: IFN 25
	b#19 := $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
	if(!b#19){goto Label_25;}
	// 20: LOAD 0, 5 (act: P!Action)
	call stk := OpCode#Load(stk, act#8);
	// 21: GET (fieldname: DIRECTION)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$DIRECTION): Field (int)]));
	// 22: PUSH (intValue: 5)
	call stk := OpCode#Pushi(stk, 5);
	// 23: INVOKE (argcount: 1) (opname: =~)
	call stk := Native#OCLOperation#MatchingOperator
		(stk, 
		$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): int,
		$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): int);
	// 24: GOTO 26
	goto Label_26;
Label_25:
	// 25: PUSHF
	call stk := OpCode#Pushf(stk);
Label_26:
	r:= $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
}	 