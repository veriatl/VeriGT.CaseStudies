procedure match_GhostMoveLeftTest() returns (res: Seq ref)
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





procedure match_filter_GhostMoveLeft(s:ref, rec:ref, ghost:ref, grid2:ref, grid1:ref, act:ref) returns(r: bool)
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
{

var s#5: ref;
var rec#5: ref;
var ghost#5: ref;
var grid1#5: ref;
var grid2#5: ref;
var act#5: ref;
var stk: Seq BoxType;

var b#4: bool;
var b#11: bool;
var b#19: bool;

var b#4#Box: BoxType;
var b#11#Box: BoxType;
var b#19#Box: BoxType;

s#5,rec#5,ghost#5,grid2#5,grid1#5,act#5 := s, rec, ghost, grid2, grid1, act;

stk := OpCode#Aux#InitStk();

Label_0:
	 // 0: LOAD 0, 0 (s: P!GameState)
	call stk := OpCode#Load(stk, s#5);
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
	call stk := OpCode#Load(stk, act#5);
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
	call stk := OpCode#Load(stk, act#5);
	// 13: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 14: LOAD 0, 1 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#5);
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
	call stk := OpCode#Load(stk, act#5);
	// 21: GET (fieldname: DIRECTION)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$DIRECTION): Field (int)]));
	// 22: PUSH (intValue: 1)
	call stk := OpCode#Pushi(stk, 1);
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
	 

	
