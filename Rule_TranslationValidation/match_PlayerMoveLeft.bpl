procedure match_PlayerMoveLeftTest() returns (res: Seq ref)
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),0),pacman$GameState.STATE) == 3
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.DONEBY) == 1
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.DIRECTION)==1
	 && !(dtype(read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),3), pacman$Grid.hasEnemy))<:pacman$Ghost)
)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_PlayerMoveLeft($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 3
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DONEBY) == 1
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DIRECTION)==1
	&& !(dtype(read($srcHeap,Seq#Index(res,3), pacman$Grid.hasEnemy))<:pacman$Ghost)
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
			 && read($srcHeap,Seq#Index(Seq#Index(P#0,i),5),pacman$Action.DIRECTION)==1
			 && dtype(read($srcHeap,Seq#Index(Seq#Index(P#0,i),3), pacman$Grid.hasEnemy))!=pacman$Ghost)
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





procedure match_filter_PlayerMoveLeft(s:ref, rec:ref, pac:ref, grid2:ref, grid1:ref, act:ref) returns(r: bool)
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
 free requires !(dtype(read($srcHeap,grid2,pacman$Grid.hasEnemy)) <: class._System.array); // # SHOULD BE IN METAMODEL.BPL
 ensures r <==> ( 
		read($srcHeap,s,pacman$GameState.STATE) == 3
	 && read($srcHeap,act,pacman$Action.DONEBY) == 1
	 && read($srcHeap,act,pacman$Action.FRAME) == read($srcHeap, rec, pacman$Record.FRAME)
	 && read($srcHeap,act,pacman$Action.DIRECTION)==1
	 && !(dtype(read($srcHeap,grid2, pacman$Grid.hasEnemy))<:pacman$Ghost));
{
var s#0: ref;
var rec#0: ref;
var pac#0: ref;
var grid1#0: ref;
var grid2#0: ref;
var act#0: ref;
var stk: Seq BoxType;

var b#4: bool;
var b#11: bool;
var b#19: bool;
var b#26: bool;
var b#32: bool;
var b#36: bool;

var obj#33: Seq ref;
var $i: int;

s#0,rec#0,pac#0,grid2#0,grid1#0,act#0 := s, rec, pac, grid2, grid1, act;

stk := OpCode#Aux#InitStk();

Label_0:
	 // 0: LOAD 0, 0 (s: P!GameState)
	call stk := OpCode#Load(stk, s#0);
	 // 1: GET (fieldname: STATE)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$STATE): Field (int)]));
	 // 2: PUSH (intValue: 3)
	call stk := OpCode#Pushi(stk, 3);
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
	call stk := OpCode#Load(stk, act#0);
	 // 6: GET (fieldname: DONEBY)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$DONEBY): Field (int)]));
	 // 7: PUSH (intValue: 1)
	call stk := OpCode#Pushi(stk, 1);
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
	call stk := OpCode#Load(stk, act#0);
	// 13: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 14: LOAD 0, 1 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#0);
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
	call stk := OpCode#Load(stk, act#0);
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
	// 26: IFN 47
	b#26 := $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
	if(!b#26){goto Label_47;}
	// 27: LOAD 0, 3 (grid2: P!Grid)
	call stk := OpCode#Load(stk, grid2#0);
	// 28: GET (fieldname: hasEnemy)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$hasEnemy): Field (ref)]));
	// 29: DUP
	call stk := OpCode#Dup(stk);
	// 30: FINDTYPE (modelname: #native, typename: Collection)
	call stk := OpCode#FindType(stk, _Native, _Collection);
	// 31: INVOKE (argcount: 1) (opname: oclIsKindOf)
	call stk := EMFTVM#OCL#isKindOf(stk);
	// 32: IFN 43
	b#32 := $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
	if(!b#32){goto Label_43;}
	// 33: ITERATE 38
	$i:=0;
	obj#33 := $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
	while($i<Seq#Length(obj#33))
	  invariant $i <= Seq#Length(obj#33);
	  invariant (forall i: int:: 0<=i &&i <$i ==>
			!(dtype(Seq#Index(obj#33,i)) <: pacman$Ghost)
	  );
	{
		stk := Seq#Build(stk, $Box(Seq#Index(obj#33, $i)));

		// 34: FINDTYPE (modelname: P, typename: Ghost)
		call stk := OpCode#FindType(stk, _P, _Ghost);
		// 35: INVOKE (argcount: 1) (opname: oclIsKindOf)
		call stk := EMFTVM#OCL#isKindOf(stk);
		// 36: IF 40
		b#36 := $Unbox(OpCode#Top(stk));
		call stk := OpCode#Pop(stk);
		if(b#36){goto Label_40;}
		// 37: ENDITERATE 34
	}
	
	// 38: PUSHF
	call stk := OpCode#Pushf(stk);
	// 39: GOTO 45
	goto Label_45;
Label_40:
	// 40: POP
	call stk := OpCode#Pop(stk);
	// 41: PUSHT
	call stk := OpCode#Pusht(stk);
	// 42: GOTO 45
	goto Label_45;
Label_43:
	// 43: FINDTYPE (modelname: P, typename: Ghost)
	call stk := OpCode#FindType(stk, _P, _Ghost);
	// 44: INVOKE (argcount: 1) (opname: oclIsKindOf)
	call stk := EMFTVM#OCL#isKindOf(stk);
Label_45:
	// 45: NOT
	call stk := OpCode#Not(stk);
	// 46: GOTO 48
	goto Label_48;
Label_47:
	// 47: PUSHF
	call stk := OpCode#Pushf(stk);
Label_48:
	r:= $Unbox(OpCode#Top(stk));
	call stk := OpCode#Pop(stk);
	
}	 

