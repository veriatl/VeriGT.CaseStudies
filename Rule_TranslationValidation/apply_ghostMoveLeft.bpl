procedure apply_GhostMoveLeftTest(res: Seq ref)
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
requires Seq#Contains(findPatterns_GhostMoveLeft($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 4
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DONEBY) == 2
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DIRECTION)==1;
modifies $srcHeap;
// s : P!GameState(STATE=~5)
ensures read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5;
// grid2: P!Grid(hasEnemy=~ghost)
ensures read($srcHeap,Seq#Index(res,3),pacman$Grid.hasEnemy) == Seq#Index(res,2);
// grid1: P!Grid(hasEnemy=~null)
ensures read($srcHeap,Seq#Index(res,4),pacman$Grid.hasEnemy) == null;
// act : P!Action(alloc=~false)
ensures !read($srcHeap,Seq#Index(res,5),alloc);
ensures (forall<alpha> o:ref,f:Field alpha::
  o!=null && read(old($srcHeap),o,alloc)==>
   (dtype(o)==pacman$GameState && f==pacman$GameState.STATE)
   ||(dtype(o)==pacman$Grid && f==pacman$Grid.hasEnemy)
   ||(dtype(o)==pacman$Action && (f==alloc||f==pacman$Action.DONEBY||f==pacman$Action.DIRECTION		||f==pacman$Action.FRAME))
   ||(read($srcHeap,o,f)==read(old($srcHeap),o,f))); 
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);
{
	var stk: Seq BoxType;
	var s#5: ref;
	var rec#5: ref;
	var ghost#5: ref;
	var grid1#5: ref;
	var grid2#5: ref;
	var act#5: ref;
	
	s#5 := Seq#Index(res,0);
	rec#5 := Seq#Index(res,1);
	ghost#5 := Seq#Index(res,2);
	grid2#5 := Seq#Index(res,3);
	grid1#5 := Seq#Index(res,4);
	act#5 := Seq#Index(res,5);
	stk := OpCode#Aux#InitStk();
	
     // 0: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#5);
	 // 1: PUSH (intValue: 4)
	 call stk := OpCode#Pushi(stk, 4);
	 // 2: REMOVE (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 3: LOAD 0, 5 (grid1: P!Grid)
	 call stk := OpCode#Load(stk, grid1#5);
	 // 4: LOAD 0, 3 (ghost: P!Ghost)
	 call stk := OpCode#Load(stk, ghost#5);
	 // 5: REMOVE (fieldname: hasEnemy)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$hasEnemy): Field (ref),null);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);	 
	 // 6: LOAD 0, 6 (act: P!Action)
	 call stk := OpCode#Load(stk, act#5);
	 // 7: PUSH (intValue: 2)
	 call stk := OpCode#Pushi(stk, 2);
	 // 8: REMOVE (fieldname: DONEBY)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$DONEBY): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 9: LOAD 0, 6 (act: P!Action)
	 call stk := OpCode#Load(stk, act#5);
	// 10: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#5);
	// 11: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 12: REMOVE (fieldname: FRAME)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$FRAME): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 13: LOAD 0, 6 (act: P!Action)
	call stk := OpCode#Load(stk, act#5);
	// 14: PUSH (intValue: 1)
	call stk := OpCode#Pushi(stk, 1);
	// 15: REMOVE (fieldname: DIRECTION)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$DIRECTION): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 16: LOAD 0, 1 (s: P!GameState)
	call stk := OpCode#Load(stk, s#5);
	// 17: PUSH (intValue: 5)
	call stk := OpCode#Pushi(stk, 5);
	// 18: ADD (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	// 19: LOAD 0, 4 (grid2: P!Grid)
	call stk := OpCode#Load(stk, grid2#5);
	// 20: LOAD 0, 3 (ghost: P!Ghost)
	call stk := OpCode#Load(stk, ghost#5);
	// 21: ADD (fieldname: hasEnemy)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$hasEnemy): Field (ref), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 	 
	// 22: LOAD 0, 6 (act: P!Action)
	call stk := OpCode#Load(stk, act#5);
	// 23: DELETE
	assert Seq#Length(stk) >= 1;
	assert $Unbox(OpCode#Top(stk)) != null;
	$srcHeap := update($srcHeap, $Unbox(OpCode#Top(stk)), alloc, false);
	stk := Seq#Take(stk, Seq#Length(stk)-1);			

}
