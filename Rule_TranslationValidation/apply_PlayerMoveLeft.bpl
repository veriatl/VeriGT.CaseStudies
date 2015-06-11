procedure apply_PlayerMoveLeftTest(res: Seq ref)
requires lemma_col($srcHeap, col);
requires $Well_form($srcHeap);
requires Seq#Contains(findPatterns_PlayerMoveLeft($srcHeap), res) 
   && read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 3
   && read($srcHeap,Seq#Index(res,5),pacman$Action.DONEBY) == 1
   && read($srcHeap,Seq#Index(res,5),pacman$Action.FRAME) == 
      read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
   && read($srcHeap,Seq#Index(res,5),pacman$Action.DIRECTION)==1
   && !(dtype(read($srcHeap,Seq#Index(res,3), pacman$Grid.hasEnemy))<:pacman$Ghost);
modifies $srcHeap, col;
// s : P!GameState(STATE=~4)
ensures read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 4;
// grid2: P!Grid(hasPlayer=~pac)
ensures read($srcHeap,Seq#Index(res,3),pacman$Grid.hasPlayer) == Seq#Index(res,2);
// grid1: P!Grid(hasPlayer=~null)
ensures read($srcHeap,Seq#Index(res,4),pacman$Grid.hasPlayer) == null;
// act : P!Action(alloc=~false)
ensures !read($srcHeap,Seq#Index(res,5),alloc);
ensures (forall<alpha> o:ref,f:Field alpha::
  o!=null && read(old($srcHeap),o,alloc)==>
   (dtype(o)==pacman$GameState && f==pacman$GameState.STATE)
   ||(dtype(o)==pacman$Grid && f==pacman$Grid.hasPlayer)
   ||(dtype(o)==pacman$Action && (f==alloc||f==pacman$Action.DONEBY||f==pacman$Action.DIRECTION		||f==pacman$Action.FRAME))
   ||(read($srcHeap,o,f)==read(old($srcHeap),o,f))); 
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);
{
	var s#0: ref;
	var rec#0: ref;
	var pac#0: ref;
	var grid1#0: ref;
	var grid2#0: ref;
	var act#0: ref;
	var stk: Seq BoxType;

	s#0 := Seq#Index(res,0);
	rec#0 := Seq#Index(res,1);
	pac#0 := Seq#Index(res,2);
	grid2#0 := Seq#Index(res,3);
	grid1#0 := Seq#Index(res,4);
	act#0 := Seq#Index(res,5);
				
	stk := OpCode#Aux#InitStk();

/* P3 specific, ghost */
assume Seq#Contains(col,act#0);
assume Seq#Index(col,idx) == act#0;
assume 0<=idx && idx<Seq#Length(col);

     // 0: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#0);
	 // 1: PUSH (intValue: 3)
	 call stk := OpCode#Pushi(stk, 3);
	 // 2: REMOVE (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 // 3: LOAD 0, 5 (grid1: P!Grid)
	 call stk := OpCode#Load(stk, grid1#0);
	 // 4: LOAD 0, 3 (pac: P!Pacman)
	 call stk := OpCode#Load(stk, pac#0);
	 // 5: REMOVE (fieldname: hasPlayer)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$hasPlayer): Field (ref), null);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 
	 // 6: LOAD 0, 6 (act: P!Action)
	 call stk := OpCode#Load(stk, act#0);
	 // 7: PUSH (intValue: 1)
	 call stk := OpCode#Pushi(stk, 1);
	 // 8: REMOVE (fieldname: DONEBY)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$DONEBY): Field (int), 0);
 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 // 9: LOAD 0, 6 (act: P!Action)
	 call stk := OpCode#Load(stk, act#0);
	// 10: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#0);
	// 11: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 12: REMOVE (fieldname: FRAME)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	 
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$FRAME): Field (int), 0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	// 13: LOAD 0, 6 (act: P!Action)
	call stk := OpCode#Load(stk, act#0);
	// 14: PUSH (intValue: 1)
	call stk := OpCode#Pushi(stk, 1);
	// 15: REMOVE (fieldname: DIRECTION)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$DIRECTION): Field (int), 0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	// 16: LOAD 0, 1 (s: P!GameState)
	call stk := OpCode#Load(stk, s#0);
	// 17: PUSH (intValue: 4)
	call stk := OpCode#Pushi(stk, 4);
	// 18: ADD (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	// 19: LOAD 0, 4 (grid2: P!Grid)
	call stk := OpCode#Load(stk, grid2#0);
	// 20: LOAD 0, 3 (pac: P!Pacman)
	call stk := OpCode#Load(stk, pac#0);
	// 21: ADD (fieldname: hasPlayer)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$hasPlayer): Field (ref), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	// 22: LOAD 0, 6 (act: P!Action)
	call stk := OpCode#Load(stk, act#0);
	// 23: DELETE
	assert Seq#Length(stk) >= 1;
	assert $Unbox(OpCode#Top(stk)) != null;
	$srcHeap := update($srcHeap, $Unbox(OpCode#Top(stk)), alloc, false);
	stk := Seq#Take(stk, Seq#Length(stk)-1);

/* P3 specific, ghost */
col := Seq#Drop(col,idx+1);	
}