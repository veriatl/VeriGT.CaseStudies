procedure apply_GhostStayTest(res: Seq ref)
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
requires Seq#Contains(findPatterns_GhostStay($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 4
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DONEBY) == 2
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DIRECTION)==5 ;
modifies $srcHeap;
ensures read($srcHeap, Seq#Index(res,0), pacman$GameState.STATE)==5;
ensures !read($srcHeap, Seq#Index(res,4), alloc);
ensures (forall<alpha> o:ref,f:Field alpha::
  o!=null && read(old($srcHeap),o,alloc)==>
   (dtype(o)==pacman$GameState && f==pacman$GameState.STATE)
   ||(dtype(o)==pacman$Action && (f==alloc||f==pacman$Action.DONEBY||f==pacman$Action.DIRECTION	||f==pacman$Action.FRAME))
   ||(read($srcHeap,o,f)==read(old($srcHeap),o,f))); 
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);
{
	var s#8: ref;
	var rec#8: ref;
	var ghost#8: ref;
	var grid1#8: ref;
	var act#8: ref;
	var stk: Seq BoxType;
	
	s#8 := Seq#Index(res,0);
	rec#8 := Seq#Index(res,1);
	ghost#8 := Seq#Index(res,2);
	grid1#8 := Seq#Index(res,3);
	act#8 := Seq#Index(res,4);
	
	stk := OpCode#Aux#InitStk();

	 // 0: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#8);
	 // 1: PUSH (intValue: 4)
	 call stk := OpCode#Pushi(stk, 4);
	 // 2: REMOVE (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);	
	 // 3: LOAD 0, 5 (act: P!Action)
	 call stk := OpCode#Load(stk, act#8);
	 // 4: PUSH (intValue: 2)
	 call stk := OpCode#Pushi(stk, 2);
	 // 5: REMOVE (fieldname: DONEBY)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$DONEBY): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 6: LOAD 0, 5 (act: P!Action)
	 call stk := OpCode#Load(stk, act#8);
	 // 7: LOAD 0, 2 (rec: P!Record)
	 call stk := OpCode#Load(stk, rec#8);
	 // 8: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 9: REMOVE (fieldname: FRAME)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$FRAME): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
    // 10: LOAD 0, 5 (act: P!Action)
	call stk := OpCode#Load(stk, act#8);
	// 11: PUSH (intValue: 5)
	call stk := OpCode#Pushi(stk, 5);
	// 12: REMOVE (fieldname: DIRECTION)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$DIRECTION): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	// 13: LOAD 0, 1 (s: P!GameState)
	call stk := OpCode#Load(stk, s#8);
	// 14: PUSH (intValue: 5)
	call stk := OpCode#Pushi(stk, 5);
	// 15: ADD (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 // 16: LOAD 0, 5 (act: P!Action)
	call stk := OpCode#Load(stk, act#8);
	// 17: DELETE
	assert Seq#Length(stk) >= 1;
	assert $Unbox(OpCode#Top(stk)) != null;
	$srcHeap := update($srcHeap, $Unbox(OpCode#Top(stk)), alloc, false);
	stk := Seq#Take(stk, Seq#Length(stk)-1);
}