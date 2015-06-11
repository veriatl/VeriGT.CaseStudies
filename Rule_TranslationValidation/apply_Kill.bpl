procedure apply_KillTest(res: Seq ref)
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
requires Seq#Contains(findPatterns_Kill($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5;
modifies $srcHeap;
// GameState.STATE = 6		
ensures read($srcHeap, Seq#Index(res,0), pacman$GameState.STATE)==6;
// Grid.hasPlayer = null
ensures read($srcHeap, Seq#Index(res,3), pacman$Grid.hasPlayer)==null;		
// pacman.alloc = false
ensures !read($srcHeap, Seq#Index(res,2), alloc);
ensures (forall<alpha> o:ref,f:Field alpha::
  o!=null && read(old($srcHeap),o,alloc)==>
   (dtype(o)==pacman$GameState && (f==pacman$GameState.STATE))
   ||(dtype(o)==pacman$Grid && f==pacman$Grid.hasPlayer)
   ||(dtype(o)==pacman$Pacman && f==alloc)
   ||(read($srcHeap,o,f)==read(old($srcHeap),o,f)));
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);
{
	var s#10: ref;
	var ghost#10: ref;
	var pac#10: ref;
	var grid#10: ref;
	var stk: Seq BoxType;
	
	s#10 := Seq#Index(res,0);
	ghost#10 := Seq#Index(res,1);
	pac#10 := Seq#Index(res,2);
	grid#10 := Seq#Index(res,3);

	stk := OpCode#Aux#InitStk();
	
	 // 0: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#10);
	 // 1: PUSH (intValue: 5)
	 call stk := OpCode#Pushi(stk, 5);
	 // 2: REMOVE (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 3: LOAD 0, 4 (grid: P!Grid)
	 call stk := OpCode#Load(stk, grid#10);
	 // 4: LOAD 0, 3 (pac: P!Pacman)
	 call stk := OpCode#Load(stk, pac#10);
	 // 5: REMOVE (fieldname: hasPlayer)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$hasPlayer): Field (ref),null);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 6: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#10);
	 // 7: PUSH (intValue: 6)
	 call stk := OpCode#Pushi(stk, 6);
	 // 8: ADD (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 	 
	 // 9: LOAD 0, 3 (pac: P!Pacman)
	call stk := OpCode#Load(stk, pac#10);
	// 10: DELETE
	assert Seq#Length(stk) >= 1;
	assert $Unbox(OpCode#Top(stk)) != null;
	$srcHeap := update($srcHeap, $Unbox(OpCode#Top(stk)), alloc, false);
	stk := Seq#Take(stk, Seq#Length(stk)-1);	
}