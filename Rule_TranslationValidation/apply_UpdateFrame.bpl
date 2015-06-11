procedure apply_UpdateFrameTest(res: Seq ref, recNew: ref)
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
requires  Seq#Contains(findPatterns_UpdateFrame($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
	&& recNew!=null && !read($srcHeap,recNew,alloc) && dtype(recNew)==pacman$Record;
modifies $srcHeap;
ensures recNew!=null && read($srcHeap,recNew,alloc) && dtype(recNew)==pacman$Record;
// gameState.STATE = 3
ensures read($srcHeap, Seq#Index(res,0), pacman$GameState.STATE) == 3;		
// gameState.record = newRecord
ensures read($srcHeap, Seq#Index(res,0), pacman$GameState.record) == recNew;		
// initialize newRecord
ensures read($srcHeap, recNew, pacman$Record.FRAME) == old(read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)+1);
ensures read($srcHeap, recNew, pacman$Record.SCORE) == old(read($srcHeap, Seq#Index(res,1), pacman$Record.SCORE));	
// rec.alloc = false
ensures !read($srcHeap, Seq#Index(res,1), alloc);
ensures (forall<alpha> o:ref,f:Field alpha::
  o!=null && read(old($srcHeap),o,alloc)==>
   (dtype(o)==pacman$GameState && (f==pacman$GameState.STATE||f==pacman$GameState.record))
   ||(dtype(o)==pacman$Record && (f==pacman$Record.FRAME||f==pacman$Record.SCORE||f==alloc))
   ||(read($srcHeap,o,f)==read(old($srcHeap),o,f))); 
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);
{
	var s#11: ref;
	var rec#11: ref;
	var pac#11: ref;
	var recNew#11: ref;
	var stk: Seq BoxType;
	
	// [Important] the reason we can make such assumption, is because we have already pass the <Kill> state, so that we should have no grid that has both player and ghost. Unfortunately, current UpdateFrame is too week to guarantee this. One option is to make assumption as we did here. Or we could rewrite UpdateFrame to be stronger. 
	// P2 specific. This is to prove well_form 5 and 6.
	assume (forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid ==>
	!(dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost && dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman));
	
	// allocation
	$srcHeap := update($srcHeap, recNew, alloc, true);
	assume $IsGoodHeap($srcHeap);
	
	// local init
	s#11 := Seq#Index(res,0);
	rec#11 := Seq#Index(res,1);
	pac#11 := Seq#Index(res,2);
	recNew#11 := recNew;
	
	// stk init
	stk := OpCode#Aux#InitStk();
	
	 // 0: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#11);
	 // 1: PUSH (intValue: 5)
	 call stk := OpCode#Pushi(stk, 5);
	 // 2: REMOVE (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int),0);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 3: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#11);
	 // 4: LOAD 0, 2 (rec: P!Record)
	 call stk := OpCode#Load(stk, rec#11);
	 // 5: REMOVE (fieldname: record)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$record): Field (ref),null);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 6: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#11);
	 // 7: PUSH (intValue: 3)
	 call stk := OpCode#Pushi(stk, 3);
	 // 8: ADD (fieldname: STATE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$STATE): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 // 9: LOAD 0, 1 (s: P!GameState)
	call stk := OpCode#Load(stk, s#11);
	// 10: LOAD 0, 4 (recNew: P!Record)
	call stk := OpCode#Load(stk, recNew#11);
	// 11: ADD (fieldname: record)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$record): Field (ref), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 // 12: LOAD 0, 4 (recNew: P!Record)
	call stk := OpCode#Load(stk, recNew#11);
	// 13: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#11);
	// 14: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 15: PUSH (intValue: 1)
	call stk := OpCode#Pushi(stk, 1);
	// 16: INVOKE (argcount: 1) (opname: +)
	call stk := OCL#Integer#Plus(stk);

	// 17: ADD (fieldname: FRAME)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$FRAME): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 18: LOAD 0, 4 (recNew: P!Record)
	call stk := OpCode#Load(stk, recNew#11);
	// 19: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#11);
	// 20: GET (fieldname: SCORE)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$SCORE): Field (int)]));
	// 21: ADD (fieldname: SCORE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$SCORE): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 // 22: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#11);
	// 23: DELETE
	assert Seq#Length(stk) >= 1;
	assert $Unbox(OpCode#Top(stk)) != null;
	$srcHeap := update($srcHeap, $Unbox(OpCode#Top(stk)), alloc, false);
	stk := Seq#Take(stk, Seq#Length(stk)-1);		

}