procedure apply_CollectTest(res: Seq ref, recNew: ref)
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
requires Seq#Contains(findPatterns_Collect($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
	&& recNew!=null && !read($srcHeap,recNew,alloc) && dtype(recNew)==pacman$Record;
modifies $srcHeap;
ensures recNew!=null && read($srcHeap,recNew,alloc) && dtype(recNew)==pacman$Record;
// gameState.record = newRecord
ensures read($srcHeap, Seq#Index(res,0), pacman$GameState.record) == recNew;
// initialize newRecord
ensures read($srcHeap, recNew, pacman$Record.FRAME) == old(read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME));
ensures read($srcHeap, recNew, pacman$Record.SCORE) == old(read($srcHeap, Seq#Index(res,1), pacman$Record.SCORE)+100);
// Grid.hasGem = null
ensures read($srcHeap, Seq#Index(res,4), pacman$Grid.hasGem) == null;
// gem.alloc = false
ensures !read($srcHeap, Seq#Index(res,3), alloc);
// rec.alloc = false
ensures !read($srcHeap, Seq#Index(res,1), alloc);
ensures (forall<alpha> o:ref,f:Field alpha::
  o!=null && read(old($srcHeap),o,alloc)==>
   (dtype(o)==pacman$GameState && (f==pacman$GameState.STATE||f==pacman$GameState.record))
   ||(dtype(o)==pacman$Grid && f==pacman$Grid.hasGem)
   ||(dtype(o)==pacman$Record && (f==pacman$Record.FRAME||f==pacman$Record.SCORE||f==alloc))
   ||(dtype(o)==pacman$Gem && f==alloc)
   ||(read($srcHeap,o,f)==read(old($srcHeap),o,f))); 
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);
{
	var s#9: ref;
	var rec#9: ref;
	var pac#9: ref;
	var gem#9: ref;
	var grid#9: ref;
	var recordNew#9: ref;
	var stk: Seq BoxType;
	
	
	// allocation
	$srcHeap := update($srcHeap, recNew, alloc, true);
	assume $IsGoodHeap($srcHeap);
	
	// local init
	s#9 := Seq#Index(res,0);
	rec#9 := Seq#Index(res,1);
	pac#9 := Seq#Index(res,2);
	gem#9 := Seq#Index(res,3);
	grid#9 := Seq#Index(res,4);
	recordNew#9 := recNew;
	
	// stk init
	stk := OpCode#Aux#InitStk();
			
	 // 0: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#9);
	 // 1: LOAD 0, 2 (rec: P!Record)
	 call stk := OpCode#Load(stk, rec#9);
	 // 2: REMOVE (fieldname: record)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$record): Field (ref),null);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 3: LOAD 0, 5 (grid: P!Grid)
	 call stk := OpCode#Load(stk, grid#9);
	 // 4: LOAD 0, 4 (gem: P!Gem)
	 call stk := OpCode#Load(stk, gem#9);
	 // 5: REMOVE (fieldname: hasGem)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$hasGem): Field (ref),null);
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2);
	 // 6: LOAD 0, 1 (s: P!GameState)
	 call stk := OpCode#Load(stk, s#9);
	 // 7: LOAD 0, 6 (recNew: P!Record)
	 call stk := OpCode#Load(stk, recordNew#9);
	 // 8: ADD (fieldname: record)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$record): Field (ref), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	 // 9: LOAD 0, 6 (recNew: P!Record)
	call stk := OpCode#Load(stk, recordNew#9);
	// 10: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#9);
	// 11: GET (fieldname: FRAME)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$FRAME): Field (int)]));
	// 12: ADD (fieldname: FRAME)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 
	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$FRAME): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	// 13: LOAD 0, 6 (recNew: P!Record)
	call stk := OpCode#Load(stk, recordNew#9);
	// 14: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#9);
	// 15: GET (fieldname: SCORE)
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$SCORE): Field (int)]));
	// 16: PUSH (intValue: 100)
	call stk := OpCode#Pushi(stk, 100);
	// 17: INVOKE (argcount: 1) (opname: +)
	call stk := OCL#Integer#Plus(stk);
	// 18: ADD (fieldname: SCORE)
	 assert Seq#Length(stk) >= 2;
	 assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;

	 $srcHeap := update($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$SCORE): Field (int), $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	 
	 stk := Seq#Take(stk, Seq#Length(stk)-2); 
	// 19: LOAD 0, 2 (rec: P!Record)
	call stk := OpCode#Load(stk, rec#9);
	// 20: DELETE
	assert Seq#Length(stk) >= 1;
	assert $Unbox(OpCode#Top(stk)) != null;
	$srcHeap := update($srcHeap, $Unbox(OpCode#Top(stk)), alloc, false);
	stk := Seq#Take(stk, Seq#Length(stk)-1);	
	// 21: LOAD 0, 4 (gem: P!Gem)
	call stk := OpCode#Load(stk, gem#9);
	// 22: DELETE	
	assert Seq#Length(stk) >= 1;
	assert $Unbox(OpCode#Top(stk)) != null;
	$srcHeap := update($srcHeap, $Unbox(OpCode#Top(stk)), alloc, false);
	stk := Seq#Take(stk, Seq#Length(stk)-1);	

	

	

	


}