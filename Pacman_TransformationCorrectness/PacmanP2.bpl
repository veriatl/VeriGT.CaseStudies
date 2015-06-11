procedure driver();
requires $IsGoodHeap($srcHeap);
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
modifies $srcHeap, col;
ensures (forall gs1: ref::
	(gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState && read($srcHeap,gs1,pacman$GameState.STATE)==4) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) ));
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);

implementation driver()
{

var $i: int;

var s#0: ref;
var rec#0: ref;
var pac#0: ref;
var grid1#0: ref;
var grid2#0: ref;
var act#0: ref;

var s#4: ref;
var rec#4: ref;
var pac#4: ref;
var grid1#4: ref;
var act#4: ref;

var s#5: ref;
var rec#5: ref;
var ghost#5: ref;
var grid1#5: ref;
var grid2#5: ref;
var act#5: ref;

var s#8: ref;
var rec#8: ref;
var ghost#8: ref;
var grid1#8: ref;
var act#8: ref;

var s#9: ref;
var rec#9: ref;
var pac#9: ref;
var gem#9: ref;
var grid#9: ref;
var recordNew#9: ref;

var s#10: ref;
var ghost#10: ref;
var pac#10: ref;
var grid#10: ref;

var s#11: ref;
var rec#11: ref;
var pac#11: ref;
var recordNew#11: ref;

var todo: Seq ref;	
var pattern: Seq ref;	

var P#0: Seq (Seq ref);
var b#0: bool;

var P#5: Seq (Seq ref);
var b#5: bool;

var P#9: Seq (Seq ref);
var b#9: bool;

var P#10: Seq (Seq ref);
var b#10: bool;

var P#11: Seq (Seq ref);
var b#11: bool;



while(true)
invariant $Well_form($srcHeap);
invariant lemma_col($srcHeap, col);
{

	match_PlayerMoveLeft:	
		havoc todo;
		call todo := match_PlayerMoveLeft();
		goto apply_PlayerMoveLeft;
				
	apply_PlayerMoveLeft:
		if(todo!=Seq#Empty()){
			// execute applier block start
			
			call apply_PlayerMoveLeft(todo);
				
			// havoc act#0; as a alternative to dispose act#0
			// act#0 := null;
			
			
			// update finished, Heap should still be in a valid state.

			// exists RHS
			
			// Termination Metric 

			// restart
			goto restart;
		}else{
			goto match_PlayerStay;
		}

	match_PlayerStay:	
		havoc todo;
		call todo := match_PlayerStay();
		goto apply_PlayerStay;
				
	apply_PlayerStay:
		if(todo!=Seq#Empty()){
			// execute applier block start
			call apply_PlayerStay(todo);
			// havoc act#0; as a alternative to dispose act#0
			// act#0 := null;
			
			
			// update finished, Heap should still be in a valid state.

			// exists RHS
			
			// Termination Metric 

			// restart
			goto restart;
		}else{
			goto match_GhostMoveLeft;
		}

		
	match_GhostMoveLeft:	
		havoc todo;
		call todo := match_GhostMoveLeft();
		goto apply_GhostMoveLeft;

				
	apply_GhostMoveLeft:
		if(todo!=Seq#Empty()){
			// execute applier block start
			call apply_GhostMoveLeft(todo);
			// update finished, Heap should still be in a valid state.

			// exists RHS
			
			// Termination Metric 

			// restart
			goto restart;
		}else{
			goto match_GhostStay;
		}
	
	match_GhostStay:	
		havoc todo;
		call todo := match_GhostStay();
		goto apply_GhostStay;

				
	apply_GhostStay:
		if(todo!=Seq#Empty()){
			// execute applier block start
			call apply_GhostStay(todo);
			
			// update finished, Heap should still be in a valid state.




			// exists RHS
			
			// Termination Metric 

			// restart
			goto restart;
		}else{
			goto match_Collect;
		}
		
	match_Collect:	
		havoc todo;
		call todo := match_Collect();
		goto apply_Collect;
		
	apply_Collect:
		if(todo!=Seq#Empty()){
		
			// newRecord
			havoc recordNew#9;
			assume recordNew#9 != null && !read($srcHeap, recordNew#9, alloc) && dtype(recordNew#9) == pacman$Record;
			
	
			// execute applier block start

			call apply_Collect(todo, recordNew#9);
			
			// update finished, Heap should still be in a valid state.

		
			// exists RHS
			
			// Termination Metric 

			// restart
			goto restart;
		}else{
			goto match_Kill;
		}


	match_Kill:	
		havoc todo;
		call todo := match_Kill();
		goto apply_Kill;
		
	apply_Kill:
		if(todo!=Seq#Empty()){
			// execute applier block start

			call apply_Kill(todo);
			// todo

			
			// exists RHS
			
			// Termination Metric 

			// restart
			goto restart;
		}else{
			goto match_UpdateFrame;
		}

	match_UpdateFrame:	
		havoc todo;
		call todo := match_UpdateFrame();
		goto apply_UpdateFrame;
		
	apply_UpdateFrame:
		if(todo!=Seq#Empty()){
		
			// newRecord
			havoc recordNew#11;
			assume recordNew#11 != null && !read($srcHeap, recordNew#11, alloc) && dtype(recordNew#11) == pacman$Record;
	
			// execute applier block start
			call apply_UpdateFrame(todo, recordNew#11);
					
			// exists RHS
			
			// Termination Metric 

			// restart
			goto restart;
		}else{
			goto nextRule;
		}
	
	nextRule:	
		goto survive;	

	restart:


	
}

survive:


}












