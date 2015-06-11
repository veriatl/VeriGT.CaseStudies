procedure driver();
requires $IsGoodHeap($srcHeap);
requires (forall gs1,gs2: ref::
	gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState
&&	gs2 != null && read($srcHeap,gs2,alloc) && dtype(gs2) == pacman$GameState
==>
	gs1 == gs2
);
requires (forall pac1,pac2: ref::
	pac1 != null && read($srcHeap,pac1,alloc) && dtype(pac1) == pacman$Pacman
&&	pac2 != null && read($srcHeap,pac2,alloc) && dtype(pac2) == pacman$Pacman
==>
	pac1 == pac2
);
requires (forall r1,r2: ref::
	r1 != null && read($srcHeap,r1,alloc) && dtype(r1) == pacman$Record
&&	r2 != null && read($srcHeap,r2,alloc) && dtype(r2) == pacman$Record
==>
	r1 ==r2
);
requires (forall<alpha> grid: ref :: 
	grid != null && read($srcHeap,grid,alloc) && dtype(grid) == pacman$Grid
	&& read($srcHeap,grid,pacman$Grid.hasGem)!=null && read($srcHeap,read($srcHeap,grid,pacman$Grid.hasGem),alloc)
	==>
	dtype(read($srcHeap,grid,pacman$Grid.hasGem)) == pacman$Gem
);
requires (forall<alpha> grid1, grid2: ref :: 
	grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid
&&	grid2 != null && read($srcHeap,grid2,alloc) && dtype(grid2) == pacman$Grid
	/* grid1 can equal to grid2 */
	==>
	reachable($srcHeap, grid1, grid2)
);
requires  !(forall<alpha> grid1, grid2: ref :: 
	grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid
&&	grid2 != null && read($srcHeap,grid2,alloc) && dtype(grid2) == pacman$Grid
==>  (read($srcHeap,grid1,pacman$Grid.hasPlayer) != null 
	&& read($srcHeap,grid2,pacman$Grid.hasEnemy) != null)
);
requires (forall gs1: ref::
	(gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState && read($srcHeap,gs1,pacman$GameState.STATE)==3) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) ));
requires (forall gs1: ref::
	(gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState && read($srcHeap,gs1,pacman$GameState.STATE)==4) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) ));
modifies $srcHeap;
ensures (forall gs1: ref::
	(gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState && read($srcHeap,gs1,pacman$GameState.STATE)==4) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) ));


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
invariant (forall gs1,gs2: ref::
	gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState
&&	gs2 != null && read($srcHeap,gs2,alloc) && dtype(gs2) == pacman$GameState
==>
	gs1 == gs2
);
invariant (forall pac1,pac2: ref::
	pac1 != null && read($srcHeap,pac1,alloc) && dtype(pac1) == pacman$Pacman
&&	pac2 != null && read($srcHeap,pac2,alloc) && dtype(pac2) == pacman$Pacman
==>
	pac1 == pac2
);
invariant (forall gs1: ref::
	(gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState && read($srcHeap,gs1,pacman$GameState.STATE)==3) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) )); 
invariant (forall gs1: ref::
	(gs1 != null && read($srcHeap,gs1,alloc) && dtype(gs1) == pacman$GameState && read($srcHeap,gs1,pacman$GameState.STATE)==4) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) ));

{

	match_PlayerMoveLeft:	
		havoc todo;
		call todo := match_PlayerMoveLeft();
		goto apply_PlayerMoveLeft;
				
	apply_PlayerMoveLeft:
		if(todo!=Seq#Empty()){
			// execute applier block start
			s#0 := Seq#Index(todo,0);
			rec#0 := Seq#Index(todo,1);
			pac#0 := Seq#Index(todo,2);
			grid2#0 := Seq#Index(todo,3);
			grid1#0 := Seq#Index(todo,4);
			act#0 := Seq#Index(todo,5);
	
			$srcHeap := update($srcHeap, s#0, pacman$GameState.STATE, 4);
			$srcHeap := update($srcHeap, grid1#0, pacman$Grid.hasPlayer, null);
			$srcHeap := update($srcHeap, grid2#0, pacman$Grid.hasPlayer, pac#0);
			$srcHeap := update($srcHeap, act#0, alloc, false);
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
			s#4 := Seq#Index(todo,0);
			rec#4 := Seq#Index(todo,1);
			pac#4 := Seq#Index(todo,2);
			grid1#4 := Seq#Index(todo,3);
			act#4 := Seq#Index(todo,4);
	
			$srcHeap := update($srcHeap, s#4, pacman$GameState.STATE, 4);
			$srcHeap := update($srcHeap, act#4, alloc, false);
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
			s#5 := Seq#Index(todo,0);
			rec#5 := Seq#Index(todo,1);
			ghost#5 := Seq#Index(todo,2);
			grid2#5 := Seq#Index(todo,3);
			grid1#5 := Seq#Index(todo,4);
			act#5 := Seq#Index(todo,5);


			

			
			$srcHeap := update($srcHeap, s#5, pacman$GameState.STATE, 5);
			$srcHeap := update($srcHeap, grid1#5, pacman$Grid.hasEnemy, null);
			$srcHeap := update($srcHeap, grid2#5, pacman$Grid.hasEnemy, ghost#5);
			$srcHeap := update($srcHeap, act#5, alloc, false);
			
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
			s#8 := Seq#Index(todo,0);
			rec#8 := Seq#Index(todo,1);
			ghost#8 := Seq#Index(todo,2);
			grid1#8 := Seq#Index(todo,3);
			act#8 := Seq#Index(todo,4);


			$srcHeap := update($srcHeap, s#8, pacman$GameState.STATE, 5);
			$srcHeap := update($srcHeap, act#8, alloc, false);
			
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
			// execute applier block start
			s#9 := Seq#Index(todo,0);
			rec#9 := Seq#Index(todo,1);
			pac#9 := Seq#Index(todo,2);
			gem#9 := Seq#Index(todo,3);
			grid#9 := Seq#Index(todo,4);



			
			// newRecord
			havoc recordNew#9;
			assume recordNew#9 != null && !read($srcHeap, recordNew#9, alloc) && dtype(recordNew#9) == 
			pacman$Record;
			$srcHeap := update($srcHeap, recordNew#9, alloc, true);
			assume $IsGoodHeap($srcHeap);
			
			// gameState.record = newRecord
			$srcHeap := update($srcHeap, s#9, pacman$GameState.record, recordNew#9);
			
			// initialize newRecord
			$srcHeap := update($srcHeap, recordNew#9, pacman$Record.FRAME, read($srcHeap, rec#9, pacman$Record.FRAME));
			
			$srcHeap := update($srcHeap, recordNew#9, pacman$Record.SCORE, read($srcHeap, rec#9, pacman$Record.SCORE)+100);
			

			
			// Grid.hasGem = null
			$srcHeap := update($srcHeap, grid#9, pacman$Grid.hasGem, null);
			
			// gem.alloc = false
			$srcHeap := update($srcHeap, gem#9, alloc, false);
			
			// rec.alloc = false
			$srcHeap := update($srcHeap, rec#9, alloc, false);
			
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
			s#10 := Seq#Index(todo,0);
			ghost#10 := Seq#Index(todo,1);
			pac#10 := Seq#Index(todo,2);
			grid#10 := Seq#Index(todo,3);


			// Grid.hasPlayer = null
			$srcHeap := update($srcHeap, grid#10, pacman$Grid.hasPlayer, null);
				
			$srcHeap := update($srcHeap, s#10, pacman$GameState.STATE, 6);
			
			// pacman.alloc = false
			$srcHeap := update($srcHeap, pac#10, alloc, false);

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
			// execute applier block start
			s#11 := Seq#Index(todo,0);
			rec#11 := Seq#Index(todo,1);
			pac#11 := Seq#Index(todo,2);

			// [Important] the reason we can make such assumption, is because we have already pass the <Kill> state, so that we should have no grid that has both player and ghost. Unfortunately, current UpdateFrame is too week to guarantee this. One option is to make assumption as we did here. Or we could rewrite UpdateFrame to be stronger.
			assume (forall<alpha> grid1: ref :: grid1 != null && read($srcHeap,grid1,alloc) && dtype(grid1) == pacman$Grid ==>
	!(dtype(read($srcHeap,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost && dtype(read($srcHeap,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman));
			
			// newRecord
			havoc recordNew#11;
			assume recordNew#11 != null && !read($srcHeap, recordNew#11, alloc) && dtype(recordNew#11) == 
			pacman$Record;
			$srcHeap := update($srcHeap, recordNew#11, alloc, true);
			assume $IsGoodHeap($srcHeap);

			
			// gameState.STATE = 3
			$srcHeap := update($srcHeap, s#11, pacman$GameState.STATE, 3);
			
			// gameState.record = newRecord
			$srcHeap := update($srcHeap, s#11, pacman$GameState.record, recordNew#11);
			
			// initialize newRecord
			$srcHeap := update($srcHeap, recordNew#11, pacman$Record.FRAME, read($srcHeap, rec#11, pacman$Record.FRAME)+1);
			
			$srcHeap := update($srcHeap, recordNew#11, pacman$Record.SCORE, read($srcHeap, rec#11, pacman$Record.SCORE));	

			// rec.alloc = false
			$srcHeap := update($srcHeap, rec#11, alloc, false);
			
 
			
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












