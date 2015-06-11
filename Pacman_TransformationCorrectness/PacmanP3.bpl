/*
pacman moves within interval (invariant)
- prove by using ghost variable col, idx, in apply_PlayerMoveLeft
- explicit control how this two variable being changed during the simpleGT scheduling
- make sure the changes not break the invariant
*/
	
procedure driver();
requires lemma_col($srcHeap, col);	
requires $Well_form($srcHeap);
modifies $srcHeap, col, idx;
ensures (forall i: int :: 0<=i && i<Seq#Length(col)-1 ==>
	read($srcHeap, Seq#Index(col,i+1), pacman$Action.FRAME) - read($srcHeap, Seq#Index(col,i), pacman$Action.FRAME) < Pacman#ghost#INTERVAL	
);
ensures (forall i,j: int :: 0<=i && i<j && j<Seq#Length(col) ==>
	Seq#Index(col,i)!=Seq#Index(col,j)
);	
ensures (forall i: int :: 0<=i && i<Seq#Length(col) ==>
Seq#Index(col,i) != null 
&& read($srcHeap, Seq#Index(col,i), alloc) 
&& dtype(Seq#Index(col,i)) == pacman$Action
&& read($srcHeap, Seq#Index(col,i), pacman$Action.DONEBY) == 1
&& read($srcHeap, Seq#Index(col,i), pacman$Action.DIRECTION) != 5
);
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
invariant lemma_col($srcHeap, col);
invariant $Well_form($srcHeap);
{

	match_PlayerMoveLeft:	
		havoc todo;
		call todo := match_PlayerMoveLeft();
		goto apply_PlayerMoveLeft;
				
	apply_PlayerMoveLeft:
		if(todo!=Seq#Empty()){
			// execute applier block start
			
			// ideally idx == 0;
			havoc idx;

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











/*
procedure test()
modifies $srcHeap,col, idx;
{
assume  (forall i: int :: 0<=i && i<Seq#Length(col) ==>
Seq#Index(col,i) != null 
&& read($srcHeap, Seq#Index(col,i), alloc) 
&& dtype(Seq#Index(col,i)) == pacman$Action
&& read($srcHeap, Seq#Index(col,i), pacman$Action.DONEBY) == 1
&& read($srcHeap, Seq#Index(col,i), pacman$Action.DIRECTION) != 5
);


call driver();
}
*/
