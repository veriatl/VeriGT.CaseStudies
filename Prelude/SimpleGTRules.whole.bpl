procedure match_PlayerMoveLeft() returns (res: Seq ref);
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

procedure match_PlayerStay() returns (res: Seq ref);
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerStay($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerStay($srcHeap),i),0),pacman$GameState.STATE) == 3
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerStay($srcHeap),i),4),pacman$Action.DONEBY) == 1
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerStay($srcHeap),i),4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_PlayerStay($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerStay($srcHeap),i),4),pacman$Action.DIRECTION)==5

)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_PlayerStay($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 3
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DONEBY) == 1
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DIRECTION)==5
;


procedure match_GhostMoveLeft() returns (res: Seq ref);
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),0),pacman$GameState.STATE) == 4
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),5),pacman$Action.DONEBY) == 2
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft($srcHeap),i),5),pacman$Action.DIRECTION)==1)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_GhostMoveLeft($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 4
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DONEBY) == 2
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DIRECTION)==1
;

procedure match_GhostStay() returns (res: Seq ref);
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostStay($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),0),pacman$GameState.STATE) == 4
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),4),pacman$Action.DONEBY) == 2
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_GhostStay($srcHeap),i),4),pacman$Action.DIRECTION)==5)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_GhostStay($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 4
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DONEBY) == 2
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DIRECTION)==5
;

procedure match_Collect() returns (res: Seq ref);
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect($srcHeap)))==>	
!(  read($srcHeap,Seq#Index(Seq#Index(findPatterns_Collect($srcHeap),i),0),pacman$GameState.STATE) == 5
));
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_Collect($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
;

procedure match_Kill() returns (res: Seq ref);
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill($srcHeap)))==>	
!(  read($srcHeap,Seq#Index(Seq#Index(findPatterns_Kill($srcHeap),i),0),pacman$GameState.STATE) == 5
));
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_Kill($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
;

procedure match_UpdateFrame() returns (res: Seq ref);
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_UpdateFrame($srcHeap)))==>	
!(  read($srcHeap,Seq#Index(Seq#Index(findPatterns_UpdateFrame($srcHeap),i),0),pacman$GameState.STATE) == 5 
));
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_UpdateFrame($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 5
;


procedure apply_PlayerMoveLeft(res: Seq ref);
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
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
ensures  $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);

procedure apply_PlayerStay(res: Seq ref);
requires $Well_form($srcHeap);
requires lemma_col($srcHeap, col);
requires Seq#Contains(findPatterns_PlayerStay($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 3
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DONEBY) == 1
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,4),pacman$Action.DIRECTION)==5;
modifies $srcHeap;
ensures read($srcHeap, Seq#Index(res,0), pacman$GameState.STATE)==4;
ensures !read($srcHeap, Seq#Index(res,4), alloc);
ensures (forall<alpha> o:ref,f:Field alpha::
  o!=null && read(old($srcHeap),o,alloc)==>
   (dtype(o)==pacman$GameState && f==pacman$GameState.STATE)
   ||(dtype(o)==pacman$Action && (f==alloc||f==pacman$Action.DONEBY||f==pacman$Action.DIRECTION		||f==pacman$Action.FRAME))
   ||(read($srcHeap,o,f)==read(old($srcHeap),o,f))); 
ensures $Well_form($srcHeap);
ensures lemma_col($srcHeap, col);
 
procedure apply_GhostMoveLeft(res: Seq ref);
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
ensures  $Well_form($srcHeap);
ensures  lemma_col($srcHeap, col);

procedure apply_GhostStay(res: Seq ref);
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
 
procedure apply_Collect(res: Seq ref, recNew: ref);
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
ensures  $Well_form($srcHeap);   
ensures  lemma_col($srcHeap, col);
   
procedure apply_Kill(res: Seq ref);
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
ensures  $Well_form($srcHeap);
ensures  lemma_col($srcHeap, col);

procedure apply_UpdateFrame(res: Seq ref, recNew: ref);
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
ensures  $Well_form($srcHeap);
ensures  lemma_col($srcHeap, col);



function $Well_form($hp:HeapType): bool
{
// 1.
(forall pac1,pac2: ref::
	pac1 != null && read($hp,pac1,alloc) && dtype(pac1) == pacman$Pacman
&&	pac2 != null && read($hp,pac2,alloc) && dtype(pac2) == pacman$Pacman
==>
	pac1 == pac2
) 
&&
// 2.
(forall r1,r2: ref::
	r1 != null && read($hp,r1,alloc) && dtype(r1) == pacman$Record
&&	r2 != null && read($hp,r2,alloc) && dtype(r2) == pacman$Record
==>
	r1 ==r2
)
&&
// 3.
(forall<alpha> grid1, grid2: ref :: 
	grid1 != null && read($hp,grid1,alloc) && dtype(grid1) == pacman$Grid
&&	grid2 != null && read($hp,grid2,alloc) && dtype(grid2) == pacman$Grid
	/* grid1 can equal to grid2 */
	==>
	reachable($hp, grid1, grid2)
)
&&
// 4.
(forall gs1,gs2: ref::
	gs1 != null && read($hp,gs1,alloc) && dtype(gs1) == pacman$GameState
&&	gs2 != null && read($hp,gs2,alloc) && dtype(gs2) == pacman$GameState
==>
	gs1 == gs2
)
&&
// 5.
(forall gs1: ref::
	(gs1 != null && read($hp,gs1,alloc) && dtype(gs1) == pacman$GameState && read($hp,gs1,pacman$GameState.STATE)==3) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($hp,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($hp,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($hp,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) ))
&&
// 6.
(forall gs1: ref::
	(gs1 != null && read($hp,gs1,alloc) && dtype(gs1) == pacman$GameState && read($hp,gs1,pacman$GameState.STATE)==4) ==>
	(forall<alpha> grid1: ref :: grid1 != null && read($hp,grid1,alloc) && dtype(grid1) == pacman$Grid && dtype(read($hp,grid1,pacman$Grid.hasEnemy)) <: pacman$Ghost
		==> !(dtype(read($hp,grid1,pacman$Grid.hasPlayer)) <: pacman$Pacman) ))
}

var col: Seq ref;
var idx: int;

	


function lemma_col($hp: HeapType, $col: Seq ref):bool
{
(forall i: int :: 0<=i && i<Seq#Length($col) ==>
Seq#Index($col,i) != null 
&& read($hp, Seq#Index($col,i), alloc) 
&& dtype(Seq#Index($col,i)) == pacman$Action
&& read($hp, Seq#Index($col,i), pacman$Action.DONEBY) == 1
&& read($hp, Seq#Index($col,i), pacman$Action.DIRECTION) != 5
)
&&
(forall i: int :: 0<=i && i<Seq#Length($col)-1 ==>
	read($hp, Seq#Index($col,i+1), pacman$Action.FRAME) - read($hp, Seq#Index($col,i), pacman$Action.FRAME) < Pacman#ghost#INTERVAL	
)
&&
(forall i,j: int :: 0<=i && i<j && j<Seq#Length($col) ==>
	Seq#Index($col,i)!=Seq#Index($col,j)
)
}

/*
&&
(forall<alpha> grid: ref :: 
	grid != null && read($hp,grid,alloc) && dtype(grid) == pacman$Grid
	&& read($hp,grid,pacman$Grid.hasGem)!=null && read($hp,read($hp,grid,pacman$Grid.hasGem),alloc)
	==>
	dtype(read($hp,grid,pacman$Grid.hasGem)) == pacman$Gem
)
*/