	 
function findPatterns_PlayerMoveLeft(h: HeapType): Seq (Seq ref);
	// structure filter
	axiom (forall __heap: HeapType :: Seq#Length(findPatterns_PlayerMoveLeft(__heap)) >= 0);
	// 6 element in total
	axiom (forall __heap: HeapType ::
		(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
			Seq#Length(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i)) == 6)
	);
	// 1. pacman!Gamestate
	axiom (forall __heap: HeapType ::	
	 (forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),0) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),0),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),0)) == pacman$GameState
	 )
	);
	// 2. pacman!Record
	axiom (forall __heap: HeapType ::
		(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),1) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),1),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),1)) == pacman$Record
		)
	);
	// 3. pacman!Pacman
	axiom (forall __heap: HeapType ::
		(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),2) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),2),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),2)) == pacman$Pacman
		)
	);
	// 4. pacman!Grid
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),3) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),3),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),3)) == pacman$Grid
	)
	);
	// 5. pacman!Grid
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),4) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),4),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),4)) == pacman$Grid
	)
	);
	// 6. pacman!Action
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),5) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),5),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),5)) == pacman$Action
	)
	);	
	// grid1 != grid2
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),3) != 
		Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),4)
	)
	);		
	// s.record=~rec			
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		read(__heap, Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),0), pacman$GameState.record) == Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),1)	
	)
	);	
	// grid1.hasPlayer=~pac
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		read(__heap, Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),4), pacman$Grid.hasPlayer) == Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),2)	
	)
	);	
	// grid1.left=~grid2
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft(__heap))) ==> 
		read(__heap, Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),4), pacman$Grid.left) == Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft(__heap),i),3)	
	)
	);		
	// 
	axiom (forall __heap: HeapType ::
	(forall s,rec,pac,grid2,grid1,act: ref ::
		s != null && read(__heap,s,alloc) && dtype(s) == pacman$GameState
	&&	rec != null && read(__heap,rec,alloc) && dtype(rec) == pacman$Record
	&&	pac != null && read(__heap,pac,alloc) && dtype(pac) == pacman$Pacman
	&&	grid2 != null && read(__heap,grid2,alloc) && dtype(grid2) == pacman$Grid
	&&	grid1 != null && read(__heap,grid1,alloc) && dtype(grid1) == pacman$Grid
	&&	act != null && read(__heap,act,alloc) && dtype(act) == pacman$Action
	&&  grid1!=grid2
	&&  read(__heap, s, pacman$GameState.record) == rec
	&&  read(__heap, grid1, pacman$Grid.hasPlayer) == pac
	&&  read(__heap, grid1, pacman$Grid.left) == grid2
		==> Seq#Contains(findPatterns_PlayerMoveLeft(__heap), Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(s), rec), pac), grid2), grid1), act))
	)	
	);	
	

/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */

function findPatterns_GhostMoveLeft(h: HeapType): Seq (Seq ref);
	// structure filter
	axiom (forall __heap: HeapType :: Seq#Length(findPatterns_GhostMoveLeft(__heap)) >= 0);
	// 6 element in total
	axiom (forall __heap: HeapType ::
		(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
			Seq#Length(Seq#Index(findPatterns_GhostMoveLeft(__heap),i)) == 6)
	);
	// 1. pacman!Gamestate
	axiom (forall __heap: HeapType ::	
	 (forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),0) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),0),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),0)) == pacman$GameState
	 )
	);
	// 2. pacman!Record
	axiom (forall __heap: HeapType ::
		(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),1) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),1),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),1)) == pacman$Record
		)
	);
	// 3. pacman!Ghost
	axiom (forall __heap: HeapType ::
		(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),2) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),2),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),2)) == pacman$Ghost
		)
	);
	// 4. pacman!Grid
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),3) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),3),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),3)) == pacman$Grid
	)
	);
	// 5. pacman!Grid
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),4) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),4),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),4)) == pacman$Grid
	)
	);
	// 6. pacman!Action
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),5) != null 
		&& read(__heap,Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),5),alloc) 
		&& dtype(Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),5)) == pacman$Action
	)
	);	
	// grid1 != grid2
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),3) != 
		Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),4)
	)
	);		
	// s.record=~rec			
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		read(__heap, Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),0), pacman$GameState.record) == Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),1)	
	)
	);	
	// grid1.hasEnemy=~ghost
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		read(__heap, Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),4), pacman$Grid.hasEnemy) == Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),2)	
	)
	);	
	// grid1.left=~grid2
	axiom (forall __heap: HeapType ::
	(forall i: int :: inRange(i,0,Seq#Length(findPatterns_GhostMoveLeft(__heap))) ==> 
		read(__heap, Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),4), pacman$Grid.left) == Seq#Index(Seq#Index(findPatterns_GhostMoveLeft(__heap),i),3)	
	)
	);		
	// 
	axiom (forall __heap: HeapType ::
	(forall s,rec,ghost,grid2,grid1,act: ref ::
		s != null && read(__heap,s,alloc) && dtype(s) == pacman$GameState
	&&	rec != null && read(__heap,rec,alloc) && dtype(rec) == pacman$Record
	&&	ghost != null && read(__heap,ghost,alloc) && dtype(ghost) == pacman$Ghost
	&&	grid2 != null && read(__heap,grid2,alloc) && dtype(grid2) == pacman$Grid
	&&	grid1 != null && read(__heap,grid1,alloc) && dtype(grid1) == pacman$Grid
	&&	act != null && read(__heap,act,alloc) && dtype(act) == pacman$Action
	&&  grid1!=grid2
	&&  read(__heap, s, pacman$GameState.record) == rec
	&&  read(__heap, grid1, pacman$Grid.hasEnemy) == ghost
	&&  read(__heap, grid1, pacman$Grid.left) == grid2
		==> Seq#Contains(findPatterns_GhostMoveLeft(__heap), Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(s), rec), ghost), grid2), grid1), act))
	)	
	);	


	
	
/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */

function findPatterns_Collect(h: HeapType): Seq (Seq ref);
		// structure filter
		axiom (forall __heap: HeapType :: Seq#Length(findPatterns_Collect(__heap)) >= 0);
		// 5 element in total
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			Seq#Length(Seq#Index(findPatterns_Collect(__heap),i)) == 5));
		// 1. pacman!Gamestate
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),0) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),0),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),0)) == pacman$GameState
		));
		// 2. pacman!Record
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),1) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),1),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),1)) == pacman$Record
		));		
		// 3. pacman!Pacman
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),2) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),2),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),2)) == pacman$Pacman
		));			
		// 4. pacman!Gem
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),3) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),3),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),3)) == pacman$Gem
		));			
		// 5. pacman!Grid
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),4) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),4),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),4)) == pacman$Grid
		));			
		// s.record=~rec
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			read(__heap, Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),0), pacman$GameState.record) == Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),1)	
		));	
		// grid1.hasPlayer=~pac
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			read(__heap, Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),4), pacman$Grid.hasPlayer) == Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),2)	
		));			
		// grid1.hasGem=~gem
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Collect(__heap))) ==> 
			read(__heap, Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),4), pacman$Grid.hasGem) == Seq#Index(Seq#Index(findPatterns_Collect(__heap),i),3)	
		));			
		
		
		axiom (forall __heap: HeapType :: (forall s,rec,pac,gem,grid: ref ::
			s != null && read(__heap,s,alloc) && dtype(s) == pacman$GameState
		&&	rec != null && read(__heap,rec,alloc) && dtype(rec) == pacman$Record
		&&	pac != null && read(__heap,pac,alloc) && dtype(pac) == pacman$Pacman
		&&	gem != null && read(__heap,gem,alloc) && dtype(gem) == pacman$Gem
		&&	grid != null && read(__heap,grid,alloc) && dtype(grid) == pacman$Grid
		&&  read(__heap, s, pacman$GameState.record) == rec
		&&  read(__heap, grid, pacman$Grid.hasPlayer) == pac
		&&  read(__heap, grid, pacman$Grid.hasGem) == gem
			==> Seq#Contains(findPatterns_Collect(__heap), Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(s), rec), pac), gem), grid))
		)); 
		
/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */	
		




function findPatterns_Kill(h: HeapType): Seq (Seq ref);
		// structure filter
		axiom (forall __heap: HeapType :: Seq#Length(findPatterns_Kill(__heap)) >= 0);
		// 5 element in total
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill(__heap))) ==> 
			Seq#Length(Seq#Index(findPatterns_Kill(__heap),i)) == 4));
		// 1. pacman!Gamestate
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),0) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),0),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),0)) == pacman$GameState
		));
		// 2. pacman!Ghost
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),1) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),1),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),1)) == pacman$Ghost
		));		
		// 3. pacman!Pacman
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),2) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),2),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),2)) == pacman$Pacman
		));			
		// 4. pacman!Grid
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),3) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),3),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),3)) == pacman$Grid
		));			
		

		// grid1.hasPlayer=~pac
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill(__heap))) ==> 
			read(__heap, Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),3), pacman$Grid.hasPlayer) == Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),2)	
		));			
		// grid1.hasEnemy=~ghost
		axiom (forall __heap: HeapType :: (forall i: int :: inRange(i,0,Seq#Length(findPatterns_Kill(__heap))) ==> 
			read(__heap, Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),3), pacman$Grid.hasEnemy) == Seq#Index(Seq#Index(findPatterns_Kill(__heap),i),1)	
		));			
		
		
		axiom (forall __heap: HeapType :: (forall s,ghost,pac,grid: ref ::
			s != null && read(__heap,s,alloc) && dtype(s) == pacman$GameState
		&&	ghost != null && read(__heap,ghost,alloc) && dtype(ghost) == pacman$Ghost
		&&	pac != null && read(__heap,pac,alloc) && dtype(pac) == pacman$Pacman
		&&	grid != null && read(__heap,grid,alloc) && dtype(grid) == pacman$Grid
		&&  read(__heap, grid, pacman$Grid.hasPlayer) == pac
		&&  read(__heap, grid, pacman$Grid.hasEnemy) == ghost
			==> Seq#Contains(findPatterns_Kill(__heap), Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(s), ghost), pac), grid))
		));		
		
		
/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */

function findPatterns_UpdateFrame(h: HeapType): Seq (Seq ref);
		// structure filter
		axiom (forall __heap: HeapType ::  Seq#Length(findPatterns_UpdateFrame(__heap)) >= 0);
		// 5 element in total
		axiom (forall __heap: HeapType ::  (forall i: int :: inRange(i,0,Seq#Length(findPatterns_UpdateFrame(__heap))) ==> 
			Seq#Length(Seq#Index(findPatterns_UpdateFrame(__heap),i)) == 3));
		// 1. pacman!Gamestate
		axiom (forall __heap: HeapType ::  (forall i: int :: inRange(i,0,Seq#Length(findPatterns_UpdateFrame(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),0) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),0),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),0)) == pacman$GameState
		));
		// 2. pacman!Record
		axiom (forall __heap: HeapType ::  (forall i: int :: inRange(i,0,Seq#Length(findPatterns_UpdateFrame(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),1) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),1),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),1)) == pacman$Record
		));		
		// 3. pacman!Pacman
		axiom (forall __heap: HeapType ::  (forall i: int :: inRange(i,0,Seq#Length(findPatterns_UpdateFrame(__heap))) ==> 
			Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),2) != null 
			&& read(__heap,Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),2),alloc) 
			&& dtype(Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),2)) == pacman$Pacman
		));			
		
		

		// GameState.Record=~rec
		axiom (forall __heap: HeapType ::  (forall i: int :: inRange(i,0,Seq#Length(findPatterns_UpdateFrame(__heap))) ==> 
			read(__heap, Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),0), pacman$GameState.record) == Seq#Index(Seq#Index(findPatterns_UpdateFrame(__heap),i),1)	
		));			
		
		
		
		axiom (forall __heap: HeapType ::  (forall s,rec,pac: ref ::
			s != null && read(__heap,s,alloc) && dtype(s) == pacman$GameState
		&&	rec != null && read(__heap,rec,alloc) && dtype(rec) == pacman$Record
		&&	pac != null && read(__heap,pac,alloc) && dtype(pac) == pacman$Pacman
		&&  read(__heap, s, pacman$GameState.record) == rec
			==> Seq#Contains(findPatterns_UpdateFrame(__heap), Seq#Build(Seq#Build(Seq#Singleton(s), rec), pac))
		));