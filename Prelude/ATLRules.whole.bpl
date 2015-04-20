procedure match_PlayerMoveLeft() returns (res: Seq ref);
ensures res==Seq#Empty() ==> (forall i: int :: inRange(i,0,Seq#Length(findPatterns_PlayerMoveLeft($srcHeap)))==>	
!(   read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),0),pacman$GameState.STATE) == 3
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.DONEBY) == 1
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),1), pacman$Record.FRAME)
	 && read($srcHeap,Seq#Index(Seq#Index(findPatterns_PlayerMoveLeft($srcHeap),i),5),pacman$Action.DIRECTION)==1)
);
ensures res!=Seq#Empty() ==> 
       Seq#Contains(findPatterns_PlayerMoveLeft($srcHeap), res) 
	&& read($srcHeap,Seq#Index(res,0),pacman$GameState.STATE) == 3
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DONEBY) == 1
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.FRAME) == 
			read($srcHeap, Seq#Index(res,1), pacman$Record.FRAME)
	&& read($srcHeap,Seq#Index(res,5),pacman$Action.DIRECTION)==1
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














