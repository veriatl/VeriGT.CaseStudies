function reachable(HeapType, ref, ref):bool;
  // update non-grid or non-orientation-field, will still be reachable.
  // theorem
  axiom (forall<alpha> $h: HeapType, $g1, $g2, $any: ref, $f: Field alpha,$v:alpha ::
	$g1 != null && read($h,$g1,alloc) && dtype($g1) == pacman$Grid
&&	$g2 != null && read($h,$g2,alloc) && dtype($g2) == pacman$Grid
&&  $any != null /* && read($h,$any,alloc) */
&& (dtype($any) != pacman$Grid
  || (dtype($any) == pacman$Grid && $f != pacman$Grid.left 
&&  $f != pacman$Grid.right 
&&  $f != pacman$Grid.top 
&&  $f != pacman$Grid.bottom ))
&&  reachable($h,$g1,$g2)
	==> reachable(update($h,$any,$f,$v),$g1,$g2));
	// def semantic of reachable
  axiom (forall<alpha> $h: HeapType, $g1, $g2: ref, $f: Field alpha ::
	$g1 != null && read($h,$g1,alloc) && dtype($g1) == pacman$Grid
&&	$g2 != null && read($h,$g2,alloc) && dtype($g2) == pacman$Grid
&&  ($f == pacman$Grid.left || $f == pacman$Grid.right || $f == pacman$Grid.top || $f == pacman$Grid.bottom )
&&  (read($h, $g1, $f) == $g2)
	==> reachable($h,$g1,$g2));
	// identity: not necessary 
  axiom (forall<alpha> $h: HeapType, $g1: ref ::
	$g1 != null && read($h,$g1,alloc) && dtype($g1) == pacman$Grid
	==> reachable($h,$g1,$g1)); 
  axiom (forall<alpha> $h: HeapType, $g1, $g2, $g3: ref, $f: Field alpha ::
	$g1 != null && read($h,$g1,alloc) && dtype($g1) == pacman$Grid
&&	$g2 != null && read($h,$g2,alloc) && dtype($g2) == pacman$Grid
&&	$g3 != null && read($h,$g3,alloc) && dtype($g3) == pacman$Grid
&&  reachable($h,$g1,$g2) && reachable($h,$g2,$g3)
	==> reachable($h,$g1,$g3));
  axiom (forall<alpha> $h: HeapType, $g1, $g2: ref, $f: Field alpha ::
	$g1 != null && read($h,$g1,alloc) && dtype($g1) == pacman$Grid
&&	$g2 != null && read($h,$g2,alloc) && dtype($g2) == pacman$Grid
&&  reachable($h,$g1,$g2)
	==> reachable($h,$g2,$g1));
	
const unique Pacman#ghost#INTERVAL: int;
 axiom Pacman#ghost#INTERVAL == 10;
const unique Pacman#ghost#MAXFRAME: int;
 axiom Pacman#ghost#MAXFRAME == 99;