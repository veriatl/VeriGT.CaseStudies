
/* Metamodel */


const unique pacman$GameState: ClassName extends  complete;
const unique pacman$GameState.grids: Field ref;
const unique pacman$GameState.actions: Field ref;
const unique pacman$GameState.player: Field ref;
const unique pacman$GameState.ghost: Field ref;
const unique pacman$GameState.gems: Field ref;
const unique pacman$GameState.record: Field ref;
const unique pacman$GameState.STATE: Field int;


const unique pacman$Entity: ClassName extends  complete;
const unique pacman$Entity.id: Field int;

const unique pacman$Pacman: ClassName extends pacman$Entity complete;

const unique pacman$Grid: ClassName extends pacman$Entity complete;
const unique pacman$Grid.left: Field ref;
const unique pacman$Grid.right: Field ref;
const unique pacman$Grid.top: Field ref;
const unique pacman$Grid.bottom: Field ref;
const unique pacman$Grid.hasPlayer: Field ref;
const unique pacman$Grid.hasEnemy: Field ref;
const unique pacman$Grid.hasGem: Field ref;



const unique pacman$Ghost: ClassName extends pacman$Entity complete;

const unique pacman$Action: ClassName extends  complete;
const unique pacman$Action.FRAME: Field int;
const unique pacman$Action.DONEBY: Field int;
const unique pacman$Action.DIRECTION: Field int;

const unique pacman$Gem: ClassName extends pacman$Entity complete;

const unique pacman$Record: ClassName extends  complete;
const unique pacman$Record.FRAME: Field int;
const unique pacman$Record.SCORE: Field int;


  
function inRange(e: int, low:int, high:int):bool
{ low<=e && e<high }
  
// o1 is connected with o2 by link f on heap.


function isConnected(heap: HeapType, o1: ref, o2: ref, f: Field ref): bool
{  o1 !=null && read(heap, o1, alloc)
&& o2 !=null && read(heap, o2, alloc)
&& dtype(read(heap,o1,f)) == class._System.array
&& Seq#Length(Seq#FromArray(heap,read(heap,o1,f)))==1
&& Seq#Index(Seq#FromArray(heap,read(heap,o1,f)),0) == $Box(o2)
}  




// ASM-specific
const unique Asm: ref;
  axiom Asm != null;
const unique ASM#Links : Field (Set ref);
const unique Native$TransientLink: ClassName;



	// see org.eclipse.m2m.atl.engine.emfvm.lib.TransientLink
const unique TransientLink#source: Field (Map String ref);
const unique TransientLink#target: Field (Map String ref);
const unique TransientLink#rule: Field String;


// [mmName, className]
const classifierTable : [String, String] ClassName;
  axiom classifierTable[_P,_Ghost] == pacman$Ghost;
  axiom classifierTable[_Native,_Collection] == class._System.array;
 
 
 
 
 
const unique _Field$STATE: NameFamily; 
const unique _Field$FRAME: NameFamily; 
const unique _Field$DONEBY: NameFamily; 
const unique _Field$DIRECTION: NameFamily; 
const unique _Field$hasEnemy: NameFamily; 
const unique _Field$hasPlayer: NameFamily; 
const unique _Field$hasGem: NameFamily; 
const unique _Field$record: NameFamily; 
const unique _Field$SCORE: NameFamily; 





 axiom (FieldOfDecl(pacman$GameState, _Field$STATE) == pacman$GameState.STATE);
 axiom (FieldOfDecl(pacman$GameState, _Field$record) == pacman$GameState.record);
 axiom (FieldOfDecl(pacman$Action, _Field$FRAME) == pacman$Action.FRAME);
 axiom (FieldOfDecl(pacman$Record, _Field$FRAME) == pacman$Record.FRAME);
 axiom (FieldOfDecl(pacman$Record, _Field$SCORE) == pacman$Record.SCORE);
 axiom (FieldOfDecl(pacman$Action, _Field$DONEBY) == pacman$Action.DONEBY);
 axiom (FieldOfDecl(pacman$Action, _Field$DIRECTION) == pacman$Action.DIRECTION);
 axiom (FieldOfDecl(pacman$Grid, _Field$hasEnemy) == pacman$Grid.hasEnemy);
 axiom (FieldOfDecl(pacman$Grid, _Field$hasPlayer) == pacman$Grid.hasPlayer);
 axiom (FieldOfDecl(pacman$Grid, _Field$hasGem) == pacman$Grid.hasGem);
 
 
 
const unique _P: String;
const unique _Ghost: String;
const unique _Native: String;
const unique _Collection: String;
 
 