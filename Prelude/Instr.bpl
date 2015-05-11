// -----------------------------------------------------
// -- Proof System for ASM Instruction Set -------------
// -----------------------------------------------------
  
  
function OpCode#Aux#InitStk(): Seq BoxType;
  axiom OpCode#Aux#InitStk() == (Seq#Empty(): Seq BoxType);
 
//Instr: push  
procedure OpCode#Push(stk: Seq BoxType, s: String) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(s));

  
//Instr: pushi  
procedure OpCode#Pushi(stk: Seq BoxType, i: int) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(i));  
  
//Instr: pushf  
procedure OpCode#Pushf(stk: Seq BoxType) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(false));

//Instr: pusht
procedure OpCode#Pusht(stk: Seq BoxType) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(true));
  
//Instr: pop 
procedure OpCode#Pop(stk: Seq BoxType) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-1);
  
//Instr: store
procedure OpCode#Store<T>(stk: Seq BoxType) returns(newStk: Seq BoxType, topVal: T);
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-1);
  ensures topVal == $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
  
//Instr: load
procedure OpCode#Load<T>(stk: Seq BoxType, v: T) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(v));
 
//Instr: Swap
procedure OpCode#Swap(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1)), Seq#Index(stk, Seq#Length(stk)-2));
 
//Instr: Dup
procedure OpCode#Dup(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 1;
  ensures newStk == Seq#Build(stk, Seq#Index(stk, Seq#Length(stk)-1));
 
//Instr: Dup_x1
procedure OpCode#DupX1(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Build(Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1)), Seq#Index(stk, Seq#Length(stk)-2)), Seq#Index(stk, Seq#Length(stk)-1));

  
//Instr: New, [compile mechanism]
/*
	assert Seq#Length(stk) >= 2;
	havoc _placehold;
    assume _placehold != null && !read($xHeap, _placehold, alloc) && dtype(_placehold) == 
	classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
					($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
	$xHeap := update($xHeap, _placehold, alloc, true);
	assume $IsGoodHeap($xHeap);
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(_placehold));
*/


// Instr: get  [compile mechanism]
/*
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($xHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _placeholder): Field (_infered)]));
*/
  

//Instr: set [compile mechanism]
/*
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
	
if(isCollection(FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _placeholder): Field (_infered))){
	havoc $newCol;
	assume dtype($newCol) == class._System.array;
	assume $newCol != null && read($xHeap, $newCol, alloc);
	assume Seq#FromArray($xHeap,$newCol) == Seq#Append(Seq#FromArray($xHeap, read($xHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _placeholder): Field (_infered))), Seq#FromArray($xHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));


	$xHeap := update($xHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
					FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _placeholder): Field (_infered), 
					$newCol
					);
	assume $IsGoodHeap($xHeap);
	stk := Seq#Take(stk, Seq#Length(stk)-2);	
}else{

	$xHeap := update($xHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
					FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _placeholder): Field (_infered), 
					$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	assume $IsGoodHeap($xHeap);
	stk := Seq#Take(stk, Seq#Length(stk)-2);
}
*/

//Instr: delete o [compile mechanism]
/*
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
$xHeap := update($xHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)), alloc, false);
stk := Seq#Take(stk, Seq#Length(stk)-1);
*/   
  


  
//Instr: add _Feature _o _v [compile mechanism], add _v to the end of _o._Feature
/*


var _o = $Unbox(Seq#Index(stk, Seq#Length(stk)-2));
var _v = $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
	
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;	
assert isNotField(_Feature);	// it is part of the semantics, but not handled at now, a field is a static value/initializer/rule

if(isCollection(FieldOfDecl(dtype(_o), _Feature): Field (_infered))){

	havoc $newCol;
	assume dtype($newCol) == class._System.array;
	assume $newCol != null && read($xHeap, $newCol, alloc);
	
	if(dtype(_v) == class._System.array){	// _v is collection, add to the end of _o._Feature
		assume Seq#FromArray($xHeap,$newCol) == Seq#Append(
		Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))), 
		Seq#FromArray($xHeap,_v));
	}else{	// is EObject
		assume Seq#FromArray($xHeap,$newCol) == Seq#Append(
		Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))), 
		Seq#Singleton(_v));
	}
	
	$xHeap := update($xHeap, _o, 
					FieldOfDecl(dtype(_o), _Feature): Field (_infered), 
					$newCol
					);
	
}else{
	assert !isSet(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)));
	assert _i == 0;
	$xHeap := update($xHeap, _o, 
					FieldOfDecl(dtype(_o), _Feature): Field (_infered), 
					_v);
	assert isSet(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)));
}

assume $IsGoodHeap($xHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);



*/     







//Instr: insert _Feature, _o, _v, _i [compile mechanism] add _v to the index _i of _o._Feature
/*

var _o = $Unbox(Seq#Index(stk, Seq#Length(stk)-3));
var _v = $Unbox(Seq#Index(stk, Seq#Length(stk)-2));
var _i = $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
	
assert Seq#Length(stk) >= 3;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-3)) != null;	
assert isNotField(_Feature);	// it is part of the semantics, but not handled at now, a field is a static value/initializer/rule

if(isCollection(FieldOfDecl(dtype(_o), _Feature): Field (_infered))){
	assert _i < Seq#Length(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))));
	havoc $newCol;
	assume dtype($newCol) == class._System.array;
	assume $newCol != null && read($xHeap, $newCol, alloc);
	
	if(dtype(_v) == class._System.array){	// _v is collection, add to the end of _o._Feature
		assume Seq#FromArray($xHeap,$newCol) == 
		Seq#Append(
			Seq#Append(
				Seq#Take(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))), _i-1),
				Seq#FromArray($xHeap,_v)),
			Seq#Drop(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))), _i-1)
		);
		
		
	}else{	// is EObject
		assume Seq#FromArray($xHeap,$newCol) == 
		Seq#Append(
			Seq#Append(
				Seq#Take(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))), _i-1),
				Seq#Singleton(_v)),
			Seq#Drop(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))), _i-1)
		);
	}
	
	$xHeap := update($xHeap, _o, 
					FieldOfDecl(dtype(_o), _Feature): Field (_infered), 
					$newCol
					);

}else{
	assert !isSet(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)));
	assert _i == 0;
	$xHeap := update($xHeap, _o, 
					FieldOfDecl(dtype(_o), _Feature): Field (_infered), 
					_v);
	assert isSet(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)));
}

assume $IsGoodHeap($xHeap);
stk := Seq#Take(stk, Seq#Length(stk)-3);
*/  

 
//Instr: remove Feature obj val  [compile mechanism]
/*

var _o = $Unbox(Seq#Index(stk, Seq#Length(stk)-2));
var _v = $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
	
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;	
assert isNotField(_Feature);	// it is part of the semantics, but not handled at now, a field is a static value/initializer/rule

if(isCollection(FieldOfDecl(dtype(_o), _Feature): Field (_infered))){

	havoc $newCol;
	assume dtype($newCol) == class._System.array;
	assume $newCol != null && read($xHeap, $newCol, alloc);
	
	// remove v from _o._f
	if(dtype(_v) == class._System.array){	
		assume (forall i: int :: 0<=i && i<Seq#Length(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)))) ==>
			Seq#Contains(Seq#FromArray($xHeap),_v, Seq#Index(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))),i)) ==>
			!Seq#Contains(Seq#FromArray($xHeap,$newCol), Seq#Index(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))),i)));
	}else{	// is EObject
		assume Seq#Contains(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)), _v) ==>
			(forall i: int :: 0<=i && i<Seq#Length(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)))) ==>
				Seq#Index(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))),i) == _v ==>
					Seq#FromArray($xHeap,$newCol) == 
					Seq#Append(
						Seq#Take(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))),i-1)
						Seq#Drop(Seq#FromArray($xHeap, read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered))),i)
					));
	}
	
	$xHeap := update($xHeap, _o, 
					FieldOfDecl(dtype(_o), _Feature): Field (_infered), 
					$newCol
					);
	assume $IsGoodHeap($xHeap);
}else{
	if(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)) == null)
	{
		if(_v == null){
			$xHeap := ...	// set to defult, most likely null
			assume $IsGoodHeap($xHeap);
			assume !isSet(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)));
		}
	}else{
		if(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)) == _v){
			$xHeap := ... 	// set to defult
			assume $IsGoodHeap($xHeap);
			assume !isSet(read($xHeap, _o, FieldOfDecl(dtype(_o), _Feature): Field (_infered)));
		}
	}

	
}


stk := Seq#Take(stk, Seq#Length(stk)-2);




*/      

   


  
// Instr: findme
procedure OpCode#Findme(stk: Seq BoxType) returns(newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), 
							  $Box(classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
												   ($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)]));

// Instr: getASM  
procedure OpCode#GetASM(stk: Seq BoxType) returns(newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(Asm));
  
  
  
  
// Instr: NOT
procedure OpCode#Not(stk: Seq BoxType) returns(newStk: Seq BoxType);
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(!$Unbox(OpCode#Top(stk))));
  
  
procedure OpCode#FindType(stk: Seq BoxType, modelName:String, typeName: String) returns(newStk: Seq BoxType);  
  ensures newStk == Seq#Build(stk, $Box(classifierTable[modelName, typeName]));


  
