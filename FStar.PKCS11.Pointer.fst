module FStar.PKCS11.Pointer

open FStar.Seq

noeq type pointer_t a' b' = 
	| NULL_PTR: pointer_t a' b'
	| Pointer_Object: t:Type -> a: t ->  pointer_t a' b'
	| FunctionPointer: (a : a' -> b: b')  -> pointer_t a' b'

type flags_t = 
	|Flags: seq bool -> flags_t