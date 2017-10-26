module FStar.PKCS11.Functions.General

open FStar.PKCS11.Pointer 
open FStar.PKCS11.Exception

let result = FStar.PKCS11.Exception.result

(*)
type args_CK_C_INITIALIZE a' b' c' d' e' = {
	createMutes : pointer_t a' result ; // option (unit -> mutex)
	destroyMutex :	pointer_t b' result ;
	lockMutex: pointer_t c' result;
	unlockMutex: pointer_t d' result;
	flags: flags_t;
	pReserved: pointer_t e' unit;
}

type args_CK_C_INITIALIZK a' b' c' d' e'  = {
	createMutes : pointer_t a' bool ; // option (unit -> mutex)
	destroyMutex :	pointer_t b' bool ;
	lockMutex: pointer_t c' bool;
	unlockMutex: pointer_t d' bool;
	flags: flags_t;
	pReserved: pointer_t e' bool;
}

type args_CK_C_INITIALIZA (ctx mutex_t:Type)  = {
	createMutes : pointer_t ctx mutex_t ; // option (unit -> mutex)
	destroyMutex :	pointer_t mutex_t unit ;
	lockMutex: pointer_t mutex_t unit;
	unlockMutex: pointer_t mutex_t unit;
	flags: flags_t;
	pReserved: pointer_t e' bool;
}

type args_CK_C_INITIALIZ3 a' b' c' d' e'  = {
	createMutes : pointer_t void_t void_t ; // option (unit -> mutex)
	destroyMutex :	pointer_t void_t void_t ;
	lockMutex: pointer_t void_t void_t;
	unlockMutex: pointer_t void_t void_t;
	flags: flags_t;
	pReserved: pointer_t void_t void_t;
}
*)
assume val void_star : Type
assume val null_ptr : void_star

noeq type args_CK_C_INITIALIZE  = {
	createMutes : option(void_star -> void_star); // option (unit -> mutex)
	destroyMutex :	option(void_star -> void_star) ;
	lockMutex: option(void_star -> void_star);
	unlockMutex: option(void_star -> void_star);
	flags: flags_t;
	pReserved: void_star;
}

val ck_C_INITIALIZE: args: option args_CK_C_INITIALIZE -> Tot result

let ck_C_INITIALIZE args = 
	Inl (true)
