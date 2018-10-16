module PKCS11.Spec13_EC
open FStar.UInt32
open FStar.Seq
open FStar.Option

open FStar.Seq.Base
open FStar.Seq.Properties

open PKCS11.Spec.Lemmas

(* #set-options "--z3rlimit 200 --lax"  *)

#set-options "--z3rlimit 100 --detail_errors"

type _CK_MECHANISM_TYPE = nat

type _CK_ULONG = FStar.UInt32.t

type _CK_ATTRIBUTE_TYPE = FStar.UInt32.t

type _CK_BYTE = FStar.UInt8.t


type _CK_OBJECT_CLASS = _CK_ULONG

type _CK_KEY_TYPE_T = _CK_ULONG

type _CK_OBJECT_HANDLE = _CK_ULONG

type _CK_EXCEPTION = _CK_ULONG

type _CK_FLAGS_T = _CK_ULONG
type _CK_SESSION_HANDLE = _CK_ULONG

type _CKS_MECHANISM_INFO = 
	| MecInfo: flags: seq _CK_ULONG -> _CKS_MECHANISM_INFO	

(*

val count_lemma: #a: eqtype -> s: seq a -> f: (a -> Tot bool){count f s = 1} -> 
    Lemma(
      (ensures ((exists (i: nat). i< Seq.length s ==> f (Seq.index s i)) /\
      (forall (i: nat).  i< Seq.length s ==> (forall (j: nat). ((j< Seq.length s) && (i<>j)) ==> f (Seq.index s i) == false))))
)

let count_lemma #a s f = 
  if Seq.length s = 0 then ()
  else if Seq.length s = 1 then ()
  else if f(head s) then 
    let a = head s in 
    let b = tail s in 
    assert(f a);
    assert(count f b = 0);
    count0Lemma b f;
    assert(forall (i: nat). i<Seq.length b ==> f (Seq.index b i) == false);
    assert(equal (append (Seq.create 1 a)  b) s);
    assert(forall (i: nat). (i< Seq.length s && i<>0) ==>  f (Seq.index s i) == false)
  else 
  admit()

*)

(*
val test_one_element: #a: eqtype -> f: (a -> Tot bool) -> 
    f2: (a -> Tot bool) -> 
    s: seq a{
        (
            exists (i: nat). i < Seq.length s ==> f (Seq.index s i) /\ f2 (Seq.index s i)
        )
            /\ countT f2 s = 1
        } ->       
    Tot unit


assume val countTLemma: #a: eqtype -> s: seq a -> f2: (a -> Tot bool) {countT f2 s = 1} -> Lemma
    (ensures
    (
      (exists (i: nat). i< Seq.length s ==> f2 (Seq.index s i)) /\
      (forall (k: nat {k < Seq.length s}). f2 (Seq.index s k) ==>
      (forall (j: nat {j < Seq.length s /\ k <> j}).  f2 (Seq.index s j) = false))
    ))
  (decreases (Seq.length s))



val count2: #a: eqtype -> s: seq a -> f1: (a -> Tot bool) {countT f1 s = 1}  -> 
  f2: (a -> Tot bool){exists (i: nat). i< Seq.length s ==> f1 (Seq.index s i) && f2 (Seq.index s i)} -> 
  i: nat {i< Seq.length s} -> 
  Tot a

*)     

(*
val lemmaAppendFunction: #a: eqtype -> f: (a -> Tot bool)  -> 
    s: seq a{forall (i: nat{i < Seq.length s}). f (Seq.index s i) == true} 
    -> el: a{f el == true} -> 
    Lemma(ensures(let sUpdated = Seq.append s (Seq.create 1 el) in 
    forall (i: nat{i< Seq.length sUpdated}). f (Seq.index sUpdated i) == true))



let lemmaAppendFunction  #a f s el = ()
*)

type attributeSpecification  = 
	(* | CKA_CLASS: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x0ul} -> pValue: seq _CK_OBJECT_CLASS{length pValue = 1} ->  attributeSpecification *)
	| CKA_CLASS: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x0ul} -> pValue: _CK_OBJECT_CLASS->  attributeSpecification
	| CKA_TOKEN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x1ul}->  pValue: seq bool-> attributeSpecification
	| CKA_PRIVATE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x2ul} ->  pValue: seq bool-> attributeSpecification
	| CKA_LABEL: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x3ul} ->  pValue: seq _CK_ULONG->a: attributeSpecification
	| CKA_APPLICATION:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x10ul} ->pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_VALUE:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x11ul} ->pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_OBJECT_ID:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x12ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_CERTIFICATE_TYPE:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x80ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_ISSUER:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x81ul} ->pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_SERIAL_NUMBER: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x82ul}-> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_KEY_TYPE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x100ul} -> pValue: _CK_KEY_TYPE_T-> attributeSpecification
	| CKA_ID: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x102ul} -> pValue: seq _CK_ULONG->a: attributeSpecification
	| CKA_SENSITIVE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x103ul} ->pValue: seq bool -> attributeSpecification
	| CKA_ENCRYPT: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x104ul} ->pValue: (seq bool) ->a: attributeSpecification
	| CKA_DECRYPT: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x105ul}->pValue: seq bool ->a: attributeSpecification
	| CKA_WRAP: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x106ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_UNWRAP: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x107ul} -> pValue: seq _CK_ULONG->a: attributeSpecification
	| CKA_SIGN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x108ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_VERIFY: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x10Aul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_VALUE_LEN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x161ul} -> pValue: seq _CK_ULONG -> attributeSpecification
	| CKA_STUB: typeId: _CK_ATTRIBUTE_TYPE{typeId = 0x999ul} -> pValue: seq bool{length pValue = 1} -> attributeSpecification
	(* Elliptic curve params *)
	| CKA_EC_PARAMS: typeId: _CK_ATTRIBUTE_TYPE{typeId = 0x180ul} -> pValue: seq _CK_BYTE -> attributeSpecification
	| CKA_EC_POINT: typeId: _CK_ATTRIBUTE_TYPE{typeId = 0x181ul} -> pValue: seq _CK_BYTE -> attributeSpecification


type _object = 
	|O: 
		identifier: _CK_ULONG -> 
		attrs: seq attributeSpecification -> 
		_object

val classAttribute : a: _object -> Tot (a: option attributeSpecification{Some? a  ==> (let a = (match a with Some a -> a) in  CKA_CLASS? a)}) 		

let classAttribute a = 
	let attrs = a.attrs in 
	find_l (fun x -> CKA_CLASS? x) attrs

(* Key structure *)

let _CKO_PUBLIC_KEY = 2ul
let _CKO_PRIVATE_KEY = 3ul
let _CKO_SECRET_KEY = 4ul

type key = 
	|SecretKey: element: _object{
		(let elementAttributes = classAttribute element in Some? elementAttributes
			&& 
			(
				let attributeSpecifyingClass = (match elementAttributes with Some a -> a) in 
				let valueForAttributeSpecifyingClass = CKA_CLASS?.pValue attributeSpecifyingClass
				in valueForAttributeSpecifyingClass = _CKO_SECRET_KEY
			)
		)} 
		-> key 
	| PublicKey: element: _object
		{
			(let elementAttributes = classAttribute element in Some? elementAttributes &&
			(
				let attributeSpecifyingClass = (match elementAttributes with Some a -> a) in 
				let valueForAttributeSpecifyingClass = CKA_CLASS?.pValue attributeSpecifyingClass in 
				valueForAttributeSpecifyingClass = _CKO_PUBLIC_KEY
			)
		)}	
		-> key
	| PrivateKey: element: _object
		{
			(let elementAttributes = classAttribute element in Some? elementAttributes &&
			(
				let attributeSpecifyingClass = (match elementAttributes with Some a -> a) in 
				let valueForAttributeSpecifyingClass = CKA_CLASS?.pValue attributeSpecifyingClass in 
				valueForAttributeSpecifyingClass = _CKO_PRIVATE_KEY
			)
		)} 
		-> key		

val keyGetObject: k: key -> Tot _object

let keyGetObject k = 
    match k with 
      |SecretKey e -> e 
      |PublicKey e -> e
      |PrivateKey e -> e
      

(*/ Key structure *)

(* TODO: what's it used for? *)
type temporalStorage = 
	|Element: dat: seq FStar.UInt8.t * _CK_ULONG -> temporalStorage

type mechanismSpecification = 
	| Mechanism: mechanismID: _CK_MECHANISM_TYPE -> 
		pParameters: seq FStar.UInt8.t -> 
		mechanismSpecification

let _SubSessionInit = 0ul
let _SubSessionUpd = 1ul

let _SubSessionVerifyInit = 2ul
let _SubSessionVerifyUpd = 3ul


type subSession (k: seq key) (m: seq mechanismSpecification) = 
	|Signature: id: _CK_SESSION_HANDLE -> 
		state: _CK_ULONG{state = _SubSessionInit \/ state = _SubSessionUpd} ->
		pMechanism: _CK_MECHANISM_TYPE{exists (a: nat {a < Seq.length m}). let mechanism = Seq.index m a in 
			mechanism.mechanismID = pMechanism} ->
		keyHandler: _CK_OBJECT_HANDLE{Seq.length k > v keyHandler}-> 
		temp: option temporalStorage -> 
		subSession k m
	|Verify : 	id: _CK_SESSION_HANDLE -> 
		state: _CK_ULONG{state = _SubSessionVerifyInit \/ state = _SubSessionVerifyUpd} ->
		pMechanism: _CK_MECHANISM_TYPE{exists (a: nat {a < Seq.length m}). let mechanism = Seq.index m a in 
			mechanism.mechanismID = pMechanism} ->
		keyHandler: _CK_OBJECT_HANDLE {Seq.length k > v keyHandler}-> 
		temp: option temporalStorage -> 
		subSession k m


val subSessionGetID: #ks: seq key -> #ms: seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_SESSION_HANDLE

let subSessionGetID #ks #ms s = 
	match s with 
	|Signature a _ _ _ _ -> a 
	|Verify a _ _ _  _  -> a


val subSessionGetState: #ks: seq key -> #ms : seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_ULONG

let subSessionGetState #ks #ms s = 
	match s with
	| Signature _ b _ _ _ -> b
	| Verify _ b _ _ _  -> b


val subSessionSetState: #ks: seq key -> #ms: seq mechanismSpecification -> s: subSession ks ms -> state : _CK_ULONG 
	{if Signature? s then state =  _SubSessionInit \/ state = _SubSessionUpd 
	else if Verify? s then state = _SubSessionVerifyInit \/ state = _SubSessionVerifyUpd 
	else true} -> 
		Tot (r: subSession ks ms{subSessionGetState r = state /\ 
			(if Signature? s then Signature? r 
			  else if Verify? s then Verify? r else true) /\
			(match s with 
				|Signature a _ c d e ->
					begin match r with 
						|Signature a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
					end	
				|Verify a _ c d e ->
					begin match r with 
						|Verify a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
					end	
			)
		})

let subSessionSetState #ks #ms s state = 
let a = 	match s with 
	|Signature a b c d e -> Signature a state c d e 
	|Verify a b c d e -> Verify a state c d e in 	 a


val subSessionGetStorage: #ks: seq key -> #ms : seq mechanismSpecification -> s: subSession ks ms -> Tot (option temporalStorage)

let subSessionGetStorage #ks #ms s = 
	match s with 
	|Signature _ _ _ _ e -> e 
	|Verify _ _ _ _ e -> e


val subSessionSetStorage: #ks: seq key -> #ms: seq mechanismSpecification -> s: subSession ks ms -> storage: option temporalStorage -> 
Tot (r: subSession ks ms {subSessionGetStorage r = storage /\
  (if Signature? s then Signature? r 
  else if Verify? s then Verify? r 
  else true) /\
  (match s with 
    |Signature a b c d e ->
	begin match r with 
	  |Signature a1 b1 c1 d1 e1 -> a = a1 /\ b = b1/\ c = c1 /\ d = d1 
	end	
    |Verify a b c d e ->
	begin match r with 
	  |Verify a1 b1 c1 d1 e1 -> a = a1 /\b = b1 /\ c = c1 /\ d = d1 
	end)
}
)

let subSessionSetStorage #ks #ms s storage = 
	match s with 
	|Signature a b c d e -> Signature a b c d storage
	|Verify a b c d e -> Verify a b c d storage


val subSessionGetMechanism: #ks: seq key -> #ms: seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_MECHANISM_TYPE

let subSessionGetMechanism #ks #ms s = 
	match s with 
	|Signature _ _  c _ _ -> c
	|Verify _ _ c _ _ -> c


val subSessionGetKeyHandler: #ks: seq key -> #ms: seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_OBJECT_HANDLE

let subSessionGetKeyHandler #ks #ms s = 
	match s with 
	|Signature _ _ _ d _ -> d 
	|Verify _ _ _ d _ -> d


type device = 
	|Device: 
		keys: seq key ->
		mechanisms: seq mechanismSpecification -> 
		objects: seq _object -> 
		subSessions: seq (subSession keys mechanisms) -> 
	device
		

(* Internal data *)
assume val mechanismGetFlags: d: device -> mechanismID: _CK_MECHANISM_TYPE -> Tot _CK_FLAGS_T

assume val isFlagKeyGeneration: flags: _CK_FLAGS_T -> Tot bool

assume val isFlagSign: flags: _CK_FLAGS_T -> Tot bool

assume val isFlagVerify: flags: _CK_FLAGS_T -> Tot bool

assume val isAttributeLocal: attrs: seq attributeSpecification -> Tot bool

assume val isAttributeSecretKey: attrs: seq attributeSpecification -> Tot bool

assume val isAttributeSign: attrs : seq attributeSpecification -> Tot bool

assume val isAttributeVerify: attrs: seq attributeSpecification -> Tot bool


type exception_t = _CK_ULONG 

type result 'a = either 'a exception_t


(* Takes too long*) 
assume val isPresentOnDevice_: d: device -> pMechanism: _CK_MECHANISM_TYPE -> 
	counter: nat{counter < Seq.length d.mechanisms} -> 
	Tot (r: bool {r = true ==> (exists (a: nat{a < Seq.length d.mechanisms}). 
				let m = Seq.index d.mechanisms a in m.mechanismID = pMechanism) /\ 
			(Some? (find_l (fun x -> x.mechanismID = pMechanism) d.mechanisms))
		}
	)
	(decreases(Seq.length d.mechanisms - counter))
(*
let rec isPresentOnDevice_ d pMechanism counter =
	let m = Seq.index d.mechanisms counter in 
	if (m.mechanismID = pMechanism) then 
		(
			let f = (fun x -> x.mechanismID = pMechanism) in 
			let a, b' = Seq.split d.mechanisms counter in 
			let elementCounter, b = Seq.split b' 1 in 
			(*	assert(Some? (find_l f  elementCounter));*)
			find_append_some elementCounter b f; 
(*				assert(equal (Seq.append elementCounter b) b'); *)
			find_append_some_s2 a b' f;
			  assert(equal (Seq.append a b') d.mechanisms);	
			true
		)
	else if counter+1 = Seq.length d.mechanisms then false 
	else 
		isPresentOnDevice_ d pMechanism (counter +1) 

*)
val isPresentOnDevice: d: device -> pMechanism: _CK_MECHANISM_TYPE -> 
	Tot (r: bool {r = true ==> (exists (a: nat{a < Seq.length d.mechanisms}). 
				let m = Seq.index d.mechanisms a in m.mechanismID = pMechanism) /\ 
			(Some? (find_l (fun x -> x.mechanismID = pMechanism) d.mechanisms))
		}
	)

let isPresentOnDevice d pMechanism =
	if Seq.length d.mechanisms = 0 then false else
	isPresentOnDevice_ d pMechanism 0


val mechanismGetFromDevice: d: device -> pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism = true} -> 
	Tot (m: mechanismSpecification{m.mechanismID = pMechanism})

let mechanismGetFromDevice d pMechanism = 
	let mechanisms = d.mechanisms in 
	let m = find_l (fun x -> x.mechanismID = pMechanism) mechanisms in 
	match m with 
	Some m -> m


assume val checkedAttributes: pTemplate : seq attributeSpecification -> Tot bool


assume val keyGeneration: mechanismID: mechanismSpecification -> pTemplate: seq attributeSpecification ->
	Tot (either (k: key 
			{
			let obj = match k with |SecretKey o -> o |PublicKey o -> o |PrivateKey o -> o in 
			let attrs = obj.attrs in isAttributeLocal attrs &&  isAttributeSecretKey attrs}) exception_t)



val sessionEqual: #ks: seq key -> #ms: seq mechanismSpecification -> #ks1: seq key -> #ms1 : seq mechanismSpecification -> 
	s: subSession ks ms -> s1 : subSession ks1 ms1 -> Tot Type0

let sessionEqual #ks #ms #ks1 #ms1 s s1 = 
	match s with 
	|Signature a b c d e -> 
		begin match s1 with 
			|Signature a1 b1 c1 d1 e1 -> a == a1 /\ b == b1 /\ c == c1 /\ d == d1 /\ e == e1
			| _ -> False
		end
	|Verify a b c d e -> 	
		begin 
			match s1 with
			| Verify a1 b1 c1 d1 e1 -> a == a1 /\ b == b1 /\ c == c1 /\ d == d1 /\ e == e1
			| _ -> False

		end	


val updateSession_: d: device -> 
	s: subSession d.keys d.mechanisms ->
 	ks: seq key
 		{Seq.length ks >= Seq.length d.keys \/ v (subSessionGetKeyHandler s) < Seq.length ks} ->
	ms: seq mechanismSpecification{ms == d.mechanisms} -> 
	Tot (r: subSession ks ms
		{Signature? s ==> Signature? r /\ Verify? s ==> Verify? r /\ sessionEqual s r})	

let updateSession_ d s ks ms = 
	match s with 
	| Signature a b c d e -> 
		let (a: subSession ks ms) = Signature a b c d e in a
	| Verify a b c d e -> 
		let (a: subSession ks ms) = Verify a b c d e in a		


let le_lt_plus_one (counter:nat) : Lemma (forall (i:nat). i <= counter <==> i < counter + 1) = ()

let forall_domain_refine #a (p:a -> Type0) (q:a -> Type0) : Lemma (requires (forall (i:a{p i}). q i)) (ensures (forall (i:a). p i ==> q i)) = ()


val lemma_forall_because_fstar_doesnot_work: 
    counter : nat ->  f: (nat -> Type0) ->
    Lemma
    (requires(forall (i: nat).  i <= counter ==> f i))
    (ensures(forall (i: nat). i < (counter + 1) ==> f i))
    
let lemma_forall_because_fstar_doesnot_work counter f = ()

val _updateSession: d: device ->  ks: seq key -> 
	ms: seq mechanismSpecification{ms == d.mechanisms} -> 
	s: seq (subSession d.keys d.mechanisms)
		{
		forall (i: nat). i < Seq.length s ==> (let elem = Seq.index s i in 
				Seq.length ks >= Seq.length d.keys \/ v (subSessionGetKeyHandler elem) < Seq.length ks)
		} ->
	counter: nat {counter < Seq.length s}->
	alreadySeq: seq (subSession ks ms) 
		{Seq.length alreadySeq = counter /\
			(
				forall (i: nat).  i < Seq.length alreadySeq ==> 
					(sessionEqual (index s i) (index alreadySeq i))
			)
	} -> 
	Tot (snew: (seq (subSession ks ms))
		{Seq.length s = Seq.length snew /\
			(forall (i: nat). i < Seq.length s ==> sessionEqual (index s i) (index snew i))
		}
	)
	(decreases (Seq.length s - Seq.length alreadySeq))


#set-options "--z3rlimit 150 --detail_errors"

let rec _updateSession d ks ms s counter alreadySeq = 
	let element = Seq.index s counter in 
	let updatedElement = updateSession_ d element ks ms in 
	let updatedSeq = Seq.append alreadySeq (Seq.create 1 updatedElement) in 
	if Seq.length s = Seq.length updatedSeq	then 
	   (
	     assert(forall (i: nat). i < counter ==> sessionEqual (index s i) (index updatedSeq i));
	     assert(forall (i: nat). i <= counter ==> sessionEqual (index s i) (index updatedSeq i));
	     updatedSeq
	  )
	else 
		(
		   assert(forall (i: nat). i < counter ==> sessionEqual (index s i) (index updatedSeq i));
		   assert(forall (i: nat). i <= counter ==> sessionEqual (index s i) (index updatedSeq i));
		   assert(Seq.length s > counter +1 ); 
			_updateSession d ks ms s (counter + 1) updatedSeq
		)


#set-options "--z3rlimit 50 --detail_errors"

val updateSession: d: device ->  ks: seq key -> 
	ms: seq mechanismSpecification{ms == d.mechanisms} -> 
	s: seq (subSession d.keys d.mechanisms)
	{
	  forall (i: nat). i < Seq.length s ==> (let elem = Seq.index s i in 
			Seq.length ks >= Seq.length d.keys \/ v(subSessionGetKeyHandler elem) < Seq.length ks)
	} ->
	Tot (snew: (seq (subSession ks ms))
		{
			Seq.length s = Seq.length snew /\ 
			(forall (i: nat). i < Seq.length s ==> sessionEqual (index s i) (index snew i))
		}
	)
 
let updateSession d ks ms s = 
	if Seq.length s = 0 then 
		Seq.createEmpty 
	else	
	_updateSession d ks ms s 0 (Seq.createEmpty)

(* Modifies Section*)
val modifies0: dBefore: device -> dAfter: device -> Tot Type0

let modifies0 dBefore dAfter = 
  let keysPrevious, mechanismsPrevious,  objectsPrevious, subSessionsPrevious = dBefore.keys, dBefore.mechanisms, dBefore.objects, dBefore.subSessions in 
  let keysNew, mechanismsNew, objectsNew, subSessionsNew = dAfter.keys, dAfter.mechanisms, dAfter.objects, dAfter.subSessions in keysPrevious == keysNew /\
  mechanismsPrevious == mechanismsNew /\
  objectsPrevious == objectsNew /\
  Seq.length dBefore.subSessions = Seq.length dAfter.subSessions /\
  (forall (i: nat). i < Seq.length dBefore.subSessions ==> sessionEqual (index dBefore.subSessions i) (index dAfter.subSessions i))



val modifiesKeysM: dBefore: device -> dAfter: device{Seq.length dBefore.keys + 1 = Seq.length dAfter.keys /\ Seq.length dBefore.subSessions = Seq.length dAfter.subSessions} -> 
	i: _CK_OBJECT_HANDLE{v i < Seq.length dAfter.keys} -> Tot Type0

let modifiesKeysM dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let i = v i in 
	let keysBeforeA, keysBeforeB = Seq.split dBefore.keys i in 
	let keysAfterA, key_keysAfterB = Seq.split dAfter.keys i in 	
	let key, keysAfterB = Seq.split key_keysAfterB 1 in 
	mechanismsPrevious == mechanismsNew /\
	keysBeforeA == keysAfterA /\ keysBeforeB = keysAfterB /\
	objectsPrevious == objectsNew /\ 
	(forall (i: nat). i < Seq.length dBefore.subSessions ==> sessionEqual (index dBefore.subSessions i) (index dAfter.subSessions i))



val modifiesSessionsM: dBefore: device -> dAfter : device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions +1} -> 
	i: nat{i < Seq.length dBefore.subSessions} -> Tot Type0

let modifiesSessionsM dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, sessionsAfterB = Seq.split dAfter.subSessions i in 
	mechanismsPrevious == mechanismsNew /\
	keysPrevious == keysNew /\ 
	objectsPrevious == objectsNew /\
	(forall (i: nat{i < Seq.length sessionsBeforeA}). sessionEqual (index sessionsBeforeA i) (index sessionsAfterA i))/\
	(forall (i: nat{i < Seq.length sessionsBeforeB}). sessionEqual (index sessionsBeforeB i) (index sessionsAfterB i))

(* modifies Sessions equal stands for the:
the number of sessions was stayed the same and 
there was a change only in the session number i*)
val modifiesSessionsE: dBefore: device -> dAfter: device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions} ->
	i: nat {i < Seq.length dBefore.subSessions} -> Tot Type0

let modifiesSessionsE dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, session_sessionAfterB = Seq.split dBefore.subSessions i in 
	let _, sessionsAfterB = Seq.split session_sessionBeforeB 1 in 
	mechanismsPrevious == mechanismsNew /\
	keysPrevious == keysNew /\
	objectsPrevious == objectsNew /\
	(forall (i: nat{i < Seq.length sessionsBeforeA}). sessionEqual (index sessionsBeforeA i) (index sessionsAfterA i))/\
	(forall (i: nat{i < Seq.length sessionsBeforeB}). sessionEqual (index sessionsBeforeB i) (index sessionsAfterB i))


(* Predicate Section*)

let predicateSessionVerify hSession = (fun #p1 #p2 (x: subSession p1 p2) -> Verify? x && subSessionGetID x = hSession)
let predicateSessionSignature hSession = (fun #p1 #p2 (x:subSession p1 p2) -> Signature? x && subSessionGetID x = hSession)

val lemma_predicateSignatureForAll: hSession: _CK_SESSION_HANDLE -> Lemma 
	(ensures (
		let f = predicateSessionSignature hSession in 
		forall (ks1:seq key) (ms1: seq mechanismSpecification) 
		(ks2: seq key) (ms2: seq mechanismSpecification) 
		(s: subSession ks1 ms1) (s2: subSession ks2 ms2). 
		Signature? s == Signature? s2 /\ subSessionGetID s == subSessionGetID s2 ==> f s == f s2)
	)

let lemma_predicateSignatureForAll hSession = ()

let maximum_keys = 4294967296

#set-options "--z3rlimit 50 --detail_errors"


val deviceUpdateKey: d: device{let keysInDevice = d.keys in Seq.length keysInDevice < maximum_keys -1} -> newKey: key -> Tot (resultDevice: device
	{
		Seq.length resultDevice.keys = Seq.length d.keys + 1 /\
		Seq.length d.subSessions = Seq.length resultDevice.subSessions
	} &
	(handler: _CK_OBJECT_HANDLE
		{
		  let v_handler = v handler in 
		  v_handler < Seq.length resultDevice.keys/\ 
		  Seq.index resultDevice.keys v_handler = newKey /\
		  modifiesKeysM d resultDevice handler
		}
	))

let deviceUpdateKey d newKey = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let newKey = Seq.create 1 newKey in 
	let keysNew = Seq.append keysPrevious newKey in
	let handler = Seq.length keysNew -1 in 
		lemma_append keysPrevious newKey;
	let s = d.subSessions in 
	let sessionsUpdated =  updateSession d keysNew mechanismsPrevious s in
	let resultDevice = Device keysNew mechanismsPrevious objectsPrevious sessionsUpdated in 
	let intvalue = uint_to_t handler in 
	(|resultDevice, intvalue|)


assume val deviceRemoveSession: #ks: seq key -> #ms: seq mechanismSpecification ->  hSession : _CK_SESSION_HANDLE -> 
	f: (#ks: seq key -> #ms: seq mechanismSpecification -> subSession ks ms -> bool) -> 
	d: device{countF f d.subSessions = 1} ->
	Tot (resultDevice: device
		{
			countF f resultDevice.subSessions  = 0 /\
			Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1  /\
			(
				let indexOfSessionToDelete = seq_getIndexF d.subSessions f in 
				modifiesSessionsM d resultDevice indexOfSessionToDelete
			)
		}
	)	

#set-options "--z3rlimit 150 --detail_errors --hint_info"
(*
let deviceRemoveSession #ks #ms hSession f d = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionsNew = seq_remove sessionsPrevious f in 
		seq_remove_lemma_count_of_deleted sessionsPrevious f;
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsNew in 
	let i = seq_getIndex2 f d.subSessions in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split d.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, sessionsAfterB = Seq.split newDevice.subSessions i in 
		seq_remove_unchanged sessionsPrevious f;
		
		assert (count f newDevice.subSessions = 0);
		assert (Seq.length d.subSessions = Seq.length newDevice.subSessions +1);
		assert (let indexOfSessionToDelete = seq_getIndex2 f d.subSessions in 
		  modifiesSessionsM d newDevice indexOfSessionToDelete);
	newDevice
*)

(* Takes a device with all the sessions and tells that the only thing that was changed is the session 
that satisfies the function f. For the function that satisfies f the status is the 'updated' now
*) 

#set-options "--z3rlimit 50 --detail_errors"

val find_if_more_than_one: #a: eqtype -> f: (a -> bool) -> s: seq a{countF f s = 1} -> 
    Tot (r:a{f r}) 

let find_if_more_than_one #a f s = 
    let toChange = find_l f s in  countMore0IsSome s f;
     match toChange with |Some a -> a 
    

val deviceUpdateSessionChangeStatus: #ks : seq key -> #ms : seq mechanismSpecification -> 
	f: (#ks: seq key -> #ms: seq mechanismSpecification -> subSession ks ms -> bool)
	{
	      forall (ks1:seq key) (ms1: seq mechanismSpecification) 
		(ks2: seq key) (ms2: seq mechanismSpecification) 
		(s: subSession ks1 ms1) (s2: subSession ks2 ms2). 
		(
		Signature? s = Signature? s2 /\
		Verify? s = Verify? s2 /\
		subSessionGetID s == subSessionGetID s2) ==> (f s == f s2)
	}->
	d: device {countF (f #d.keys #d.mechanisms) d.subSessions = 1}  -> 
	Tot (resultDevice: device
	{ 
	  countF (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions = 1 /\
	  Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
	  (
	    let s = find_if_more_than_one (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions in 
	    let sessionIndex = seq_getIndexF d.subSessions (f #d.keys #d.mechanisms)  in 
	    let previousSession = find_if_more_than_one (f #d.keys #d.mechanisms) d.subSessions in 
		Signature? s ==> subSessionGetState s == _SubSessionUpd/\
		Verify? s ==> subSessionGetState s == _SubSessionVerifyUpd/\
		subSessionGetStorage s == subSessionGetStorage previousSession/\
		subSessionGetMechanism s == subSessionGetMechanism previousSession /\
		subSessionGetKeyHandler s == subSessionGetKeyHandler previousSession/\
		modifiesSessionsE d resultDevice sessionIndex
	  )
	}
    )	
    
#reset-options   


#set-options "--z3rlimit 200 --detail_errors --initial_fuel 2"

assume val lemFindWith2Funcs: #a: eqtype -> s: seq a -> f1: (a -> Tot bool) -> f2: (a -> Tot bool)
       {
	 countF f1 s = 1 /\ 
	 (exists(n: nat). n< Seq.length s ==> f1 (Seq.index s n) /\ f2 (Seq.index s n))
	} -> 
    Lemma((ensures(let e = find_if_more_than_one f1 s in f2 e)))


let deviceUpdateSessionChangeStatus #ks #ms f d = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionToChange = find_if_more_than_one (f #d.keys #d.mechanisms) sessionsPrevious in 
	  assert((f #d.keys #d.mechanisms) sessionToChange);
	let sessionChanged = subSessionSetState sessionToChange
	  (match sessionToChange with 
	    |Signature _ _ _ _ _ -> _SubSessionUpd
	    |Verify _ _ _ _ _  -> _SubSessionVerifyUpd) in
	    assert(subSessionGetID sessionChanged == subSessionGetID sessionToChange);
	    assert((f #d.keys #d.mechanisms) sessionChanged == (f #d.keys #d.mechanisms) sessionToChange);
	    assert((f #d.keys #d.mechanisms) sessionChanged);
	let sessionsChanged = Seq.create 1 sessionChanged in 
	    miniLemmaCount (f #d.keys #d.mechanisms) sessionChanged;
	    (*assert(countF (f #d.keys #d.mechanisms) sessionsChanged = 1);*)
	let sessionsNew = seq_remove sessionsPrevious (f #keysPrevious #mechanismsPrevious) in 
	    seq_remove_lemma_count_of_deleted sessionsPrevious (f #keysPrevious #mechanismsPrevious);
	    assert(Seq.length sessionsNew = Seq.length sessionsPrevious -1);
	    assert(countF (f #keysPrevious #mechanismsPrevious) sessionsNew = 0);
	let sessionsUpdated = Seq.append sessionsNew sessionsChanged in 
	    lemma_append_countF_aux2 (f #keysPrevious #mechanismsPrevious) sessionsNew sessionsChanged;
	    let f_t = f #keysPrevious #mechanismsPrevious in 
	    (*assert(countF f_t sessionsUpdated = countF f_t sessionsNew + countF f_t sessionsChanged);*)
	    (*assert(countF f_t sessionsNew = 0);*)
	    (*assert(countF f_t sessionsChanged = 1);*)
	    assert(countF f_t sessionsUpdated = 1);
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsUpdated in
	   (* assert(countF (f #newDevice.keys #newDevice.mechanisms) newDevice.subSessions = 1); *)
	   (* assert(Seq.length newDevice.subSessions = Seq.length d.subSessions); *)
	let s = find_if_more_than_one (f #newDevice.keys #newDevice.mechanisms) newDevice.subSessions in
	lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> if Signature? x then subSessionGetState x = _SubSessionUpd else true);
	    lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> if Verify? x then 
subSessionGetState x = _SubSessionVerifyUpd else true);	
	lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> subSessionGetStorage x =
subSessionGetStorage sessionToChange);
	lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> subSessionGetMechanism x =
subSessionGetMechanism sessionToChange);
	lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> subSessionGetKeyHandler x =
subSessionGetKeyHandler sessionToChange);				    
	 newDevice
	   
#set-options "--z3rlimit 50 --detail_errors "	  

val deviceUpdateSessionChangeStorage: #ks : seq key -> #ms : seq mechanismSpecification -> 
	f: (#ks: seq key -> #ms: seq mechanismSpecification -> subSession ks ms -> bool)
	{forall (ks1:seq key) (ms1: seq mechanismSpecification) 
		(ks2: seq key) (ms2: seq mechanismSpecification) 
		(s: subSession ks1 ms1) (s2: subSession ks2 ms2). 
		(
		  Signature? s = Signature? s2 /\
		  Verify? s = Verify? s2 /\
		  subSessionGetID s == subSessionGetID s2
		) ==> f s == f s2}->
	d: device {countF (f #d.keys #d.mechanisms) d.subSessions = 1}  -> 
	storage : temporalStorage ->
	Tot (resultDevice: device
	{
	  countF (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions = 1/\
	  Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
	  (
	  let s = find_if_more_than_one (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions in 
	  let sessionIndex = seq_getIndexF d.subSessions (f #d.keys #d.mechanisms)  in 
	  let previousSession = find_if_more_than_one (f #d.keys #d.mechanisms) d.subSessions in 
	  subSessionGetStorage s == Some storage /\
	  subSessionGetState s == subSessionGetState previousSession /\
	  subSessionGetMechanism s == subSessionGetMechanism previousSession /\
	  subSessionGetKeyHandler s == subSessionGetKeyHandler previousSession /\
	  modifiesSessionsE d resultDevice sessionIndex)	
	}
)


let deviceUpdateSessionChangeStorage #ks #ms f d storage = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys  in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionToChange = find_if_more_than_one (f #d.keys #d.mechanisms) sessionsPrevious in 
	    assert((f #d.keys #d.mechanisms) sessionToChange);
	let sessionChanged = subSessionSetStorage sessionToChange (Some storage) in 
	    assert(subSessionGetID sessionChanged == subSessionGetID sessionToChange);
	    assert((f #d.keys #d.mechanisms) sessionChanged == (f #d.keys #d.mechanisms) sessionToChange);
	    assert((f #d.keys #d.mechanisms) sessionChanged);
	let sessionsChanged = Seq.create 1 sessionChanged in 
	    miniLemmaCount (f #d.keys #d.mechanisms) sessionChanged;
	let sessionsNew = seq_remove sessionsPrevious (f #keysPrevious #mechanismsPrevious) in 
	  seq_remove_lemma_count_of_deleted sessionsPrevious (f #keysPrevious #mechanismsPrevious);
	let sessionsUpdated = Seq.append sessionsChanged sessionsNew in 
	  lemma_append_countF_aux2 (f #keysPrevious #mechanismsPrevious) sessionsChanged sessionsNew;
	  assert(countF (f #keysPrevious #mechanismsPrevious) sessionsUpdated = 1);
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsUpdated in 
	    let s = find_if_more_than_one (f #newDevice.keys #newDevice.mechanisms) newDevice.subSessions in 
	lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> subSessionGetKeyHandler x =
subSessionGetKeyHandler sessionToChange);
	lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> subSessionGetState x =
subSessionGetState sessionToChange);	
	lemFindWith2Funcs newDevice.subSessions (f #newDevice.keys #newDevice.mechanisms) (fun x -> subSessionGetMechanism x =
subSessionGetMechanism sessionToChange);	
	newDevice


(*
val lemma_count: #ks: seq key -> #ms: seq mechanismSpecification -> #ks1 : seq keyEntity -> #ms1 : seq mechanismSpecification -> 
	s: seq (subSession ks ms) -> s1: seq (subSession ks1 ms1){Seq.length s = Seq.length s1} -> f: (subSession ks ms -> bool) -> f1: (subSession ks1 ms1 -> bool) -> 
	Lemma (requires (forall (i: nat{i < Seq.length s}). sessionEqual (index s i) (index s1 i)))
	(ensures (count f s = count f1 s1))

let lemma_count #ks #ms #ks1 #ms1 s s1 f f1 = 
	if Seq.length s = 0 then () 
	else admit()

*)

val deviceAddSession: hSession:_CK_SESSION_HANDLE ->
  f: (#ks: seq key -> #ms: seq mechanismSpecification -> subSession ks ms -> bool) -> 
  d: device{countF f d.subSessions = 0} -> 
  newSession: subSession d.keys d.mechanisms{f newSession} -> 
  Tot (resultDevice: device
  {
    ( 
    (* The number of subsessions satisfying the function*)
    (* A new entity added *)
    (* no other sessions changed *)
	countF f resultDevice.subSessions = 1 /\ 
	Seq.length d.subSessions + 1 = Seq.length resultDevice.subSessions /\ (
	let sessionIndex = seq_getIndexF resultDevice.subSessions f in 
	modifiesSessionsM resultDevice d sessionIndex/\
	  (
	    let newSession = updateSession_ d newSession resultDevice.keys resultDevice.mechanisms in 
	    count newSession resultDevice.subSessions = 1 /\
	    seq_getIndex resultDevice.subSessions newSession == seq_getIndexF resultDevice.subSessions f 
	  )
	))	
  }
)


#set-options "--z3rlimit 100 --detail_errors"

let deviceAddSession hSession f d newSession = 
	(*countFCount f d.subSessions newSession;*)
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessions = d.subSessions in 
	let newSessionUpd = updateSession_ d newSession d.keys d.mechanisms in 
	let newElement = Seq.create 1 newSessionUpd in 
	  miniLemmaCount f newSessionUpd;
	let sessions_upd = append sessions newElement in
	  lemma_append_countF_aux2 f sessions newElement;
	  countFCount (f #keysPrevious #mechanismsPrevious) sessions newSessionUpd;
	  lemma_append_count_aux newSessionUpd sessions newElement;
	let updatedDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessions_upd	in 
		lemma_getIndex2 f sessions newSessionUpd;
		countFCount f sessions newSessionUpd;
		lemma_getIndex newSessionUpd sessions; 
	updatedDevice

(*
val _CKS_GenerateKey: d: device ->  
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism = true /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagKeyGeneration flags)} ->
	pTemplate: seq attributeSpecification{checkedAttributes pTemplate} -> 
	Pure(
		(handler: result _CK_OBJECT_HANDLE) & 
		(resultDevice : device {
			if Inr? handler then 
				d = resultDevice else 
			let handler = (match handler with Inl a -> a) in 	
			Seq.length resultDevice.keys = Seq.length d.keys + 1 /\
			Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
			handler = Seq.length resultDevice.keys -1 /\
			(
				let newCreatedKey = Seq.index resultDevice.keys handler in 
				isAttributeLocal (newCreatedKey.element).attrs 
			) /\
			modifiesKeysM d resultDevice handler 
			}
		) 
	)
	(requires (True))
	(ensures (fun h -> True))

let _CKS_GenerateKey d hSession pMechanism pTemplate = 
	let mechanism = mechanismGetFromDevice d pMechanism in 
	let newKey = keyGeneration mechanism pTemplate in 
	if Inr? newKey then 
		let keyGenerationException = match newKey with Inr a -> a in 
		let keyGenerationException = Inr keyGenerationException in 
		(|keyGenerationException, d|)
	else 
		let key = (match newKey with Inl a -> a) in 
		let (|d, h|) = deviceUpdateKey d key in 
		(|Inl h, d|)

*)

assume val _sign: pData: seq FStar.UInt8.t ->  pMechanism: _CK_MECHANISM_TYPE -> key: _CK_OBJECT_HANDLE -> 
	pSignature: option (seq UInt8.t) ->
	pSignatureLen : _CK_ULONG ->
	Tot (result (seq FStar.UInt8.t * _CK_ULONG))


assume val _signUpdate: pPart: seq FStar.UInt8.t -> ulPartLen: nat {Seq.length pPart = ulPartLen} -> pMechanism: _CK_MECHANISM_TYPE -> key: _CK_OBJECT_HANDLE ->
	previousSign: option temporalStorage -> 
	Tot (result temporalStorage)


val signInit: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism = true /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagSign flags)} ->
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > v keyHandler /\ 
		(
		  let key = Seq.index d.keys (v keyHandler) in 
		  let attrKey = (keyGetObject key).attrs in 
		  isAttributeSign attrKey
		)} -> 
	Pure((resultDevice: device)  * (r: result bool))
	(requires
	  (
	    let f = predicateSessionSignature hSession in 
	    let openedSessions = d.subSessions in countF f openedSessions = 0
	  )
	)
	(ensures (fun h -> 
		let (resultDevice, r) = h in 
		if Inr? r then 
			d = resultDevice 
		else
			let f = predicateSessionSignature hSession in 
			let openedSessions = resultDevice.subSessions in 
			countF f openedSessions = 1 /\
			(
			  (
			    let sessionIndex = seq_getIndexF resultDevice.subSessions f in 
			    let s = Seq.index resultDevice.subSessions sessionIndex in 
			    subSessionGetState s = _SubSessionInit  /\  
			    subSessionGetMechanism s = pMechanism  /\
			    subSessionGetKeyHandler	s = keyHandler /\
			    Seq.length resultDevice.subSessions = Seq.length d.subSessions + 1 /\
			    modifiesSessionsM resultDevice d sessionIndex )
			)	
		)
	)	

let signInit d hSession pMechanism keyHandler = 
	let newSession = Signature hSession _SubSessionInit pMechanism keyHandler None in 
	let f = predicateSessionSignature hSession in 
	let resultDevice = deviceAddSession hSession f d newSession in 
	(resultDevice, Inl true)

val sign: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	(* the data to sign *)
	pData: seq UInt8.t -> 
	(* count of bytes to sign *)
	ulDataLen: _CK_ULONG{Seq.length pData = v ulDataLen} -> 
	(* in case of only request for the length*)
	pSignature: option (seq UInt8.t) -> 
	pSignatureLen: _CK_ULONG{if Some? pSignature then Seq.length (match pSignature with Some a -> a) = v pSignatureLen else true} -> 
	Pure(
	  (resultDevice: device) &
	  r: result (o: option (seq FStar.UInt8.t){Some? pSignature ==> Some? o /\ None? pSignature ==> None? o} * _CK_ULONG)
	)
	(requires(
	  let openedSessions = d.subSessions in 
	  let f = predicateSessionSignature hSession in 
	  countF (f #d.keys #d.mechanisms)  d.subSessions = 1 /\
	  (
	    let session = find_if_more_than_one f openedSessions in subSessionGetState session = _SubSessionInit
	  )
	))
	(ensures (fun h -> 
	  let (|resultDevice, r|) = h in 
	  let f = predicateSessionSignature hSession in 
	  if Inr? r ||  None? pSignature then 
	    modifies0 d resultDevice
	  else 
	    let openedSessions = resultDevice.subSessions in 
	    countF (f #d.keys #d.mechanisms) d.subSessions = 1 /\
	    countF f resultDevice.subSessions = 0 /\
	    Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1 /\
	    (
		let sessionIndex = seq_getIndexF d.subSessions f in 
		modifiesSessionsM d resultDevice sessionIndex
	    )
	))

let sign d hSession pData ulDataLen pSignature pSignatureLen = 
	let f = predicateSessionSignature hSession in 
	let currentSession = find_if_more_than_one f d.subSessions in 
	let m = subSessionGetMechanism	currentSession in 
	let k = subSessionGetKeyHandler	currentSession in 
	let signature = _sign pData m k pSignature pSignatureLen in 
	if Inr? signature then
	  (*let session = find_l f d.subSessions in 
	  let session = match session with Some a -> a in 
	  let exc = (match signature with Inr exc -> exc) in 
	  let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession f d in 
	  (|resultDevice, Inr exc|) *)
	  let exc = match signature with Inr exc -> exc in
	  (|d, Inr exc|)
	else if None? pSignature then 	
	  let (pSig,  pLen) = (match signature with Inl a -> a) in
	  (|d, Inl (None, pLen)|)
	else
	    begin 
	      let (pSig, pLen) = match signature with Inl a -> a in 
	      let session = find_l f d.subSessions in 
	      let session = match session with Some a -> a in 
	      let f = predicateSessionSignature hSession in 
	      let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession f d in 
	      (|resultDevice, Inl(Some pSig , pLen)|)
	    end	


val signUpdate: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	(* the data to sign *)
	pPart: seq FStar.UInt8.t -> //seq uint8
	(* count of bytes to sign *)
	ulPartLen : _CK_ULONG{Seq.length pPart = v ulPartLen} -> 
	Pure(
		(resultDevice: device) &
		(r: result bool)
	)
	(requires(
	  let f = predicateSessionSignature hSession in 
	  countF f d.subSessions  = 1 /\
	  (
	    let session = find_if_more_than_one f (d.subSessions) in 
	    countF f d.subSessions = 1 /\
	    (subSessionGetState session = _SubSessionInit || subSessionGetState session = _SubSessionUpd)
	)))
	(ensures (fun h -> 
	  let (|resultDevice, r|) = h in 
	  let f = predicateSessionSignature hSession in 
	  if Inr? r then 
	    modifies0 d resultDevice
	  else
	    countF f d.subSessions = 1 /\
	    countF f resultDevice.subSessions = 1 /\
	    (
	      let currentSession = find_if_more_than_one f (resultDevice.subSessions) in 
	      let previousSession = find_if_more_than_one f d.subSessions in 
	      let sessionIndex = seq_getIndexF d.subSessions f in 
	      Seq.length d.subSessions = Seq.length resultDevice.subSessions /\ 
	      subSessionGetState currentSession = _SubSessionUpd /\
	      subSessionGetMechanism previousSession = subSessionGetMechanism currentSession /\
	      subSessionGetKeyHandler previousSession = subSessionGetKeyHandler currentSession /\
	      Some? (subSessionGetStorage currentSession) /\ modifiesSessionsE d resultDevice sessionIndex
	    )
	)	
    )


let signUpdate d hSession pPart ulPartLen = 
    let f = predicateSessionSignature hSession in 
    let currentSession = find_l (f #d.keys #d.mechanisms) d.subSessions in 
    let currentSession = match currentSession with Some a -> a in 
    let m = subSessionGetMechanism	currentSession in 
    let k = subSessionGetKeyHandler currentSession in 
    let previousSign = subSessionGetStorage	currentSession in 
    let signature = _signUpdate pPart (v ulPartLen) m k previousSign in 
    if Inr? signature then 
      let exc = match signature with Inr exc -> exc in (|d, Inr exc|)
    else 
      begin
	let signature = (match signature with Inl a -> a) in 
	let session = find_l f d.subSessions in 
	let session = match session with Some a -> a in 
	let resultDevice = deviceUpdateSessionChangeStatus #d.keys #d.mechanisms (predicateSessionSignature hSession) d in 
	let resultDevice = deviceUpdateSessionChangeStorage #resultDevice.keys #resultDevice.mechanisms (predicateSessionSignature hSession) resultDevice signature in 
	lemFindWith2Funcs resultDevice.subSessions f (fun x -> subSessionGetState x = _SubSessionUpd);
	lemFindWith2Funcs resultDevice.subSessions f (fun x -> subSessionGetMechanism x = subSessionGetMechanism currentSession);
	lemFindWith2Funcs resultDevice.subSessions f (fun x -> subSessionGetKeyHandler x = subSessionGetKeyHandler currentSession);
	lemFindWith2Funcs resultDevice.subSessions f (fun x -> Some? (subSessionGetStorage x));
	(|resultDevice, Inl true|)
      end

val signFinal: d: device ->  
  hSession: _CK_SESSION_HANDLE ->
  Pure((resultDevice: device) & (r: result (seq FStar.UInt8.t * _CK_ULONG)))
  (requires(
    let openedSessions = d.subSessions in 
    let f = predicateSessionSignature hSession in 
    countF f openedSessions = 1 /\
    (
      countMore0IsSome openedSessions f;
      let theSameSession = find_l f openedSessions in 
      (	
	let session = match theSameSession with Some a -> a in 
	subSessionGetState session = _SubSessionUpd /\
	Some? (subSessionGetStorage session)
      )
    )
  ))
  (ensures (fun h -> 
    let (|resultDevice, r|) = h in 
	if Inr? r then 
	  d = resultDevice 
	else
	  let openedSessions = resultDevice.subSessions in 
	  let f = predicateSessionSignature hSession in 
	  Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1 /\ 
	  countF f openedSessions = 0 /\
	  countF f d.subSessions = 1 /\ 
	  (
	    let f1 = predicateSessionSignature hSession in 
	    let session = find_l f d.subSessions in 
	    let sessionIndex = seq_getIndexF d.subSessions f in 
	    modifiesSessionsM d resultDevice sessionIndex
	  )
	)
    )

let signFinal d hSession = 
	let f = predicateSessionSignature hSession in 
	let currentSession = find_l f d.subSessions in 
		countMore0IsSome d.subSessions f;
	let currentSession = match currentSession with Some a -> a in  
	let signature = subSessionGetStorage currentSession in 
	let signature = match signature with Some a -> a in 
	let signature = match signature with Element a -> a in 
	let (s, len) = signature in 
	let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession f d in 
	(|resultDevice, Inl (s, len)|)


(*)
val _CKS_Verify: d: device -> 
	hSession : nat -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\
		(let flags = mechanismGetFlags d pMechanism in isFlagVerify flags)} -> 
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\
		(let key = Seq.index d.keys keyHandler in let attrKey = (key.element).attrs in 
		isAttributeVerify attrKey)} -> 
	data: seq FStar.UInt8.t -> 
	dataLen : nat {Seq.length data = dataLen} -> 	
	Pure(
			resultDevice: device & 
			(option (_CK_ULONG * _CK_ULONG))
		)
	(requires(True))
	(ensures (fun h -> True))

(*)
val verifyInit: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagVerify flags)} ->
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\ 
		(let key = Seq.index d.keys keyHandler in 
		let attrKey = (key.element).attrs in
		isAttributeVerify attrKey)} -> 
	Pure(
			(resultDevice: device)  * 
			(r: result bool)
		)
	(requires(
			(* exists current session *)
		let openedSessions = d.subSessions in 
		let theSameSession = find_l (fun x -> x.id = hSession) openedSessions in 
		None? theSameSession
	))
	(ensures (fun h -> 
		let (resultDevice, r) = h in 
		if Inr? r then 
			d = resultDevice 
		else
			let openedSessions = resultDevice.subSessions in 
			let theSameSession = find_l (fun x -> x.id = hSession) openedSessions in 
			Some? theSameSession /\
			(let session = (match theSameSession with Some a  -> a) in 
			session.state = _SubSessionInit /\ 
			session.pMechanism = pMechanism /\
			session.keyHandler = keyHandler) /\
			count (fun x -> x.id = hSession) openedSessions = 1
		)
	)	
