(* This structure only contains the operations that *)
(* can be made more efficient (but still equivalent to) *)
(* than converting to a normal list and then performing *)
(* them *)
structure LazyList = struct
datatype 'a lazyList = zCons of 'a * (unit -> 'a lazyList)
                 | zNil
fun fromList [] = zNil
  | fromList (e::es) =
    zCons (e, fn () => fromList es)

fun toList zNil = []
  | toList (zCons (e, eRest)) =
    e :: toList (eRest ())

fun zNil @ A = A
  | A @ zNil = A
  | (zCons (e, eRest)) @ F =
    zCons (e, fn () => eRest () @ F)

fun appendLazy (zNil,               B) = B ()
  | appendLazy ((zCons (e, eRest)), B) = 
    zCons (e, fn () => appendLazy (eRest (), B))

fun map f zNil = zNil
  | map f (zCons (e, eRest)) =
    zCons (f e, fn () => map f (eRest ()))

fun concat zNil = zNil
  | concat (zCons (zNil, eRest)) = concat (eRest ())
  | concat (zCons (zCons (f, fRest), eRest)) = 
    zCons (f, fn () => concat (zCons (fRest (), eRest)))

fun zip (zCons (e, eRest), zCons (f, fRest)) =
    zCons ((e, f), fn () => zip (eRest (), fRest ()))
  | zip _ = zNil

fun app f zNil = ()
  | app f (zCons (e, eRest)) =
    (f e; app f (eRest ()))

fun filter f zNil = zNil
  | filter f (zCons (e, eRest)) =
    if f e then
        zCons (e, fn () => filter f (eRest ()))
    else
        filter f (eRest ())

fun filterMap f zNil = zNil
  | filterMap f (zCons (e, eRest)) =
    case f e of
        SOME e => zCons (e, fn () => filterMap f (eRest ()))
      | NONE   => filterMap f (eRest ())

fun cartesian product (zCons (e, eRest), F as zCons _) =
    map (fn f => product (e, f)) F @ 
    cartesian product (eRest (), F)
  | cartesian _ _ = zNil

fun take 0 _ = []
  | take n zNil = []
  | take n (zCons (e, eRest)) = e :: take (n-1) (eRest ())
end
