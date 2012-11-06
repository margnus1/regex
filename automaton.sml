datatype regex = 
         Star of regex
       | Union of regex * regex
       | Concat of regex * regex
       | Class of char -> bool
       | Char of char
       | Epsilon
datatype match =
         SOME of char list * char list * (unit -> match)
       | NONE
fun match (input : char list , Epsilon) = SOME ([], input, fn () => NONE)
  | match ([], Char p) = NONE
  | match (c::rest, Char p) = 
    if c = p then
        SOME ([c], rest, fn () => NONE)
    else
        NONE
  | match ([], Class pred) = NONE
  | match (c::rest, Class pred) =
    if pred c then 
        SOME ([c], rest, fn () => NONE)
    else
        NONE
  | match (input, Concat (t, u)) = 
    let 
        fun matchConcat thisM = 
            case thisM () of 
                NONE => NONE
              | SOME (s1, r1, n1) => 
                matchConcat2 (s1, r1, n1) (fn () => match (r1, u))
        and matchConcat2 (s1, r1, n1) thisM =
            case thisM () of
                NONE => matchConcat n1
              | SOME (s2, r2, n2) => 
                SOME (s1 @ s2, r2, fn () => matchConcat2 (s1, r1, n1) n2)
   in
       matchConcat (fn () => match (input, t))
   end
  | match (input, Union (t, u)) =
    let
        fun butalso mf other () =
            case mf () of
                SOME (s, r, n) =>
                SOME (s, r, butalso n other)
              | NONE =>
                match (input, other)
    in
        butalso (fn () => match (input, t)) u ()
    end
  | match (input, Star t) =
    let
        fun matchRest [] = ([], [])
          | matchRest ((s,r,n)::rest) =
            let val (prevs, _) = matchRest rest in
                (prevs @ s, r) end
        fun matchStar stack mf =
            case mf () of
                SOME (s, r, n) =>
                matchStar (s, r, n) (fn () => match (r, t))
              | NONE =>
                case stack of
                    [] => SOME ([], input, fn () => NONE)
                  | ((_, _, nf)::rest) =>
                    let val (s, r) = matchRest stack in
                        (s, r, fn () => matchStar rest nf) end
    in
        matchStar [] (fn () => match (input, t))
    end
    
(* datatype  *)


(* Unit tests *)

(* Epsilon *)
local
    val SOME ([], [], f1) = match ([], Epsilon)
    val NONE = f1 ()
    val SOME ([], [#"h"], f2) = match ([#"h"], Epsilon)
    val NONE = f2 ()                 
in ; end

(* Char *)
local 
    val NONE = match ([], Char #"n")
    val SOME ([#"n"], [], f1) = match ([#"n"], Char #"n")
    val NONE = f1 ()                  
    val SOME ([#"n"], [#"k"], f2) = match ([#"n", #"k"], Char #"n")
    val NONE = f2 ()
in ; end

(* Union *)
local
    val SOME ([#"c"], [#"d"], f1) = match ([#"c", #"d"], Union (Char #"c", Char #"d"));
    val NONE = f1 ()
    val SOME ([#"c"], [#"d"], f2) = match ([#"c", #"d"], Union (Char #"c", Char #"c"));
    val SOME ([#"c"], [#"d"], f3) = f2 ()
    val NONE = f3 ()
in ; end
