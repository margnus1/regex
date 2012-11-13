structure Regex = struct
local
    val keyChars = "\\[]()+*?"
in
datatype regex = 
       Star of regex
     | Union of regex * regex
     | Concat of regex * regex
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
                matchStar ((s, r, n)::stack) (fn () => match (r, t))
              | NONE =>
                case stack of
                    [] => SOME ([], input, fn () => NONE)
                  | ((_, _, nf)::rest) =>
                    let val (s, r) = matchRest stack in
                        SOME (s, r, fn () => matchStar rest nf) end
    in
        matchStar [] (fn () => match (input, t))
    end

fun matchesFully (string, regex) =
    let
        fun loop rest = 
            case rest () of
                SOME (match, [], _) => true
              | SOME (_, _, rest)   => loop rest
              | NONE                => false
    in
        loop (fn () => match (String.explode string, regex))
    end

fun allMatches (string, regex) =
    let
        fun loop rest = 
            case rest () of
                SOME (match, _, rest) => String.implode match :: loop rest
              | NONE                  => []
    in
        loop (fn () => match (String.explode string, regex))
    end

fun simplify (Star a) = Star (simplify a)
  | simplify (Union (a, b)) = Union (simplify a, simplify b)
  | simplify (Concat (Epsilon, b)) = simplify b
  | simplify (Concat (a, b)) = Concat (simplify a, simplify b)
  | simplify a = a

exception Parse of string
fun parse string = 
    let 
        fun p []         acc = ([], acc)
          | p (#"("::cs) acc = 
            (let 
                val (rest, pr) = p cs Epsilon
            in
                case rest of 
                    (#")"::cont) => p cont (Concat (acc, pr))
                  | _            => raise Parse "Unmatched left parenthesis"
            end)
          | p (cs as #")"::_) acc = (cs, acc)
          | p (#"|"::cs)      acc = 
            let 
                val (rest, ur) = p cs Epsilon
            in
                (rest, Union (acc, ur))
            end
          | p (#"[":: #"]"::_) _   = raise Parse "Empty character classes are not allowed"
          | p (#"["::c::cs)    acc = 
            let 
                fun range f t acc =
                    if f > t then acc else
                    range (f+1) t (Union (acc, Char (chr f)))
                fun inner (#"]"::cs)     acc = (cs, acc)
                  | inner (#"\\"::c::cs) acc = inner cs (Union (acc, Char c))
                  | inner (#"-"::t::cs)  (Char f) = inner cs (range (ord f+1) (ord t) (Char f))
                  | inner (#"-"::t::cs)  (Union (acc, Char f)) =
                    inner cs (range (ord f) (ord t) acc)
                  | inner [#"-"]         _ = raise Parse "You cannot end a class with a dash"
                  | inner (c::cs)        acc = inner cs (Union (acc, Char c))
                  | inner []             _   = raise Parse "Unmatched left square bracket"
                val (classRem, classRes) = inner cs (Char c)
            in
                p classRem (Concat (acc, classRes))
            end
          | p (#"?"::cs)     (Concat (prev, last)) = p cs (Concat (prev, Union (last, Epsilon)))
          | p (#"+"::cs)     (Concat (prev, last)) = p cs (Concat (prev, Concat (last, Star last)))
          | p (#"*"::cs)     (Concat (prev, last)) = p cs (Concat (prev, Star last))
          | p (#"\\"::c::cs) acc                   = p cs (Concat (acc, Char c))
          | p (c::cs)        acc                   = 
            if CharVector.exists (fn e => e = c) keyChars then
                raise Parse ("Unexpected " ^ Char.toString c)
            else
                p cs (Concat (acc, Char c))
        val (remains, result) = p (String.explode string) Epsilon
    in
        case remains of 
            [] => simplify result
          | _ => raise Parse "Unmatched right parenthesis"
    end

fun toString Epsilon = ""
  | toString (Char   c)            = 
    if CharVector.exists (fn e => e = c) keyChars then
        "\\" ^ Char.toString c
    else Char.toString c
  | toString (Concat (a, Star b))  = 
    if a = b then
        String.concat ["(", toString a, ")+"]
    else
        String.concat [toString a, toString (Star b)]
  | toString (Concat (a,       b)) = toString a ^ toString b
  | toString (Union  (Epsilon, b)) = String.concat ["(", toString b, ")?"]
  | toString (Union  (a,       b)) = String.concat ["(", toString a, "|", toString b, ")"]
  | toString (Star   a)            = String.concat ["(", toString a, ")*"]

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
end
end
