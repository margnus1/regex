signature NFA = sig
    type regex
    type nfa
    val fromRegex : regex -> nfa
end 
structure Nfa = struct
local
    structure R = Regex
in
type regex = R.regex

(* State numbers go from 1 to NumberOfStates, 0 represent the null state *)
datatype transition = Regular of int * char * int
                    | Epsilon of int * int
type nfa = int * transition list
(* (NumberOfStates, Transitions) *)
(* State 1 is the initial state, state NumberOfStates is the final state *)

local 
    fun transpose amount (numStates, trans) = 
        (numStates + amount, (* map (fn n => n + amount) accepting, *)
         map (fn Regular (f, c, t) => Regular (f + amount, c, t + amount)
               | Epsilon (f, t)    => Epsilon (f + amount,    t + amount)) 
             trans)
in
fun fromRegex R.Epsilon  = (2, [Epsilon (1, 2)]) : nfa
  | fromRegex (R.Char c) = (2, [Regular (1, c, 2)])
  | fromRegex (R.Star r) = 
    let val (nos, trans) = fromRegex r 
    in (nos + 1, Epsilon (1, nos + 1) ::
                 Epsilon (nos, 1) ::
                 Epsilon (nos, nos + 1) ::
                 trans) end
  | fromRegex (R.Concat (r, s)) = 
    let 
        val (rNos, rTrans) = fromRegex r
        val (nos, sTrans) = transpose (rNos-1) (fromRegex s)
    in
        (nos, (* Epsilon (rNos, rNos+1) :: *) rTrans @ sTrans)
    end
  | fromRegex (R.Union (r, s)) = 
    let 
        val (rNos, rTrans) = transpose 1 (fromRegex r)
        val (sNos, sTrans) = transpose rNos (fromRegex s)
    in
        (sNos + 1, Epsilon (1, 2) :: 
                   Epsilon (1, rNos + 1) :: 
                   Epsilon (rNos, sNos + 1) :: 
                   Epsilon (sNos, sNos + 1) :: 
                   rTrans @ sTrans)
    end
end

fun toDot (nos, trans) =
    let
        fun dotTrans (Regular (f, c, t)) = 
            String.concat [Int.toString f, " -> ", Int.toString t, 
                           " [label=\"", Char.toString c, "\"]"]
          | dotTrans (Epsilon (f, t)) = 
                        String.concat [Int.toString f, " -> ", Int.toString t, 
                           " [label=\"&epsilon;\"]"]
    in
        String.concatWith "\n" (["digraph D {",
                                 "graph [rankdir=LR]",
                                 "node [shape=circle]",
                                 "\"\" [shape=none]",
                                 Int.toString nos ^ " [shape=doublecircle]",
                                "\"\" -> 1"]
                                @ map dotTrans trans @ ["}"])
    end

end
end
