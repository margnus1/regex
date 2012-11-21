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

fun fromRegex regex =
    let
        fun translate m trans =
            map (fn Regular (f, c, t) => Regular (m f, c, m t)
                  | Epsilon (f, t)    => Epsilon (m f,    m t)) 
                trans
        fun transposeT amount trans =
            translate (fn 0 => 0 | n => n + amount) trans
        fun transpose  amount (numStates, trans) = 
            (numStates + amount, transposeT amount trans)
        (* Merges nodes a, b into b *)
        fun merge a b trans = translate (fn n => if n = a then b else n) trans
        fun swap  a b trans = translate (fn n => if n = a then b else 
                                                 if n = b then a 
                                                 else n) trans
        (* POST: (StartInc, Nfa, EndOutg) *)
        fun fromRegex R.Epsilon  = (false, (2, [Epsilon (1, 2)]), false) : bool * nfa * bool
          | fromRegex (R.Char c) = (false, (2, [Regular (1, c, 2)]), false)
          | fromRegex (R.Star r) =
            let
                val (startinc, (nos, trans), endoutg) = fromRegex r
            in
                case (startinc, endoutg) of
                    (* Observe that the start and final states could be merged in the following *)
                    (* three cases, but it is not supported by the representation *)
                    (false, false) => (true, (nos, Epsilon (1, nos) ::
                                                   merge nos 1 trans),
                                       true)
                  | (_,     false) => (true, (nos + 1, Epsilon (1, nos) ::
                                                       Epsilon (1, nos+1) ::
                                                       swap 1 nos trans),
                                       false)
                  | (_,     _)     => (true, (nos + 2, Epsilon (1, 2) ::
                                                       Epsilon (1, nos+2) ::
                                                       Epsilon (nos+1, 1) ::
                                                       transposeT 1 trans),
                                       false)
            end
          | fromRegex (R.Concat (r, s)) = 
            let 
                val (rSInc, (rNos, rTrans), rEOutg) = fromRegex r
                val (sSInc, (sNos, sTrans), sEOutg) = fromRegex s
            in
                case (rEOutg, sSInc) of
                    (true, true) => (rSInc, (sNos+rNos, Epsilon (rNos, rNos+1) ::
                                                        transposeT rNos sTrans @ 
                                                        rTrans), 
                                     sEOutg)
                  | (_,    _)    => (rSInc, (sNos+rNos-1, 
                                             transposeT (rNos-1) sTrans @ rTrans),
                                     sEOutg)
            end
          | fromRegex (R.Union (r, s)) = 
            let 
                val (rSInc, rN, rEOutg) = fromRegex r
                val (sSInc, sN, sEOutg) = fromRegex s
                (* PRE: rFin = nos or sFin = nos *)
                fun outg ((nos, trans), rFin, sFin) =
                    let
                        val (max, min) = (Int.max (rFin, sFin), Int.min (rFin, sFin))
                    in
                        case (rEOutg, sEOutg) of 
                            (true,  true)  => (false, (nos+1, Epsilon (rFin, nos+1) :: 
                                                              Epsilon (sFin, nos+1) :: trans), 
                                               false)
                          | (true,  false) => 
                            (false,
                             (* We cannot merge rFin and sFin because the exit transitions from rFin *)
                             (* will cause us to accept strings not in the language *)
                             (* Solution: Epsilon from rFin to eFin, use eFin as last *)
                             (nos, swap nos sFin (Epsilon (rFin, sFin) :: trans)),
                             false)
                          | (false, true) => 
                            (false, 
                             (* Same as previously, with eFin and rFin swapped *)
                             (nos, swap nos rFin (Epsilon (sFin, rFin) :: trans)), 
                             false)
                          | (false, false) => 
                            (false,
                             (nos - 1, swap min (max-1) (merge max min trans)),
                             false)
                    end
                fun union ((true, rN), (false,  sN)) = 
                    let
                        val (nt, sFin, rFin) = union ((false, sN), (true, rN))
                    in
                        (nt, rFin, sFin)
                    end
                  | union ((false, rN), (false, sN)) =
                    let
                        val (rNos, rTrans) = rN
                        val (sNos, sTrans) = transpose (rNos-1) sN
                        (* Merge start nodes *)
                        fun rTMap n = if n = rNos then 1 else n
                    in
                        ((sNos, translate rTMap sTrans @ rTrans), rNos, sNos)
                    end
                  | union ((false, rN), (true,  sN)) = 
                    let
                        val (rNos, rTrans) = rN
                        val (sTNos, sTTrans) = transpose rNos sN
                    in
                        ((sTNos, Epsilon (1, rNos + 1) ::
                                 rTrans @ sTTrans),
                         rNos, sTNos)
                    end
                  | union ((true,  rN), (true,  sN)) = 
                    let
                        val (rTNos, rTTrans) = transpose 1 rN
                        val (sTNos, sTTrans) = transpose rTNos sN
                    in
                        ((sTNos, Epsilon (1, 2) ::
                                 Epsilon (1, rTNos + 1) ::
                                 rTTrans @ sTTrans),
                         rTNos, sTNos)
                    end
            in
                outg (union ((rSInc, rN), (sSInc, sN)))
            end
        val (_, nfa, _) = fromRegex regex
    in
        nfa
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
