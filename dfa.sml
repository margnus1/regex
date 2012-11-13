structure Dfa = struct
local
    fun lexComp ac bc ((a1, b1), (a2, b2)) =
        case (ac (a1, a2), bc (b1, b2)) of
            (GREATER,     _) => GREATER
          | (LESS,        _) => LESS
          | (EQUAL, GREATER) => GREATER
          | (EQUAL,    LESS) => LESS
          | (EQUAL,   EQUAL) => EQUAL
in
structure TransMap = BinaryMapFn(
    struct
    type ord_key = int * char
    val compare = lexComp Int.compare Char.compare
    end)
structure Set = IntBinarySet
type dfa = (int * Set.set * int TransMap.map)

local
    structure SetTransMap = BinaryMapFn(struct 
                                         type ord_key = Set.set * char
                                         val compare = lexComp Set.compare Char.compare
                                         end)
    structure SetMap = BinaryMapFn(struct
                                    type ord_key = Set.set
                                    val compare = Set.compare
                                    end)
    structure SetSet = BinarySetFn(struct
                                    type ord_key = Set.set
                                    val compare = Set.compare
                                    end)
in
(* TYPE: Nfa.nfa -> dfa *)
fun fromNFA (nos, trans) =
    let
        val epsilons = List.mapPartial (fn Nfa.Epsilon (_, 0) => NONE
                                         | Nfa.Epsilon p => SOME p 
                                         | _ => NONE) trans
        val regulars = List.mapPartial (fn Nfa.Regular (_, _, 0) => NONE
                                         | Nfa.Regular p => SOME p 
                                         | _ => NONE) trans
        (* PRE:  state is a set of states *)
        (* POST: All states reachable from any of the states in state following only *)
        (*       epsilon transitions *)
        fun expand state = 
            let 
                fun addToPair (e, (s1, s2)) = if Set.member (s1, e) then (s1, s2) else (s1, Set.add (s2, e))
                exception First of int
                fun firstElementInSet s =
                    (Set.app (fn e => raise First e) s; NONE)
                    handle First e => SOME e
                (* PRE:  All states reachable from sr are in sr union *)
                (*       sr and su are sets of states *)
                (* POST: All states reachable from any of the states in sr union su *)
                (*       following  only epsilon transitions *)
                fun loop (sr, su) =
                    case firstElementInSet su of
                        NONE => sr
                      | SOME element =>                        
                        let 
                            fun efilter (f, t) = if element = f then SOME t else NONE
                            val (nr, nu) = foldl addToPair (sr, su) (List.mapPartial efilter epsilons)
                        in
                            loop (Set.add (nr, element), Set.delete (nu, element))
                        end
            in
                loop (Set.empty, state)
            end
        val initial = (expand (Set.singleton 1))
        (* PRE:  // trans is a list of transitions in the NFA *)
        (* POST: (all states of the dfa, final states of the dfa, transitions of the dfa) *)
        (* TYPE: Nfa.transition list -> SetSet.set * SetSet.set * SetTransMap.map *)
        fun convert () =
            let
                fun addToPair (e, (s1, s2)) = if SetSet.member (s1, e) then (s1, s2) else (s1, SetSet.add (s2, e))
                exception First of Set.set
                fun firstElementInSet s =
                    (SetSet.app (fn e => raise First e) s; NONE)
                    handle First e => SOME e

                (* POST: The new state when recieving c when in state e *)
                fun eTrans e c = expand (Set.addList (Set.empty, List.mapPartial
                                  (fn (f, d, t) =>
                                      if Set.member (e, f) andalso c = d
                                      then SOME t else NONE) regulars))
                (* POST: a list of all input characters c that are accepted in state e *)
                fun possibleInputs e = ListMergeSort.uniqueSort Char.compare (List.mapPartial
                                        (fn (f, c, _) => if Set.member (e, f)
                                                         then SOME c else NONE) regulars)                    
                
                (* POST: (states of the DFA, transitions of the DFA) *)
                fun loop ((pstates, ustates), trans) =
                    case firstElementInSet ustates of
                        NONE => (pstates, trans)
                      | SOME state => 
                        let
                            fun introduceTransition (c, (sp, trans)) =
                                let val newState = eTrans state c in
                                    (addToPair (newState, sp), 
                                     SetTransMap.insert (trans, (state, c), newState)) end
                            val ((npstates, nustates), ntrans) = 
                                foldl introduceTransition ((pstates, ustates), trans) (possibleInputs state)
                        in
                            loop ((SetSet.add (npstates, state), SetSet.delete (nustates, state)), ntrans)
                        end

                val (states, transitions) = loop ((SetSet.empty, SetSet.singleton initial), SetTransMap.empty)
                (* POST: true iff set is a final state *)
                fun final set = Set.member (set, nos)
            in
                (states, SetSet.filter final states, transitions)
            end
        (* PRE:  (states, finals, trans) represents a valid DFA *)
        (* POST: (numberOfStates, finalStates, transitions) which represents the same *)
        (*       DFA that (states, finals, trans) does *)
        (* TYPE: SetSet.set * SetSet.set * SetTransMap.map -> int * Set.set * TransMap.map *)
        fun toDFA (states, finals, trans) =
            let 
                fun index ([], _, acc) = acc
                  | index (e::es, n, acc) = index (es, n+1, (e, n) :: acc)
                val indexes = foldl SetMap.insert' (SetMap.insert (SetMap.empty, initial, 1)) 
                                    (index (SetSet.listItems (SetSet.delete(states, initial)), 2, []))
                fun toIndex state = valOf (SetMap.find (indexes, state))
                fun transToIndex ((s, c), t) = ((toIndex s, c), toIndex t)
            in
                (SetSet.numItems states, 
                 Set.addList (Set.empty, map toIndex (SetSet.listItems finals)), 
                 foldl TransMap.insert' TransMap.empty (map transToIndex (SetTransMap.listItemsi trans)))
            end
    in
        toDFA (convert ())
    end
end

fun toDot (_, final, trans) =
    let
        fun dotTrans ((f, c), t) = 
            String.concat [Int.toString f, " -> ", Int.toString t, 
                           " [label=\"", Char.toString c, "\"]"]
    in
        String.concatWith "\n" (["digraph D {",
                                 "graph [rankdir=LR]",
                                 "node [shape=circle]",
                                 "\"\" [shape=none]",
                                 "\"\" -> 1"]
                                @ map (fn n => Int.toString n ^ " [shape=doublecircle]") (Set.listItems final)
                                @ map dotTrans (TransMap.listItemsi trans) @ ["}"])
    end


end
end
