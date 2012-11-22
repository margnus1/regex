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
    structure CharMap = BinaryMapFn(struct
                                    type ord_key = Char.char
                                    val compare = Char.compare
                                    end)
in

(* POST: DFA with nondistinguishable states merged *)
fun simplify (nos, finals, trans) : dfa =
    let
        exception First of Set.set
        fun popSetSet s =
            (SetSet.app (fn e => raise First e) s; NONE)
            handle First e => SOME (SetSet.delete (s, e), e)
        fun singletonIntMap  (key, value) = IntBinaryMap.insert (IntBinaryMap.empty, key, value)
        fun singletonCharMap (key, value) = CharMap.insert      (CharMap.empty,      key, value)
        (* Map from target to map from character to set of possible sources *)
        (* Type: (int, (char, int set) map) map *)
        val invTrans : Set.set CharMap.map IntBinaryMap.map =
            foldl (IntBinaryMap.unionWith (CharMap.unionWith Set.union))
                  IntBinaryMap.empty
                  (map (fn ((f, c), t) =>
                           singletonIntMap
                               (t, singletonCharMap
                                       (c, Set.singleton f)))
                       (TransMap.listItemsi trans))
        (* POST: Union_(s in stateSet) invTrans[s] *)
        fun incoming stateSet =
            foldl (CharMap.unionWith Set.union)
                  CharMap.empty
                  (List.mapPartial (fn (k, v) => if Set.member (stateSet, k)
                                                 then SOME v
                                                 else NONE)
                                   (IntBinaryMap.listItemsi
                                        invTrans))
        (* Hopcroft's algorithm as described on Wikipedia *)
        fun loop (P, W) =
            case popSetSet W of
                (* Kludge; P should not contain the empty set to begin with *)
                NONE => SetSet.delete (P, Set.empty)
              | SOME (W, A) =>
                let
                    fun perset ((Y, XiY, YmX), (P, W)) =
                        let
                            val P = SetSet.addList (SetSet.delete (P, Y), [XiY, YmX])
                        in
                            (P, if SetSet.member (W, Y) then
                                    SetSet.addList (SetSet.delete (W, Y), [XiY, YmX])
                                else
                                    if Set.numItems XiY <= Set.numItems YmX
                                    then SetSet.add (W, XiY)
                                    else SetSet.add (W, YmX))
                        end
                    fun perchar ((c, X), (P, W)) =
                        foldl perset (P, W)
                              (List.mapPartial
                                   (fn Y => let
                                           val XiY = Set.intersection (X, Y)
                                       in
                                           if Set.isEmpty XiY
                                           then NONE
                                           else SOME (Y, XiY, Set.difference (Y, X))
                                       end)
                                   (SetSet.listItems P))
                in
                    loop (foldl perchar (P, W) (CharMap.listItemsi (incoming A)))
                end
        fun range (n, m) = if n > m then [] else n :: range (n+1, m)
        fun setOf list = Set.addList (Set.empty, list)
        fun setSetOf list = SetSet.addList (SetSet.empty, list)
        val nonfinals = Set.difference (setOf (range (1, nos)), finals)
        fun toDFA states =
            let
                fun index ([],          _, acc) = acc
                  | index ((e::es)::Es, n, acc) = index (es::Es, n,   (e, n) :: acc)
                  | index ([]::Es,      n, acc) = index (Es,     n+1,           acc)
                val indexes = foldl IntBinaryMap.insert' IntBinaryMap.empty
                                    (index (map Set.listItems (SetSet.listItems states),
                                            1, []))
                fun im 0 = 0
                  | im n = valOf (IntBinaryMap.find (indexes, n))
                (* We assume that the initial state is given index 1 *)
                val 1 = im 1
                fun mapkv f m =
                    List.foldl (fn (kv, m) => TransMap.insert' (f kv, m))
                               TransMap.empty
                               (TransMap.listItemsi m)
            in
                (SetSet.numItems states,
                 Set.map im finals,
                 mapkv (fn ((f, c), t) => ((im f, c), im t)) trans)
            end
    in
        toDFA (loop (setSetOf [nonfinals, finals], SetSet.singleton finals))
    end


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
                fun addToPair (e, (s1, s2)) =
                    if SetSet.member (s1, e)
                    then (s1, s2)
                    else (s1, SetSet.add (s2, e))

                exception First of Set.set
                fun firstElementInSet s =
                    (SetSet.app (fn e => raise First e) s; NONE)
                    handle First e => SOME e

                (* POST: The new state when recieving c when in state e *)
                fun eTrans e c = expand (Set.addList
                                             (Set.empty,
                                              List.mapPartial
                                                  (fn (f, d, t) =>
                                                      if Set.member (e, f) andalso c = d
                                                      then SOME t else NONE)
                                                  regulars))
                (* POST: a list of all input characters c that are accepted in state e *)
                fun possibleInputs e = ListMergeSort.uniqueSort
                                           Char.compare
                                           (List.mapPartial (fn (f, c, _) =>
                                                                if Set.member (e, f)
                                                                then SOME c else NONE)
                                                            regulars)
                
                (* POST: (states of the DFA, transitions of the DFA) *)
                fun loop ((pstates, ustates), trans) =
                    case firstElementInSet ustates of
                        NONE => (pstates, trans)
                      | SOME state =>
                        let
                            fun introduceTransition (c, (sp, trans)) =
                                let
                                    val newState = eTrans state c
                                in
                                    (addToPair (newState, sp),
                                     SetTransMap.insert (trans, (state, c), newState))
                                end
                            val ((npstates, nustates), ntrans) =
                                foldl introduceTransition
                                      ((pstates, ustates), trans)
                                      (possibleInputs state)
                        in
                            loop ((SetSet.add (npstates, state),
                                   SetSet.delete (nustates, state)),
                                  ntrans)
                        end

                val (states, transitions) =
                    loop ((SetSet.empty, SetSet.singleton initial), SetTransMap.empty)
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
        simplify (toDFA (convert ()))
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
