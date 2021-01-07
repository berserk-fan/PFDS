(* Excercise 3.6 *)
functor BinomialHeap(Element: Ordered) : Heap =
struct

structure Elem = Element
datatype Tree = Node of Elem.T * Tree list
type Heap = (int * Tree) list (* we need this because binomial tree can be only of 2^k size *)

val empty = []

fun isEmpty [] = true
  | isEmpty _ = false

fun rank((a, b)) = a
fun children((a, b)) = b

fun link(t1 as (r, Node(x1, c1)), t2 as (_, Node(x2, c2))) =
    if Elem.leq(x1, x2) then (r + 1, Node(x1, children t2 :: c1))
    else (r + 1, Node(x2, children t1 :: c2))

fun insTree(a, []) = [a]
  | insTree (t, ts as t' :: ts') =
    if rank t < rank t'
    then t :: ts
    else insTree(link(t, t'), ts')

fun insert(x, ts) = insTree( (0, Node(x, [])) , ts)

fun merge(ts1, []) = ts1
  | merge ([], ts2) = ts2
  | merge (ts1 as t1 :: ts1', ts2 as t2 :: ts2') =
    if rank t1 < rank t2 then t1 :: merge(ts1', ts2)
    else if rank t2 < rank t1 then t2 :: merge(ts1, ts2')
    else insTree(link(t1,t2), merge(ts1', ts2'))

fun root((_, Node(x, ts))) = x
                               
fun removeMinTree [] = raise Empty
  | removeMinTree [t] = (t, [])
  | removeMinTree (t :: ts) =
    let val (t', ts') = removeMinTree ts
    in if Elem.leq (root t, root t') then (t, ts) else (t', t :: ts')
    end

(* fun findMin ts = let val (t, _) = removeMinTree in root t end *)
(* Excercise 3.5 *)
fun findMin [] = raise Empty
  | findMin [t] = root t
  | findMin (t :: ts) = let val rmins = findMin(ts)
                            val rt = root t
                        in
                          if Elem.leq(rt, rmins) then rt else rmins
                        end

    
fun deleteMin ts = let val ((r, Node(x, ts1)), ts2) = removeMinTree ts
                       val (_, nodes) = foldl(fn (el, cur') => let val (i, cur) = cur'
                                                          in (i + 1, (i, el) :: cur)
                                                          end)
                                        ((length ts1, []))(ts1)
                   in merge(nodes, ts2)
                   end
end


functor ExplicitMin(H: Heap): Heap =
struct
structure Elem = H.Elem
datatype Heap = E | NE of Elem.T * H.Heap

val empty = E
                
fun isEmpty E = true
  | isEmpty _ = false

fun findMin (E) = raise Empty
  | findMin (NE(min ,_)) = min
                     
fun insert(x, E) = NE(x, H.insert(x, H.empty))
  | insert(x, (NE(min, h))) = let val smaller = if Elem.leq(x, min) then x else min
                          in NE(smaller, H.insert(x, h))
                          end

fun deleteMin(NE(_, h)) = let val deleted = H.deleteMin(h)
                        in NE(H.findMin(deleted), deleted)
                        end

fun merge(h, E) = h
  | merge (E, h) = h
  | merge (NE(min1, h1), NE(min2, h2)) = let val smaller = if Elem.leq(min1, min2) then min1 else min2
                                         in NE(smaller, H.merge(h1,h2))
                                         end

end
    
