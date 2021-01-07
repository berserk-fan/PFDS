signature Heap =
sig
  structure Elem: Ordered
  type Heap
  val empty: Heap
  val isEmpty: Heap -> bool
                           
  val insert: Elem.T * Heap -> Heap
  val merge: Heap * Heap -> Heap

  val findMin: Heap -> Elem.T (*raises empty if heap is empty*)
  val deleteMin: Heap -> Heap (*raises empty if heap is empty *)

  
end

(* Exercise 3.1 *)
    (* let's take the max right spine of a tree. assume it has k elements. 
       take the start of this spine. left child subtree has right spine that is equal to at least k-1. 
       so we have:
       let: #(k) minimum number of elemenents if leftist tree with max right spine of lenght k
       then:
             #(k) >=  #(k-1) (leftist property + size of left sbtree) 
                    + #(k-1) (right subtree) 
                    + 1 (root node)
       so we have reccurence relation #(k) >= 2 * #(k-1) + 1 and #k(0) = 0
       by solving this we have. #(k) >= 2^k - 1.
       let's n is a actual size of tree. 
       n >= #(k) ~ n >= 2^k - 1 ~ k <= log_2(n + 1) => k is at most [log_2(n+1)]. *)

functor LeftistHeap(Element: Ordered): Heap =
struct

structure Elem = Element
datatype Heap = E | T of int * Elem.T * Heap * Heap

val empty = E
                
fun isEmpty E = true
  | isEmpty _ = false
                                                   
fun rank E = 0
  | rank (T(k,_,_,_)) = k
fun makeT (x, a, b) =
    if rank a >= rank b then T(rank b + 1, x, a, b) else T (rank a + 1, x, b, a)

fun merge (h, E) = h
  | merge (E, h) = h
  | merge (h1 as T(_, x, a1, b1), h2 as T(_, y, a2, b2)) =
    if Elem.leq(x,y)
    then makeT(x, a1, merge(b1, h2))
    else makeT(y, a2, merge(h1, b2))

              
(* fun insert (x, h) = merge(T(1, x, E, E), h) *)
(* Exercise 3.2 *)
fun insert (x, E) = T(1, x, E, E)
  | insert(x, T(_, y, a, b)) = if Elem.leq(x, y)
                               then makeT(x, a, insert(y, b))
                               else makeT(y, a, insert(x, b))

fun findMin E = raise Empty
  | findMin (T(_, x, a, b)) = x
fun deleteMin E = raise Empty
  | deleteMin (T(_, x, a, b)) = merge(a,b)

(* Exercise 3.3 *)
local
  fun fromListH ([], cur) = cur
    | fromListH ([x], cur) = x :: cur
    | fromListH (x :: y :: xs, cur) =  fromListH(xs, merge(x, y) :: cur)

  fun fromListH2 [] = E
    | fromListH2 [x] = x
    | fromListH2 l = fromListH2(fromListH(l, List.empty))

in
fun fromList l = let val heaps = map(fn x => T(1,x,E,E)) l in fromListH2(heaps) end
end

end
    
    (* Excercise 3.4 *)
    (* 1. *)
    (* by induction. for 0 obvious. 
       step: assume for n.
       then: get left and right subtrees. 
       1) left subtree has k_l elements and right subtree has n + 1 - k = k_r elements.
       2) k_l < k_r, k_r <= [(n-1)/2].
       3) right spine length of right subtree is less equal to [log([(n-1)/2])], 
       4) lenght of right spine of whole tree is less equal to [log([(n-1)/2])] + 1
       5) proof that [log(n + 1)] >= [log([(n-1)/2])] + 1
          [log(n+1)] = [log(n/2 + 1/2) + 1] >? [log([(n-1)/2])] + 1
          [log(n/2 + 1/2)] + 1 = [ log((n-1)/2) ] + 1 >= [log([(n-1)/2])] + 1 ∎ *)
(* 2. *)

    
functor WeightBiasedHeap(Element: Ordered): Heap =
struct

structure Elem = Element
datatype Heap = E | T of int * Elem.T * Heap * Heap

val empty = E
                
fun isEmpty E = true
  | isEmpty _ = false
                                                   
fun size E = 0
  | size (T(k,_,_,_)) = k
fun makeT x a b =
    let val totalSize = size b + size a + 1 in
      if size a >= size b then T(totalSize, x, a, b) else T (totalSize, x, b, a)
    end

(* Old implementation *)
(* fun merge (h, E) = h *)
(*   | merge (E, h) = h *)
(*   | merge (h1 as T(_, x, a1, b1), h2 as T(_, y, a2, b2)) = *)
(*     if Elem.leq(x,y) *)
(*     then makeT(x, a1, merge(b1, h2)) *)
(*     else makeT(y, a2, merge(h1, b2)) *)

(* Excersice 3.4 c *)
local
  fun mergeH (h, E, nodes) = foldl(fn (func, head) => func(head))(h)(nodes)
    | mergeH (E, h, nodes) = foldl(fn (func, head) => func(head))(h)(nodes)
    | mergeH (h1 as T(_, x, a1, b1), h2 as T(_, y, a2, b2), cur) =
      if Elem.leq(x,y)
      then mergeH(b1, h2, (makeT x a1) :: cur)
      else mergeH(h1, b2, (makeT y a2) :: cur) 
in
  fun merge(h1,h2) = mergeH(h1,h2,[])
end

(* fun insert (x, h) = merge(T(1, x, E, E), h) *)
(* Exercise 3.2 *)
fun insert (x, E) = T(1, x, E, E)
  | insert(x, T(_, y, a, b)) = if Elem.leq(x, y)
                               then makeT(x)(a)(insert(y, b))
                               else makeT(y)(a)(insert(x, b))

fun findMin E = raise Empty
  | findMin (T(_, x, a, b)) = x
fun deleteMin E = raise Empty
  | deleteMin (T(_, x, a, b)) = merge(a,b)

(* Exercise 3.3 *)
local
  fun fromListH ([], cur) = cur
    | fromListH ([x], cur) = x :: cur
    | fromListH (x :: y :: xs, cur) =  fromListH(xs, merge(x, y) :: cur)

  fun fromListH2 [] = E
    | fromListH2 [x] = x
    | fromListH2 l = fromListH2(fromListH(l, List.empty))

in
fun fromList l = let val heaps = map(fn x => T(1,x,E,E)) l in fromListH2(heaps) end
end

end

    (* Excersice 3.2 d *)
    (* Idk. My version is tail recursive. It consumes heap space. *)
    (*  *)
