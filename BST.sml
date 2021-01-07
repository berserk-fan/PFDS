signature Set =
sig
  type Elem
  type Set

  val empty: Set
  val insert: Elem * Set -> Set
  val member: Elem * Set -> bool
  val size: Set -> int
end

signature Ordered =
sig
  type T
  val eq: T * T -> bool
  val lt: T * T -> bool
  val leq: T * T -> bool
end

functor UnbalancedSet(Element: Ordered): Set =
struct
type Elem = Element.T
datatype Tree = E | T of Tree * Elem * Tree
type Set = Tree

exception NotFound
              
val empty = E

(* fun member(x,E) = false *)
(*   | member (x, T(a,y,b)) = *)
(*     if Element.lt (x,y) then member(x,a) *)
(*     else if Element.lt(y,x) then member(x, b) *)
(*     else true *)

                
(* Exercise 2.2 *)
local
  fun memberH(x, E, h) = if Element.eq(x, h) then x else raise NotFound
    | memberH(x, T(a,y, b), h)  =
      if Element.lt (x,y) then memberH(x, a, h)
      else memberH(x, b, y)
in
fun member(x,E) = raise NotFound
  | member(x, T(a,y,b)) =
    if Element.lt (x,y) then member(x,a)
    else memberH(x,b,y)
end

(* Ex 2.4, 2.5 *)
local
  exception AlreadyExists

  fun insertH1 (x, E, h) =
      if Element.eq(x,h)
      then raise AlreadyExists
      else T(E,x,E)
    | insertH1 (x, s as T(a,y,b), h) =
      if Element.lt(x,y) then T(insertH1(x,a, h),y,b)
      else T(a,y,insertH1(x, b, y))

  fun insertH2 (x,E) = T(E,x,E)
    | insertH2 (x,T(a,y,b)) =
      if Element.lt(x,y)
      then T(insertH2(x, a), y, b)
      else T(a, y, insertH1(x, b, y))

  fun insertSafe(x, S) = insertH2(x, S) handle AlreadyExists => S
in
fun insert(x,C) = insertSafe(x,C)
end

(* Exercise 2.5 *)
fun complete(x, 0) = E
  | complete(x, k) =
    let val n = complete(x, k - 1)
    in T(n,x,n)
    end

(* Ex 2.6 *)
local
  fun create2 (x, 0) = (E, T(E, x, E))
    | create2 (x, k) =
      let val (h1,h2) = create2(x, (k - 1) div 2)
          val n2 = if k mod 2 = 0 then h2 else h1
      in
        (T(h1, x, n2), T(h2, x, n2))
      end
in

fun balanced (x, 0) = E
  | balanced (x, k) =
    if k mod 2 = 1
    then let
      val h = balanced(x, k div 2)
    in T(h,x,h)
    end
    else let
      val (h1, h2) = create2(x, k div 2 - 1)
    in T(h1, x, h2)
    end
             
end

(* Helpers *)
fun size(E) = 0
  | size (T(a,y,b)) = size(a) + size(b) + 1

fun isBalanced(E) = true
  | isBalanced (T(a,y,b)) = isBalanced(a) andalso isBalanced(b) andalso abs (size(a) - size(b)) <= 1

end

structure IntOrdered: Ordered =
struct
type T = int
fun eq(a,b) = a = b
fun lt(a,b) = a < b
fun leq(a,b) = a <= b
end



                      
     
