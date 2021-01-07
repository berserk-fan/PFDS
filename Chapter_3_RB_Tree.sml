functor RBSet(Element: Ordered): Set =
struct
type Elem = Element.T

datatype Color = R | B
datatype Tree = E | T of Color * Tree * Elem * Tree
type Set = Tree

(* 
Excerise 3.8 
size of tree = n
number of black nodes on longest path = k
#(k) - number of black nodes in tree with given k

1) root is red => #(k) >= 2*#(k) + 1
2) root is black => #(k) >= 2*#(k-1) + 1
   so #(k) >= 2*#(k-1) + 1. #(0) = 0
   #(k) >= 2^k - 1
   n = #(k) >= 2^k - 1 => from one of previous ex. k <= [log(n+1)]
   thus max number of black nodes on path is [log(n+1)] and then max number of nodes on path 
   is \ 2*[log(n+1)] + 1 \ R-B-R-B-R
  ok we got weaker solution.  \ longest_path < 2 * [log(n+1)] + 1 \ => .
*)

val empty = E
fun isEmpty E = true
  | isEmpty _ = false

fun size E = 0
  | size (T(_, a, x, b)) = size(a) + size(b) + 1
                                                   
                                                   
fun lbalance (B, T(R, T(R, a, x, b), y, c), z, d) = T(R, T(B,a,x,b), y, T(B,c,z,d))
  | lbalance (B, T(R, a, x, T(R, b, y, c)), z, d) = T(R, T(B,a,x,b), y, T(B,c,z,d))
  | lbalance body = T body

fun rbalance (B, a, x, T(R, b, y, T(R, c, z, d))) = T(R, T(B,a,x,b), y, T(B,c,z,d))
  | rbalance (B,a,x,T(R, T(R, b, y, c), z, d)) = T(R, T(B,a,x,b), y, T(B,c,z,d))
  | rbalance body = T body

fun insert(x: Elem, s) =
    let fun ins E = T(R,E,x,E)
          | ins (s as T(color, a, y, b)) =
            if Element.lt(x,y) then lbalance(color, ins a, y ,b)
            else if Element.lt(y,x) then rbalance(color, a, y, ins b)
            else s
        val T(_, a,y,b) = ins s (* always non-empty *)
    in T(B, a, y, b)
    end

fun member (x, E) = false
  | member (x, T(_, a,y,b)) = if Element.lt(x,y) then member(x,a)
                              else if Element.lt(y,x) then member(x, b)
                              else true

exception RedRedViolation;
exception BlackViolation;

fun checkRedRedInvariant E = ()
  | checkRedRedInvariant (T(R, T(R, _, _, _), _, _)) = raise RedRedViolation
  | checkRedRedInvariant (T(R, _, _, T(R, _, _ ,_))) = raise RedRedViolation
  | checkRedRedInvariant (T(_, a, x, b)) = let val _ = checkRedRedInvariant(a)
                                               val _ = checkRedRedInvariant(b)
                                           in ()
                                           end

local
  fun blackInvariantH E = 0
    | blackInvariantH (T(B, a, x, b)) = Int.max(blackInvariantH(a), blackInvariantH(b)) + 1
    | blackInvariantH (T(R, a, x, b)) = Int.max(blackInvariantH(a), blackInvariantH(b))
in
fun checkBlackInvariant E = ()
  | checkBlackInvariant (T(_, a, x, b)) =
    if not(blackInvariantH(a) = blackInvariantH(b)) then raise BlackViolation
    else let val _ = checkBlackInvariant(a)
             val _ = checkBlackInvariant(b)
         in ()
         end
end

fun checkForRB x = let val _ = checkRedRedInvariant(x)
                       val _ = checkBlackInvariant(x)
                   in ()
                   end

local
  fun constructBBST(0, xs, _, _) = (E, xs)      
    | constructBBST(size, xs as (minH, elem) :: xs', quota, pC) =
      let val leftSize = (size - 1) div 2
          val rightSize = size - leftSize - 1
          val thisColor = if pC = R then B
                          else if minH < quota then raise ColoringError
                          else if minH = quota then B
                          else R
          val newQuota = if thisColor = R then quota else quota - 1
          val (rightTree, ys) = constructBBST(rightSize, xs', newQuota, thisColor)
          val (leftTree, zs) = constructBBST(leftSize, ys, newQuota, thisColor)
      in (T(thisColor, leftTree, elem, rightTree), zs)
      end

  (* returns [root, ...rightTree, ...leftTree] as list with minHeight data. *)
  fun helper(0, xs, ress) = (0, xs, ress)
    | helper(size, xs, ress)  =
      let val leftSize = (size - 1) div 2
          val rightSize = size - leftSize - 1
          val (lh, y :: ys, ress') = helper(leftSize, xs, ress)
          val (_, zs, ress'') = helper(rightSize, ys, ress')
      in (lh + 1, zs,   (lh + 1, y) :: ress'')
      end

  exception NotAllConsumed
  fun construct(xs) =
      let
        val l = length xs
        val (quota, rest, ys) = helper(l, xs, [])
        val (res, rest') = constructBBST(l, ys, quota, B)
      in if not(null (rest) orelse null(rest')) then raise NotAllConsumed
         else res
      end

in
fun fromOrdList(x) = let val res = construct(x)
                         val _ = checkForRB(res)
                     in res
                     end
end    
end
