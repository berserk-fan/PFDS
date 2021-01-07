Control.lazysml := true;
open Lazy;

fun force($x) = x

fun lazy sum($m, $n) = $(m + n)


signature STREAM =
sig
  datatype 'a StreamCell = Nil | Cons of 'a * 'a Stream
  withtype 'a Stream = 'a StreamCell susp

  val concat : 'a Stream * 'a Stream -> 'a Stream
  val take : int * 'a Stream -> 'a Stream
  val drop : int * 'a Stream -> 'a Stream
end

signature SORT_STREAM =
sig
  structure Elem: Ordered
  val sort: Elem.T Stream -> Elem.T Stream
end


structure Stream: STREAM =
struct
  datatype 'a StreamCell = Nil | Cons of 'a * 'a Stream
  withtype 'a Stream = 'a StreamCell susp

fun lazy concat(($Nil), t) = t
       | concat(($(Cons(x,s))), t) = $(Cons(x, s <\concat\> t))

fun lazy take(0, s) = $(Nil)
       | take(n, $(Nil)) = $(Nil)
       | take(n, $(Cons(x,s)))  = $(Cons(x, take(n-1, s)))

fun lazy drop(0, s) = s
       | drop(n, $(Nil)) = $(Nil)
       | drop(n, $(Cons(x,s)))  = drop(n - 1, s)

end

functor INSERTION_SORT_STREAM(Element: Ordered): SORT_STREAM =
struct

structure Elem = Element
local
  fun lazy insert(x,$(Nil)) = $(Cons(x, $Nil))
    | insert(x, a as $(Cons(x', s)))  = if(Elem.leq(x, x'))
                                        then $(Cons(x, a))
                                        else $(Cons(x', insert(x, s)))
in

(*    force first elem of sort(stream)
      force first elem of stream
      force insert first elem of stream, to sort(tail stream)
      force first element of sort(tail) to be evaluated
      deside which element is head of sort(stream)
      return this element
   So (force first elem of Sort(#N)) = (force first elem of Sort(#N-1)) + O(1) = O(N).
   This will return first node with suspended rest.
*)
fun lazy sort($(Nil)) = $(Nil)
       | sort($(Cons(x,s))) = insert(x, sort(s))
end

end
    (* Ex. 4.1 *)
    (* fun lazy drop(0, s) = s
          | drop(n, $(Nil)) = $(Nil)
          | drop(n, $(Cons(x,s)))  = drop(n - 1, s)

  is the same as
  
  fun drop(x, y) = $(case($x,$y) of 
                           (0, s) => force($s)
                         | (n, $(Nil)) => force($($(Nil)))
                         | (n, $(Cons(x,s))) = force($(drop(n-1, s))))

  is the same as

  fun drop(x, y) = $(case($x,$y) of 
                           (0, s) => s
                          | (n, $(Nil)) => $Nil
                          | (n, $(Cons(x,s))) = (drop(n-1, s)))

  is the same as 

  fun drop(x, y) = let fun drop'(0, s) => s
                         | drop'(n, $(Nil)) => $Nil
                         | drop'(n, $(Cons(x,s))) = (drop(n-1, s)))
                   in $(case($x,$y) of force($(drop'(x,y)))
                   end

  is the same as

  lazy fun drop($n, $s) = let fun drop'(0, s) => s
                         | drop'(n, $(Nil)) => $Nil
                         | drop'(n, $(Cons(x,s))) = (drop(n-1, s)))
                        in drop'(x,y)
                        end

*)
