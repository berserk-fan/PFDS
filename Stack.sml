signature Stack =
sig
  type 'a Stack
  val empty: 'a Stack
  val isEmpty: 'a Stack -> bool
  val cons: 'a * 'a Stack -> 'a Stack
  val head: 'a Stack -> 'a (* raises Empty if stack is empty *)
  val tail: 'a Stack -> 'a Stack (* raises Empty if stack is empty *)
  val ++ : 'a Stack * 'a Stack -> 'a Stack
end
    
structure List: Stack =
struct
type 'a Stack = 'a list
val empty = []
fun isEmpty s = null s
fun cons(x,s) = x :: s
fun head s = hd s
fun tail s = tl s
fun [] ++ ys = ys
  | (x :: xs) ++ ys = x :: (xs ++ ys);
end

(* Ex 2.1 suffixes *)
fun suffixes [] = [[]]
  | suffixes xs = xs :: suffixes(tl xs)

