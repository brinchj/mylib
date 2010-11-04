
structure FingerTree :> FingerTree =
struct

open General infix 2 $ infix 4 \< \> infix 5 ^* to

datatype 'a tree = Node of 'a tree * 'a tree
                 | Leaf of 'a

datatype 'a finger = One of 'a
                   | Two of 'a * 'a
                   | Three of 'a * 'a * 'a
                   | Four of 'a * 'a * 'a * 'a

datatype 'a fingertree = Empty
                       | Singleton of 'a
                       | FingerTree of 'a finger * 'a fingertree * 'a finger

type 'a t = 'a tree fingertree

val fingerMax = 3

(* something went wrong *)
exception BailOut

fun singleton x = Singleton(Leaf(x))

fun fingerToList f = case f of
                       One(a) => [a]
                     | Two(a,b) => [a,b]
                     | Three(a,b,c) => [a,b,c]
                     | Four(a,b,c,d) => [a,b,c,d]

fun finL f v = case f of
                 One(a) => Two(v, a)
               | Two(a, b) => Three(v, a, b)
               | Three(a, b, c) => Four(v, a, b, c)
               | _ => raise BailOut


fun isEmpty Empty = true
  | isEmpty _ = false

fun fpopL f =
    case f of
      One(a) => (a, NONE)
    | Two(a, b) => (a, SOME(One(b)))
    | Three(a,b,c) => (a, SOME(Two(b, c)))
    | Four(a, b, c, d) => (a, SOME(Three(b, c, d)))

fun fpopR f =
    case f of
      One(a) => (a, NONE)
    | Two(a,b) => (b, SOME(One(a)))
    | Three(a,b,c) => (c, SOME(Two(a,b)))
    | Four(a,b,c,d) => (d, SOME(Three(a,b,c)))

local
  fun ftL (l,m,r) = FingerTree(l, m, r)
  fun ftR (l,m,r) = FingerTree(r, m, l)
  fun fswapR (l,r) = (r, l)
  fun splitL (Four(a,b,c,d)) v = (Two(v, a), Three(b,c,d))
  fun splitR (Four(a,b,c,d)) v = (Three(a,b,c), Two(d, v))
  fun nodeL  (Four(a,b,c,d)) v = (Three(v, a, b), Node(c, d))
  fun nodeR  (Four(a,b,c,d)) v = (Three(c, d, v), Node(a, b))

  fun inserttFull ft fswap pop split node (FingerTree(fingerL, tree, fingerR)) v =
      let
        val (fingerL, fingerR) = fswap (fingerL, fingerR)
      in
        (case fingerL of
           Four(a, b, c, d) =>
           let
             val (f, n) = node fingerL v
             val tree' = insertt ft fswap pop split node tree n in
             ft(f, tree', fingerR)
           end
         | l => ft(finL l v, tree, fingerR))
      end
    | inserttFull _ _ _ _ _ _ _ = raise BailOut
    (*inserttFull ft fswap pop split node tree v = insertt ft fswap pop split node tree v*)
  and insertt ft fswap pop split node (Empty) v = Singleton(v)
    | insertt ft fswap pop split node (Singleton(x)) v = ft(One(v), Empty, One(x))
    | insertt ft fswap pop split node (tree as FingerTree(fingerL, Empty, fingerR)) v =
      let
        val (fingerL, fingerR) = fswap (fingerL, fingerR)
      in
        case fingerR of
          One(z) =>
          (case fingerL of
             Four(a, b, c, d) => let val (l,r) = split fingerL v
                                 in ft(l, Empty, r) end
           | f => ft(finL f v, Empty, fingerR))
        | _ => inserttFull ft fswap pop split node tree v
      end
    | insertt ft fswap pop split node tree v = inserttFull ft fswap pop split node tree v

  fun viewt ft fswap pop Empty = raise BailOut
    | viewt ft fswap pop (Singleton(x)) = (x, Empty)
    | viewt ft fswap pop (FingerTree(fingerL, tree, fingerR)) =
      let
        val (fingerL, fingerR) = fswap (fingerL, fingerR)
      in
        (case pop fingerL of
           (x, SOME f) => (x, ft(f, tree, fingerR))
         | (x, NONE) =>
           (case tree of
              Empty => (case pop fingerR of
                          (y, SOME f) => (x, ft(One(y), Empty, f))
                        | (y, NONE)   => (x, Singleton(y)))
            | Singleton(Node(a,b)) => (x, ft(Two(a,b), Empty, fingerR))
            | tree =>
              (case viewt ft fswap pop tree of
                 (Node(a,b), tree') => (x, ft(Two(a, b), tree', fingerR))
               | _ => raise BailOut)
        ))
      end
in

fun insertL t v = insertt ftL id fpopL splitL nodeL t (Leaf(v))
fun insertR t v = insertt ftR fswapR fpopR splitR nodeR t (Leaf(v))
val insert  = insertL

fun pick (Leaf(x), t) = (x, t)
  | pick _ = raise BailOut
fun viewL t = pick (viewt ftL id fpopL t)
fun viewR t = pick (viewt ftR fswapR fpopR t)

end

local
  fun toList' view Empty l = l
    | toList' view t l =
      let val (a,t') = view t in
        toList' view t' (a::l)
      end
in
fun toList t = toList' viewR t []
fun toListRev t = toList' viewL t []
end

fun toListRev Empty = []
  | toListRev t =
    let val (a,t') = viewR t in
      a :: (toListRev t')
    end

fun depth Empty = 0
  | depth (Singleton(x)) = 1
  | depth (FingerTree(_, tree, _)) = 1 + (depth tree)

local
  fun lengthi i Empty = 0
    | lengthi i (Singleton(x)) = i
    | lengthi i (FingerTree(fl, tree, fr)) =
      (i * (List.length (fingerToList fl))) +
      (i * (List.length (fingerToList fr))) + (lengthi (2*i) tree)
in
fun length t = lengthi 1 t
end

fun fromList lst =
    List.foldl (fn (v,t) => insertR t v) Empty lst

fun testA () =
    let
      val lst = List.tabulate (5000, (fn x => x))
      val rnd = List.shuffle (lst @ lst)
      val seq = List.foldl (fn (v,t) => insert t v) Empty (List.rev rnd)
    in
      rnd = (toList seq)
    end

fun testB () =
    let
      val lst = List.tabulate (5000, (fn x => x))
      val rnd = List.shuffle (lst @ lst)
      val seq = List.foldl (fn (v,t) => insert t v) Empty (rnd)
    in
      rnd = (toListRev seq)
    end
end
