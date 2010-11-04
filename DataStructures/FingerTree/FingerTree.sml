
structure FingerTree :> FingerTree =
struct

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
    fun insertL (Empty) v = Singleton(v)
      | insertL (Singleton(x)) v = FingerTree(One(v), Empty, One(x))
      | insertL (FingerTree(fingerL, Empty, (fingerR as One(z)))) v =
        (case fingerL of
           Four(a, b, c, d) => FingerTree(Two(v, a), Empty, Four(b, c, d, z))
         | f => FingerTree(finL f v, Empty, fingerR))
      | insertL (FingerTree(fingerL, tree, fingerR)) v =
        (case fingerL of
           Four(a, b, c, d) =>
           let val tree' = insertL tree (Node(c, d)) in
             FingerTree(Three(v, a, b), tree', fingerR)
           end
         | l => FingerTree(finL l v, tree, fingerR))
  in
  fun insert t v = insertL t (Leaf(v))
  end


  local
    fun viewLt Empty = raise BailOut
      | viewLt (Singleton(x)) = (x, Empty)
      | viewLt (FingerTree(fingerL, tree, fingerR)) =
        (case fpopL fingerL of
           (x, SOME f)  => (x, FingerTree(f, tree, fingerR))
         | (x, NONE) =>
           (case tree of
              Empty => (case fpopL fingerR of
                          (y, SOME f) => (x, FingerTree(One(y), Empty, f))
                        | (y, NONE) => (x, Singleton(y)))
            | Singleton(Node(a,b)) => (x, FingerTree(Two(a,b), Empty, fingerR))
            | tree =>
              (case viewLt tree of
                 (Node(a,b), tree') => (x, FingerTree(Two(a, b), tree', fingerR))
               | _ => raise BailOut)
        ))
  in
  fun viewL t =
      case viewLt t of
        (Leaf(x), t) => (x, t)
      | _ => raise BailOut
  end

  local
    fun viewRt Empty = raise BailOut
      | viewRt (Singleton(x)) = (x, Empty)
      | viewRt (FingerTree(fingerL, tree, fingerR)) =
        (case fpopR fingerR of
           (x, SOME f) => (x, FingerTree(fingerL, tree, f))
         | (x, NONE) =>
           (case tree of
              Empty => (case fpopR fingerL of
                          (y, SOME f) => (x, FingerTree(f, Empty, One(y)))
                        | (y, NONE)   => (x, Singleton(y)))
            | Singleton(Node(a,b)) =>
              (x, FingerTree(fingerL, Empty, Two(a,b)))
            | tree =>
              (case viewRt tree of
                 (Node(a,b), tree') => (x, FingerTree(fingerL, tree', Two(a,b)))
               | _ => raise BailOut)
        ))
  in
  fun viewR t =
      case viewRt t of
        (Leaf(x), t) => (x, t)
      | _ => raise BailOut
  end

  local
    fun toList' Empty l = l
      | toList' t l =
        let val (a,t') = viewL t in
          toList' t' (a::l)
        end
  in
  fun toList t = toList' t []
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
      List.foldl (fn (v,t) => insert t v) Empty lst

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
