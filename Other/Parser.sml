structure Parser =
ParserFn(
struct
infix 0 |||
infix 1 --- |-- --|
infix 2 >>> --> ???

datatype either = datatype Either.t

type ('a, 'x) reader = ('a, 'x) StringCvt.reader
type position = int
type 'x state = 'x * position
fun position (_, p) = p
fun stream (s, _) = s

fun justFailed (_, p1) (Left _, (_, p2)) = p2 = p1
  | justFailed _ _ = false

structure Map = IntMap

datatype 'x errors = F of 'x
                   | E of 'x * string
                   | C of 'x errors * 'x errors
fun emptyE s = F s
fun someE s e = E (s, e)
fun joinE es1 es2 = C (es1, es2)

type ('a, 'x) consumer = 'x state ->
                         ('x state errors,
                          'a) either * 'x state

type ('a, 'b, 'x) parser = ('a, 'x) consumer -> ('b, 'x) consumer

type ('a, 'b) result = ({position : position,
                         token    : 'a option,
                         expected : string list} list,
                        'b) Either.t



fun fail con state =
    (Left $ emptyE state, state)

fun (p ??? e) con state =
    case p con state of
      (Left (F _), state') =>
      (Left $ someE state e, state')
    | (r as (Left _, state')) =>
      if position state = position state' then
        (Left $ someE state e, state')
      else
        r
    | x => x

fun getState con state = (Right state, state)
fun setState state' con _ = (Right (), state')

fun any con state = con state
fun notFollowedBy p con state =
    case p con state of
      (Right _, _) => fail con state
    | (Left _, _)  => (Right (), state)

fun (p1 ||| p2) con state =
    case p1 con state of
      (r1 as (Left em1, state')) =>
      if position state = position state' then
        case p2 con state' of
          (Left em2, state'') =>
          (Left $ joinE em1 em2, state'')
        | x => x
      else
        r1
    | x => x

fun try p con state =
    case p con state of
      (Left errs, _) => (Left errs, state)
    | x => x

fun return x con state = (Right x, state)

fun (p --> f) con state =
    case p con state of
      (Right x, state') => (f x) con state'
    | (Left e, state') => (Left e, state')

(* ========================================================== *)

fun parse p r s =
    let
      fun con (s, p) =
          case r s of
            SOME (x, s') => (Right x, (s', p + 1))
          | NONE => (Left $ emptyE (s, p), (s, p))
      val state = (s, 0)

      fun errs es =
          let
            val tok = Option.map fst o r

            fun flatten es =
                let
                  fun loop (F s) es = (s, NONE) :: es
                    | loop (E (s, e)) es = (s, SOME e) :: es
                    | loop (C (es1, es2)) es =
                      loop es1 $ loop es2 es
                in
                  loop es nil
                end

            fun compare ((_, p1), _) ((_, p2), _) = Int.compare (p1, p2)
            fun poseq s1 s2 = curry op= EQUAL $ compare s1 s2

            fun group (xs as (s, _) :: _) =
                (s, List.mapPartial snd xs)
              | group _ = raise Fail "impossible"

            fun pretty ((stream, pos), es) =
                {position = pos,
                 token    = tok stream,
                 expected = es}
          in
            List.map pretty $
                     List.map group $
                     List.group poseq $
                     List.sort compare $
                     flatten es
          end
    in
      case p con state of
        (Left em, (s', _)) =>
        (* (Left nil, s') *)
        (Left $ errs em, s')
      | (Right x, (s', _)) => (Right x, s')
    end

fun scan p r s =
    case parse p r s of
      (Left _, _) => NONE
    | (Right x, s') => SOME (x, s')

exception Error of string
fun test show p r s =
    case parse p r s of
      (Left es, _) =>
      let
        open Layout
        infix ^^ ++ \ & \\ &&

        fun one {position = p, token = top, expected = es} =
            let
              fun loop [x, y] = txt x & txt "or" & txt y
                | loop [x] = txt x
                | loop (x :: xs) = txt x && comma & loop xs
                | loop _ = empty
              fun tok NONE = txt "end of stream"
                | tok (SOME t) = txt $ show t
            in
              hang
                2
                (txt "Failed at position"
                     & int p && colon \
                     txt "Got" & tok top &&
                     (if null es then
                        empty
                      else
                        txt ", but expected" & loop es
                     ) && dot
                )
            end
      in
        raise Error $ Layout.pretty (SOME 80) (
              case es of
                [e] => one e
              | _   => txt "Failed in" & int (length es) & txt "places:" \
                           indent 1 (itemize "o" (map one es))
              )
      end
    | (Right x, _) => x
end
)
