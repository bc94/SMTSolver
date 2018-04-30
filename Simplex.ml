module Simplex : sig
  type int
  type nat
  type rat
  type ('a, 'b) fmap
  type ('a, 'b) mapping
  type linear_poly
  type constrainta = LT of linear_poly * rat | GT of linear_poly * rat |
    LEQ of linear_poly * rat | GEQ of linear_poly * rat |
    EQ of linear_poly * rat | LTPP of linear_poly * linear_poly |
    GTPP of linear_poly * linear_poly | LEQPP of linear_poly * linear_poly |
    GEQPP of linear_poly * linear_poly | EQPP of linear_poly * linear_poly
  val nat_of_integer : Big_int.big_int -> nat
  val simplex : constrainta list -> (nat, rat) mapping option
  val lp_monom : rat -> nat -> linear_poly
  val rat_of_int_pair : Big_int.big_int -> Big_int.big_int -> rat
end = struct

type int = Int_of_integer of Big_int.big_int;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec equal_inta
  k l = Big_int.eq_big_int (integer_of_int k) (integer_of_int l);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

type nat = Nat of Big_int.big_int;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat
  m n = Big_int.le_big_int (integer_of_nat m) (integer_of_nat n);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let rec times_int
  k l = Int_of_integer
          (Big_int.mult_big_int (integer_of_int k) (integer_of_int l));;

let rec less_eq_int
  k l = Big_int.le_big_int (integer_of_int k) (integer_of_int l);;

type rat = Frct of (int * int);;

let rec quotient_of (Frct x) = x;;

let rec less_eq_rat
  p q = (let a = quotient_of p in
         let (aa, c) = a in
         let b = quotient_of q in
         let (ba, d) = b in
          less_eq_int (times_int aa d) (times_int c ba));;

let rec less_int
  k l = Big_int.lt_big_int (integer_of_int k) (integer_of_int l);;

let rec less_rat
  p q = (let a = quotient_of p in
         let (aa, c) = a in
         let b = quotient_of q in
         let (ba, d) = b in
          less_int (times_int aa d) (times_int c ba));;

let ord_rat = ({less_eq = less_eq_rat; less = less_rat} : rat ord);;

let rec eq _A a b = equal _A a b;;

let rec equal_prod _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_rat
  a b = equal_prod equal_int equal_int (quotient_of a) (quotient_of b);;

type qDelta = QDelta of rat * rat;;

let rec equal_QDeltaa
  (QDelta (x1, x2)) (QDelta (y1, y2)) = equal_rat x1 y1 && equal_rat x2 y2;;

let equal_QDelta = ({equal = equal_QDeltaa} : qDelta equal);;

let zero_int : int = Int_of_integer Big_int.zero_big_int;;

type num = One | Bit0 of num | Bit1 of num;;

let one_int : int = Int_of_integer (Big_int.big_int_of_int 1);;

let zero_rat : rat = Frct (zero_int, one_int);;

let one_rat : rat = Frct (one_int, one_int);;

let one_QDeltaa : qDelta = QDelta (one_rat, zero_rat);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_QDelta = ({one = one_QDeltaa} : qDelta one);;

let rec sgn_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int then Big_int.zero_big_int
        else (if Big_int.lt_big_int k Big_int.zero_big_int
               then (Big_int.minus_big_int (Big_int.big_int_of_int 1))
               else (Big_int.big_int_of_int 1)));;

let rec apsnd f (x, y) = (x, f y);;

let rec comp f g = (fun x -> f (g x));;

let rec divmod_integer
  k l = (if Big_int.eq_big_int k Big_int.zero_big_int
          then (Big_int.zero_big_int, Big_int.zero_big_int)
          else (if Big_int.eq_big_int l Big_int.zero_big_int
                 then (Big_int.zero_big_int, k)
                 else comp (comp apsnd Big_int.mult_big_int) sgn_integer l
                        (if Big_int.eq_big_int (sgn_integer k) (sgn_integer l)
                          then Big_int.quomod_big_int (Big_int.abs_big_int k)
                                 (Big_int.abs_big_int l)
                          else (let (r, s) =
                                  Big_int.quomod_big_int (Big_int.abs_big_int k)
                                    (Big_int.abs_big_int l)
                                  in
                                 (if Big_int.eq_big_int s Big_int.zero_big_int
                                   then (Big_int.minus_big_int r,
  Big_int.zero_big_int)
                                   else (Big_int.sub_big_int
   (Big_int.minus_big_int r) (Big_int.big_int_of_int 1),
  Big_int.sub_big_int (Big_int.abs_big_int l) s))))));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_int
  k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));;

let rec uminus_int
  k = Int_of_integer (Big_int.minus_big_int (integer_of_int k));;

let rec gcd_int
  (Int_of_integer x) (Int_of_integer y) =
    Int_of_integer (Big_int.gcd_big_int x y);;

let rec snd (x1, x2) = x2;;

let rec normalize
  p = (if less_int zero_int (snd p)
        then (let a = gcd_int (fst p) (snd p) in
               (divide_int (fst p) a, divide_int (snd p) a))
        else (if equal_inta (snd p) zero_int then (zero_int, one_int)
               else (let a = uminus_int (gcd_int (fst p) (snd p)) in
                      (divide_int (fst p) a, divide_int (snd p) a))));;

let rec times_rat
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize (times_int aa ba, times_int c d));;

let rec qdsnd (QDelta (a, b)) = b;;

let rec qdfst (QDelta (a, b)) = a;;

let rec scaleRat_QDeltaa
  r qd = QDelta (times_rat r (qdfst qd), times_rat r (qdsnd qd));;

let rec uminus_rat p = Frct (let a = quotient_of p in
                             let (aa, b) = a in
                              (uminus_int aa, b));;

let rec uminus_QDeltaa
  qd = QDelta (uminus_rat (qdfst qd), uminus_rat (qdsnd qd));;

let rec less_eq_QDelta
  qd1 qd2 =
    less_rat (qdfst qd1) (qdfst qd2) ||
      equal_rat (qdfst qd1) (qdfst qd2) && less_eq_rat (qdsnd qd1) (qdsnd qd2);;

let rec minus_int
  k l = Int_of_integer
          (Big_int.sub_big_int (integer_of_int k) (integer_of_int l));;

let rec minus_rat
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize
                 (minus_int (times_int aa d) (times_int ba c), times_int c d));;

let rec minus_QDeltaa
  qd1 qd2 =
    QDelta
      (minus_rat (qdfst qd1) (qdfst qd2), minus_rat (qdsnd qd1) (qdsnd qd2));;

let zero_QDeltaa : qDelta = QDelta (zero_rat, zero_rat);;

let rec plus_int
  k l = Int_of_integer
          (Big_int.add_big_int (integer_of_int k) (integer_of_int l));;

let rec plus_rat
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize
                 (plus_int (times_int aa d) (times_int ba c), times_int c d));;

let rec plus_QDeltaa
  qd1 qd2 =
    QDelta
      (plus_rat (qdfst qd1) (qdfst qd2), plus_rat (qdsnd qd1) (qdsnd qd2));;

let rec less_QDelta
  qd1 qd2 =
    less_rat (qdfst qd1) (qdfst qd2) ||
      equal_rat (qdfst qd1) (qdfst qd2) && less_rat (qdsnd qd1) (qdsnd qd2);;

type 'a scaleRat = {scaleRat : rat -> 'a -> 'a};;
let scaleRat _A = _A.scaleRat;;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add;
    order_ordered_ab_semigroup_add : 'a order};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

type 'a rational_vector =
  {scaleRat_rational_vector : 'a scaleRat;
    ab_group_add_rational_vector : 'a ab_group_add};;

type 'a ordered_rational_vector =
  {rational_vector_ordered_rational_vector : 'a rational_vector;
    order_ordered_rational_vector : 'a order};;

type 'a linordered_rational_vector =
  {ordered_rational_vector_linordered_rational_vector :
     'a ordered_rational_vector;
    ordered_ab_semigroup_add_linordered_rational_vector :
      'a ordered_ab_semigroup_add;
    linorder_linordered_rational_vector : 'a linorder};;

type 'a lrv =
  {linordered_rational_vector_lrv : 'a linordered_rational_vector;
    one_lrv : 'a one};;

let plus_QDelta = ({plus = plus_QDeltaa} : qDelta plus);;

let semigroup_add_QDelta =
  ({plus_semigroup_add = plus_QDelta} : qDelta semigroup_add);;

let ab_semigroup_add_QDelta =
  ({semigroup_add_ab_semigroup_add = semigroup_add_QDelta} :
    qDelta ab_semigroup_add);;

let ord_QDelta = ({less_eq = less_eq_QDelta; less = less_QDelta} : qDelta ord);;

let preorder_QDelta = ({ord_preorder = ord_QDelta} : qDelta preorder);;

let order_QDelta = ({preorder_order = preorder_QDelta} : qDelta order);;

let ordered_ab_semigroup_add_QDelta =
  ({ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_QDelta;
     order_ordered_ab_semigroup_add = order_QDelta}
    : qDelta ordered_ab_semigroup_add);;

let cancel_semigroup_add_QDelta =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_QDelta} :
    qDelta cancel_semigroup_add);;

let minus_QDelta = ({minus = minus_QDeltaa} : qDelta minus);;

let cancel_ab_semigroup_add_QDelta =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_QDelta;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_QDelta;
     minus_cancel_ab_semigroup_add = minus_QDelta}
    : qDelta cancel_ab_semigroup_add);;

let zero_QDelta = ({zero = zero_QDeltaa} : qDelta zero);;

let monoid_add_QDelta =
  ({semigroup_add_monoid_add = semigroup_add_QDelta;
     zero_monoid_add = zero_QDelta}
    : qDelta monoid_add);;

let comm_monoid_add_QDelta =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_QDelta;
     monoid_add_comm_monoid_add = monoid_add_QDelta}
    : qDelta comm_monoid_add);;

let cancel_comm_monoid_add_QDelta =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_QDelta;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_QDelta}
    : qDelta cancel_comm_monoid_add);;

let uminus_QDelta = ({uminus = uminus_QDeltaa} : qDelta uminus);;

let group_add_QDelta =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_QDelta;
     minus_group_add = minus_QDelta; monoid_add_group_add = monoid_add_QDelta;
     uminus_group_add = uminus_QDelta}
    : qDelta group_add);;

let ab_group_add_QDelta =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_QDelta;
     group_add_ab_group_add = group_add_QDelta}
    : qDelta ab_group_add);;

let scaleRat_QDelta = ({scaleRat = scaleRat_QDeltaa} : qDelta scaleRat);;

let rational_vector_QDelta =
  ({scaleRat_rational_vector = scaleRat_QDelta;
     ab_group_add_rational_vector = ab_group_add_QDelta}
    : qDelta rational_vector);;

let ordered_rational_vector_QDelta =
  ({rational_vector_ordered_rational_vector = rational_vector_QDelta;
     order_ordered_rational_vector = order_QDelta}
    : qDelta ordered_rational_vector);;

let linorder_QDelta = ({order_linorder = order_QDelta} : qDelta linorder);;

let linordered_rational_vector_QDelta =
  ({ordered_rational_vector_linordered_rational_vector =
      ordered_rational_vector_QDelta;
     ordered_ab_semigroup_add_linordered_rational_vector =
       ordered_ab_semigroup_add_QDelta;
     linorder_linordered_rational_vector = linorder_QDelta}
    : qDelta linordered_rational_vector);;

let lrv_QDelta =
  ({linordered_rational_vector_lrv = linordered_rational_vector_QDelta;
     one_lrv = one_QDelta}
    : qDelta lrv);;

let ord_integer =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

type color = R | B;;

type ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;;

type ('b, 'a) rbt = RBT of ('b, 'a) rbta;;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a fset = Abs_fset of 'a set;;

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

type ('a, 'b) mapping = Mapping of ('a, 'b) rbt;;

type 'a atom = Leq of nat * 'a | Geq of nat * 'a;;

type linear_poly = LinearPoly of (nat, rat) fmap;;

type constrainta = LT of linear_poly * rat | GT of linear_poly * rat |
  LEQ of linear_poly * rat | GEQ of linear_poly * rat | EQ of linear_poly * rat
  | LTPP of linear_poly * linear_poly | GTPP of linear_poly * linear_poly |
  LEQPP of linear_poly * linear_poly | GEQPP of linear_poly * linear_poly |
  EQPP of linear_poly * linear_poly;;

type 'a ns_constraint = LEQ_ns of linear_poly * 'a |
  GEQ_ns of linear_poly * 'a;;

type ('a, 'b) state_ext =
  State_ext of
    (nat * linear_poly) list * (nat -> 'a option) * (nat -> 'a option) *
      (nat, 'a) mapping * bool * 'b;;

type 'a istate_ext =
  Istate_ext of nat * (nat * linear_poly) list * qDelta atom list * 'a;;

type ('a, 'b) direction_ext =
  Direction_ext of
    ('a -> 'a -> bool) * (('a, unit) state_ext -> nat -> 'a option) *
      (('a, unit) state_ext -> nat -> 'a option) *
      (((nat -> 'a option) -> nat -> 'a option) ->
        ('a, unit) state_ext -> ('a, unit) state_ext) *
      (nat -> 'a -> 'a atom) * 'b;;

let rec id x = (fun xa -> xa) x;;

let rec plus_nat
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Big_int.big_int_of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec minus_nat
  m n = Nat (max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

let zero_nat : nat = Nat Big_int.zero_big_int;;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec image f (Set xs) = Set (map f xs);;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec vala qd delta = plus_rat (qdfst qd) (times_rat delta (qdsnd qd));;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_ins _A
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (if less _A k x then balance (rbt_ins _A f k v l) x y r
          else (if less _A x k then balance l x y (rbt_ins _A f k v r)
                 else Branch (B, l, x, f k y v, r)))
    | f, k, v, Branch (R, l, x, y, r) ->
        (if less _A k x then Branch (R, rbt_ins _A f k v l, x, y, r)
          else (if less _A x k then Branch (R, l, x, y, rbt_ins _A f k v r)
                 else Branch (R, l, x, f k y v, r)));;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_insert_with_key _A f k v t = paint B (rbt_ins _A f k v t);;

let rec rbt_insert _A = rbt_insert_with_key _A (fun _ _ nv -> nv);;

let rec impl_of _B (RBT x) = x;;

let rec insert _A
  xc xd xe =
    RBT (rbt_insert _A.order_linorder.preorder_order.ord_preorder xc xd
          (impl_of _A xe));;

let rec rbt_lookup _A
  x0 k = match x0, k with Empty, k -> None
    | Branch (uu, l, x, y, r), k ->
        (if less _A k x then rbt_lookup _A l k
          else (if less _A x k then rbt_lookup _A r k else Some y));;

let rec lookup _A
  x = rbt_lookup _A.order_linorder.preorder_order.ord_preorder (impl_of _A x);;

let rec of_int a = Frct (a, one_int);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let rec merge _A qs ps = foldr (fun (a, b) -> update _A a b) ps qs;;

let rec fset (Abs_fset x) = x;;

let rec fimage xb xc = Abs_fset (image xb (fset xc));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec hd (x21 :: x22) = x21;;

let rec tl = function [] -> []
             | x21 :: x22 -> x22;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec rbt_bulkload _A xs = foldr (fun (a, b) -> rbt_insert _A a b) xs Empty;;

let rec bulkload _A
  xa = RBT (rbt_bulkload _A.order_linorder.preorder_order.ord_preorder xa);;

let rec lookupa _A (Mapping t) = lookup _A t;;

let rec updatea _A k v (Mapping t) = Mapping (insert _A k v t);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge _A m n);;

let rec fset_of_list xa = Abs_fset (Set xa);;

let rec fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let rec tabulate _A ks f = Mapping (bulkload _A (map (fun k -> (k, f k)) ks));;

let rec divide_rat
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize (times_int aa d, times_int c ba));;

let rec delta_0
  qd1 qd2 =
    (let c1 = qdfst qd1 in
     let c2 = qdfst qd2 in
     let k1 = qdsnd qd1 in
     let k2 = qdsnd qd2 in
      (if less_rat c1 c2 && less_rat k2 k1
        then divide_rat (minus_rat c2 c1) (minus_rat k1 k2) else one_rat));;

let rec fmfilter
  p (Fmap_of_list m) = Fmap_of_list (filter (fun (k, _) -> p k) m);;

let rec fmdrop _A a = fmfilter (fun aa -> not (eq _A aa a));;

let rec the (Some x2) = x2;;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec fmlookup _A (Fmap_of_list m) = map_of _A m;;

let rec get_var_coeff
  lp v = (match fmlookup equal_nat lp v with None -> zero_rat | Some c -> c);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec size_list x = gen_length zero_nat x;;

let rec part _B
  f pivot x2 = match f, pivot, x2 with
    f, pivot, x :: xs ->
      (let (lts, (eqs, gts)) = part _B f pivot xs in
       let xa = f x in
        (if less _B.order_linorder.preorder_order.ord_preorder xa pivot
          then (x :: lts, (eqs, gts))
          else (if less _B.order_linorder.preorder_order.ord_preorder pivot xa
                 then (lts, (eqs, x :: gts)) else (lts, (x :: eqs, gts)))))
    | f, pivot, [] -> ([], ([], []));;

let rec nat_of_integer k = Nat (max ord_integer Big_int.zero_big_int k);;

let rec sort_key _B
  f xs =
    (match xs with [] -> [] | [_] -> xs
      | [x; y] ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then xs else [y; x])
      | _ :: _ :: _ :: _ ->
        (let (lts, (eqs, gts)) =
           part _B f
             (f (nth xs
                  (divide_nat (size_list xs)
                    (nat_of_integer (Big_int.big_int_of_int 2)))))
             xs
           in
          sort_key _B f lts @ eqs @ sort_key _B f gts));;

let rec sorted_list_of_set (_A1, _A2)
  (Set xs) = sort_key _A2 (fun x -> x) (remdups _A1 xs);;

let rec ordered_keys (_A1, _A2)
  m = sorted_list_of_set (_A1, _A2) (fset (fmdom m));;

let rec set_var_coeff
  v c lp =
    (if equal_rat c zero_rat then fmdrop equal_nat v lp
      else fmupd equal_nat v c lp);;

let rec add_monom
  c v lp = set_var_coeff v (plus_rat c (get_var_coeff lp v)) lp;;

let rec add
  lp1 lp2 =
    foldl (fun lp v -> add_monom (get_var_coeff lp1 v) v lp) lp2
      (ordered_keys (equal_nat, linorder_nat) lp1);;

let rec lhs (l, r) = l;;

let rec rhs (l, r) = r;;

let rec gelb _A
  lt c b = (match b with None -> true | Some ba -> lt ba c || eq _A ba c);;

let rec geub _A
  lt c b = (match b with None -> false | Some ba -> lt ba c || eq _A ba c);;

let rec gtlb lt c b = (match b with None -> true | Some ba -> lt ba c);;

let rec leub _A
  lt c b = (match b with None -> true | Some ba -> lt c ba || eq _A c ba);;

let rec ltlb lt c b = (match b with None -> false | Some a -> lt c a);;

let rec ltub lt c b = (match b with None -> true | Some a -> lt c a);;

let rec poly = function LEQ_ns (p, a) -> p
               | GEQ_ns (p, a) -> p;;

let rec fmmap f (Fmap_of_list m) = Fmap_of_list (map (apsnd f) m);;

let rec scale
  r lp = (if equal_rat r zero_rat then fmempty else fmmap (times_rat r) lp);;

let rec lvars t = Set (map lhs t);;

let rec linear_poly_map (LinearPoly x) = x;;

let rec scaleRat_linear_poly r p = LinearPoly (scale r (linear_poly_map p));;

let rec uminus_linear_poly lp = scaleRat_linear_poly (uminus_rat one_rat) lp;;

let rec plus_linear_poly
  p1 p2 = LinearPoly (add (linear_poly_map p1) (linear_poly_map p2));;

let rec minus_linear_poly
  lp1 lp2 = plus_linear_poly lp1 (uminus_linear_poly lp2);;

let rec constraint_to_qdelta_constraint
  = function LT (l, r) -> [LEQ_ns (l, QDelta (r, uminus_rat one_rat))]
    | GT (l, r) -> [GEQ_ns (l, QDelta (r, one_rat))]
    | LEQ (l, r) -> [LEQ_ns (l, QDelta (r, zero_rat))]
    | GEQ (l, r) -> [GEQ_ns (l, QDelta (r, zero_rat))]
    | EQ (l, r) ->
        [LEQ_ns (l, QDelta (r, zero_rat)); GEQ_ns (l, QDelta (r, zero_rat))]
    | LTPP (l1, l2) ->
        [LEQ_ns
           (minus_linear_poly l1 l2, QDelta (zero_rat, uminus_rat one_rat))]
    | GTPP (l1, l2) ->
        [GEQ_ns (minus_linear_poly l1 l2, QDelta (zero_rat, one_rat))]
    | LEQPP (l1, l2) -> [LEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa)]
    | GEQPP (l1, l2) -> [GEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa)]
    | EQPP (l1, l2) ->
        [LEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa);
          GEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa)];;

let rec to_ns l = maps constraint_to_qdelta_constraint l;;

let rec var x = LinearPoly (set_var_coeff x one_rat fmempty);;

let rec sum_list _A
  xs = foldr (plus _A.semigroup_add_monoid_add.plus_semigroup_add) xs
         (zero _A.zero_monoid_add);;

let rec vars_list
  lp = ordered_keys (equal_nat, linorder_nat) (linear_poly_map lp);;

let rec valuate _A
  lp vala =
    (let lpm = linear_poly_map lp in
      sum_list
        _A.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add
        (map (fun x ->
               scaleRat _A.scaleRat_rational_vector
                 (the (fmlookup equal_nat lpm x)) (vala x))
          (vars_list lp)));;

let rec delta_0_val
  x0 vl = match x0, vl with
    LEQ_ns (lll, rrr), vl -> delta_0 (valuate rational_vector_QDelta lll vl) rrr
    | GEQ_ns (lll, rrr), vl ->
        delta_0 rrr (valuate rational_vector_QDelta lll vl);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec delta_0_val_min
  x0 vl = match x0, vl with [], vl -> one_rat
    | h :: t, vl -> min ord_rat (delta_0_val_min t vl) (delta_0_val h vl);;

let rec map2fun _A
  v = (fun x ->
        (match lookupa linorder_nat v x with None -> zero _A | Some y -> y));;

let rec from_ns
  vl cs =
    (let delta = delta_0_val_min cs (map2fun zero_QDelta vl) in
      tabulate linorder_nat (remdups equal_nat (maps vars_list (map poly cs)))
        (fun var -> vala (map2fun zero_QDelta vl var) delta));;

let rec u_update
  ua (State_ext (t, b_l, b_u, v, u, more)) =
    State_ext (t, b_l, b_u, v, ua u, more);;

let rec uB_upd _A (Direction_ext (lt, lb, ub, uB_upd, le, more)) = uB_upd;;

let rec lt _A (Direction_ext (lt, lb, ub, uB_upd, le, more)) = lt;;

let rec ub _A (Direction_ext (lt, lb, ub, uB_upd, le, more)) = ub;;

let rec lb _A (Direction_ext (lt, lb, ub, uB_upd, le, more)) = lb;;

let rec v_update
  va (State_ext (t, b_l, b_u, v, u, more)) =
    State_ext (t, b_l, b_u, va v, u, more);;

let rec v (State_ext (t, b_l, b_u, v, u, more)) = v;;

let rec t (State_ext (t, b_l, b_u, v, u, more)) = t;;

let rec coeff lp = get_var_coeff (linear_poly_map lp);;

let rec rhs_eq_val (_A1, _A2, _A3, _A4)
  v x_i c e =
    (let x_j = lhs e in
     let a_i_j = coeff (rhs e) x_i in
      plus _A3 (map2fun _A4 v x_j)
        (scaleRat _A1 a_i_j (minus _A2 c (map2fun _A4 v x_i))));;

let rec update_code _A
  x c s =
    v_update
      (fun _ ->
        updatea linorder_nat x c
          (foldl
            (fun va e ->
              updatea linorder_nat (lhs e)
                (rhs_eq_val
                  (_A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.scaleRat_rational_vector,
                    _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.minus_group_add,
                    _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.semigroup_add_monoid_add.plus_semigroup_add,
                    _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add)
                  (v s) x c e)
                va)
            (v s) (t s)))
      s;;

let rec update_B _A
  field_update x c s = field_update (fun b -> fun_upd _A b x (Some c)) s;;

let rec assert_bound_codea (_A1, _A2)
  dir x c s =
    (if geub _A2
          (lt _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
            dir)
          c (ub _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
              dir s x)
      then s
      else (let sa =
              update_B equal_nat
                (uB_upd
                  _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                  dir)
                x c s
              in
             (if ltlb (lt _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                        dir)
                   c (lb _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                       dir s x)
               then u_update (fun _ -> true) sa
               else (if not (member equal_nat x (lvars (t sa))) &&
                          lt _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                            dir c
                            (map2fun
                              _A1.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                              (v s) x)
                      then update_code _A1 x c sa else sa))));;

let rec b_u_update
  b_ua (State_ext (t, b_l, b_u, v, u, more)) =
    State_ext (t, b_l, b_ua b_u, v, u, more);;

let rec b_u (State_ext (t, b_l, b_u, v, u, more)) = b_u;;

let rec b_l (State_ext (t, b_l, b_u, v, u, more)) = b_l;;

let rec positive _A
  = Direction_ext
      (less _A.order_linorder.preorder_order.ord_preorder, b_l, b_u, b_u_update,
        (fun a b -> Leq (a, b)), ());;

let rec b_l_update
  b_la (State_ext (t, b_l, b_u, v, u, more)) =
    State_ext (t, b_la b_l, b_u, v, u, more);;

let rec negative _A
  = Direction_ext
      ((fun x y -> less _A.order_linorder.preorder_order.ord_preorder y x), b_u,
        b_l, b_l_update, (fun a b -> Geq (a, b)), ());;

let rec assert_bound_code (_A1, _A2)
  x0 s = match x0, s with
    Leq (x, c), s ->
      assert_bound_codea (_A1, _A2)
        (positive
          _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
        x c s
    | Geq (x, c), s ->
        assert_bound_codea (_A1, _A2)
          (negative
            _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
          x c s;;

let rec u (State_ext (t, b_l, b_u, v, u, more)) = u;;

let rec assert_bound_loop_code (_A1, _A2)
  ats s =
    foldl (fun sa a -> (if u sa then sa else assert_bound_code (_A1, _A2) a sa))
      s ats;;

let rec init_state _A
  t = State_ext
        (t, (fun _ -> None), (fun _ -> None),
          tabulate linorder_nat
            (remdups equal_nat (map lhs t @ maps (comp vars_list rhs) t))
            (fun _ -> zero _A),
          false, ());;

let rec le_ubound (_A1, _A2)
  c b = leub _A1 (less _A2.order_linorder.preorder_order.ord_preorder) c b;;

let rec ge_lbound (_A1, _A2)
  c b = gelb _A1 (less _A2.order_linorder.preorder_order.ord_preorder) c b;;

let rec in_bounds (_B1, _B2)
  x v (lb, ub) =
    ge_lbound (_B1, _B2) (v x) (lb x) && le_ubound (_B1, _B2) (v x) (ub x);;

let rec min_satisfying _A
  p l = (let xs = filter p l in
          (if null xs then None
            else Some (foldl (min _A.order_linorder.preorder_order.ord_preorder)
                        (hd xs) (tl xs))));;

let rec min_lvar_not_in_bounds (_A1, _A2, _A3)
  s = min_satisfying linorder_nat
        (fun x ->
          not (in_bounds (_A2, _A3) x (map2fun _A1 (v s)) (b_l s, b_u s)))
        (map lhs (t s));;

let rec subst_var
  v lpa lp =
    minus_linear_poly
      (plus_linear_poly lp (scaleRat_linear_poly (coeff lp v) lpa))
      (scaleRat_linear_poly (coeff lp v) (var v));;

let rec subst_var_eq_code v lp eq = (lhs eq, subst_var v lp (rhs eq));;

let rec eq_idx_for_lvar_aux
  xa0 x i = match xa0, x, i with [], x, i -> i
    | eq :: t, x, i ->
        (if equal_nata (lhs eq) x then i
          else eq_idx_for_lvar_aux t x (plus_nat i one_nat));;

let rec eq_idx_for_lvar t x = eq_idx_for_lvar_aux t x zero_nat;;

let rec eq_for_lvar_code t v = nth t (eq_idx_for_lvar t v);;

let rec pivot_eq
  e y = (let cy = coeff (rhs e) y in
          (y, plus_linear_poly
                (scaleRat_linear_poly (divide_rat (uminus_rat one_rat) cy)
                  (minus_linear_poly (rhs e) (scaleRat_linear_poly cy (var y))))
                (scaleRat_linear_poly (divide_rat one_rat cy) (var (lhs e)))));;

let rec pivot_tableau_code
  x_i x_j t =
    (let eq = eq_for_lvar_code t x_i in
     let eqa = pivot_eq eq x_j in
      map (fun e ->
            (if equal_nata (lhs e) (lhs eq) then eqa
              else subst_var_eq_code x_j (rhs eqa) e))
        t);;

let rec t_update
  ta (State_ext (t, b_l, b_u, v, u, more)) =
    State_ext (ta t, b_l, b_u, v, u, more);;

let rec pivot_code _A
  x_i x_j s = t_update (fun _ -> pivot_tableau_code x_i x_j (t s)) s;;

let rec pivot_and_update_code _A
  x_i x_j c s = update_code _A x_i c (pivot_code _A x_i x_j s);;

let rec min_rvar_incdec_eq _A
  dir s eq =
    min_satisfying linorder_nat
      (fun x ->
        less_rat zero_rat (coeff (rhs eq) x) &&
          ltub (lt _A.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                 dir)
            (map2fun
              _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
              (v s) x)
            (ub _A.linordered_rational_vector_lrv.linorder_linordered_rational_vector
              dir s x) ||
          less_rat (coeff (rhs eq) x) zero_rat &&
            gtlb (lt _A.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                   dir)
              (map2fun
                _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                (v s) x)
              (lb _A.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                dir s x))
      (vars_list (rhs eq));;

let rec check_codea _A
  dir x_i s =
    (let l_i =
       the (lb _A.linordered_rational_vector_lrv.linorder_linordered_rational_vector
             dir s x_i)
       in
      (match min_rvar_incdec_eq _A dir s (eq_for_lvar_code (t s) x_i)
        with None -> u_update (fun _ -> true) s
        | Some x_j -> pivot_and_update_code _A x_i x_j l_i s));;

let rec lt_lbound _A
  c b = ltlb (less _A.order_linorder.preorder_order.ord_preorder) c b;;

let rec check_code (_A1, _A2)
  s = (if u s then s
        else (match
               min_lvar_not_in_bounds
                 (_A1.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add,
                   _A2,
                   _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
                 s
               with None -> s
               | Some x_i ->
                 (let dir =
                    (if lt_lbound
                          _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                          (map2fun
                            _A1.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                            (v s) x_i)
                          (b_l s x_i)
                      then positive
                             _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                      else negative
                             _A1.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
                    in
                   check_code (_A1, _A2) (check_codea _A1 dir x_i s))));;

let rec assert_all_state_code (_A1, _A2)
  t ats =
    check_code (_A1, _A2)
      (assert_bound_loop_code (_A1, _A2) ats
        (init_state
          _A1.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
          t));;

let rec assert_all_code (_A1, _A2)
  t asa =
    (let s = assert_all_state_code (_A1, _A2) t asa in
      (if u s then (false, None) else (true, Some (v s))));;

let rec max_var
  lp = (let vl = vars_list lp in
         (if null vl then zero_nat else foldl (max ord_nat) (hd vl) (tl vl)));;

let rec start_fresh_variable
  = function [] -> zero_nat
    | h :: t ->
        max ord_nat (plus_nat (max_var (poly h)) one_nat)
          (start_fresh_variable t);;

let rec tableau
  (Istate_ext (firstFreshVariable, tableau, atoms, more)) = tableau;;

let rec atoms (Istate_ext (firstFreshVariable, tableau, atoms, more)) = atoms;;

let rec sgn_int
  i = (if equal_inta i zero_int then zero_int
        else (if less_int zero_int i then one_int else uminus_int one_int));;

let rec abs_int i = (if less_int i zero_int then uminus_int i else i);;

let rec inverse_rat
  p = Frct (let a = quotient_of p in
            let (aa, b) = a in
             (if equal_inta aa zero_int then (zero_int, one_int)
               else (times_int (sgn_int aa) b, abs_int aa)));;

let rec monom_var l = max_var l;;

let rec monom_coeff l = coeff l (monom_var l);;

let rec monom_to_atom
  = function
    LEQ_ns (l, r) ->
      (if less_rat (monom_coeff l) zero_rat
        then Geq (monom_var l, scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r)
        else Leq (monom_var l,
                   scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r))
    | GEQ_ns (l, r) ->
        (if less_rat (monom_coeff l) zero_rat
          then Leq (monom_var l,
                     scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r)
          else Geq (monom_var l,
                     scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r));;

let rec is_monom l = equal_nata (size_list (vars_list l)) one_nat;;

let rec qdelta_constraint_to_atom
  x0 v = match x0, v with
    LEQ_ns (l, r), v ->
      (if is_monom l then monom_to_atom (LEQ_ns (l, r)) else Leq (v, r))
    | GEQ_ns (l, r), v ->
        (if is_monom l then monom_to_atom (GEQ_ns (l, r)) else Geq (v, r));;

let rec firstFreshVariable
  (Istate_ext (firstFreshVariable, tableau, atoms, more)) = firstFreshVariable;;

let rec qdelta_constraint_to_eq
  x0 v = match x0, v with LEQ_ns (l, r), v -> (v, l)
    | GEQ_ns (l, r), v -> (v, l);;

let rec preprocessa
  x0 v = match x0, v with [], v -> Istate_ext (v, [], [], ())
    | h :: t, v ->
        (let s = preprocessa t v in
         let va = firstFreshVariable s in
         let ta = tableau s in
         let a = atoms s in
          Istate_ext
            ((if is_monom (poly h) then va else plus_nat va one_nat),
              (if is_monom (poly h) then ta
                else qdelta_constraint_to_eq h va :: ta),
              qdelta_constraint_to_atom h va :: a, ()));;

let rec preprocess
  l = (let start = start_fresh_variable l in
       let is = preprocessa l start in
        (tableau is, atoms is));;

let rec solve_exec_ns_code
  s = (let a = preprocess s in
       let (aa, b) = a in
        assert_all_code (lrv_QDelta, equal_QDelta) aa b);;

let rec solve_exec_code
  cs = (let csa = to_ns cs in
         (match solve_exec_ns_code csa
           with (true, v) -> (true, Some (from_ns (the v) csa))
           | (false, _) -> (false, None)));;

let rec simplex cs = snd (solve_exec_code cs);;

let rec lp_monom
  c x = LinearPoly
          (if equal_rat c zero_rat then fmempty
            else fmupd equal_nat x c fmempty);;

let rec rat_of_int_pair
  n d = divide_rat (of_int (Int_of_integer n)) (of_int (Int_of_integer d));;

end;; (*struct Simplex*)
