module Simplex_Validity_Checker : sig
  type int = Int_of_integer of Big_int.big_int
  type nat
  val nat_of_integer : Big_int.big_int -> nat
  type char
  type rat
  type ('a, 'b) term = Var of 'b | Fun of 'a * ('a, 'b) term list
  type ty = BoolT | IntT
  type 'a set
  type siga = LessF | LeF | SumF of nat | ConstF of int | ProdF of nat | EqF
  type tya = BoolTa | RatT
  type sigb = LessFa | LeFa | SumFa of nat | ConstFa of rat | ProdFa of nat |
    EqFa
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  type 'a formulaa = FAtom of 'a | FNegate of 'a formulaa |
    FConjunction of 'a formulaa list | FDisjunction of 'a formulaa list
  val explode : string -> char list
  val create_rat : Big_int.big_int -> Big_int.big_int -> rat
  val check_valid_IA_formula_string_vars :
    (siga, (char list * ty)) term formulaa -> (string, unit) sum
  val check_valid_RA_formula_string_vars :
    (sigb, (char list * tya)) term formulaa -> (string, unit) sum
  val check_valid_IA_formula_integer_vars :
    (siga, (Big_int.big_int * ty)) term formulaa -> (string, unit) sum
  val check_valid_RA_formula_integer_vars :
    (sigb, (Big_int.big_int * tya)) term formulaa -> (string, unit) sum
  val check_well_formed_IA_formula_string_vars :
    (siga, (char list * ty)) term formulaa -> bool
  val check_well_formed_RA_formula_string_vars :
    (sigb, (char list * tya)) term formulaa -> bool
  val check_well_formed_IA_formula_integer_vars :
    (siga, (Big_int.big_int * ty)) term formulaa -> bool
  val check_well_formed_RA_formula_integer_vars :
    (sigb, (Big_int.big_int * tya)) term formulaa -> bool
end = struct

type int = Int_of_integer of Big_int.big_int;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec equal_inta
  k l = Big_int.eq_big_int (integer_of_int k) (integer_of_int l);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

let rec times_inta
  k l = Int_of_integer
          (Big_int.mult_big_int (integer_of_int k) (integer_of_int l));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_int = ({times = times_inta} : int times);;

let dvd_int = ({times_dvd = times_int} : int dvd);;

type num = One | Bit0 of num | Bit1 of num;;

let one_inta : int = Int_of_integer (Big_int.big_int_of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec uminus_inta
  k = Int_of_integer (Big_int.minus_big_int (integer_of_int k));;

let rec minus_inta
  k l = Int_of_integer
          (Big_int.sub_big_int (integer_of_int k) (integer_of_int l));;

let zero_inta : int = Int_of_integer Big_int.zero_big_int;;

let rec plus_inta
  k l = Int_of_integer
          (Big_int.add_big_int (integer_of_int k) (integer_of_int l));;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a zero = {zeroa : 'a};;
let zeroa _A = _A.zeroa;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

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

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add;
    semiring_0_cancel_ring : 'a semiring_0_cancel};;

let plus_int = ({plus = plus_inta} : int plus);;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    int cancel_semigroup_add);;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let minus_int = ({minus = minus_inta} : int minus);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : int cancel_ab_semigroup_add);;

let zero_int = ({zeroa = zero_inta} : int zero);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : int cancel_comm_monoid_add);;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : int mult_zero);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : int semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : int semiring);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : int semiring_0);;

let semiring_0_cancel_int =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int;
     semiring_0_semiring_0_cancel = semiring_0_int}
    : int semiring_0_cancel);;

let uminus_int = ({uminus = uminus_inta} : int uminus);;

let group_add_int =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_int;
     minus_group_add = minus_int; monoid_add_group_add = monoid_add_int;
     uminus_group_add = uminus_int}
    : int group_add);;

let ab_group_add_int =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int;
     group_add_ab_group_add = group_add_int}
    : int ab_group_add);;

let ring_int =
  ({ab_group_add_ring = ab_group_add_int;
     semiring_0_cancel_ring = semiring_0_cancel_int}
    : int ring);;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add; numeral_neg_numeral : 'a numeral};;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral; ring_ring_1 : 'a ring;
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : int monoid_mult);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : int semiring_numeral);;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : int semiring_1);;

let semiring_1_cancel_int =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int;
     semiring_1_semiring_1_cancel = semiring_1_int}
    : int semiring_1_cancel);;

let neg_numeral_int =
  ({group_add_neg_numeral = group_add_int; numeral_neg_numeral = numeral_int} :
    int neg_numeral);;

let ring_1_int =
  ({neg_numeral_ring_1 = neg_numeral_int; ring_ring_1 = ring_int;
     semiring_1_cancel_ring_1 = semiring_1_cancel_int}
    : int ring_1);;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

let ab_semigroup_mult_int =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
    int ab_semigroup_mult);;

let comm_semiring_int =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int;
     semiring_comm_semiring = semiring_int}
    : int comm_semiring);;

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

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

type nat = Nat of Big_int.big_int;;

let rec integer_of_nat (Nat x) = x;;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let ord_integer =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

let rec nat_of_integer k = Nat (max ord_integer Big_int.zero_big_int k);;

let rec bit_cut_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int
        then (Big_int.zero_big_int, false)
        else (let (r, s) =
                Big_int.quomod_big_int (Big_int.abs_big_int k)
                  (Big_int.abs_big_int (Big_int.big_int_of_int 2))
                in
               ((if Big_int.lt_big_int Big_int.zero_big_int k then r
                  else Big_int.sub_big_int (Big_int.minus_big_int r) s),
                 Big_int.eq_big_int s (Big_int.big_int_of_int 1))));;

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

let rec char_of_integer
  k = (let (q0, b0) = bit_cut_integer k in
       let (q1, b1) = bit_cut_integer q0 in
       let (q2, b2) = bit_cut_integer q1 in
       let (q3, b3) = bit_cut_integer q2 in
       let (q4, b4) = bit_cut_integer q3 in
       let (q5, b5) = bit_cut_integer q4 in
       let (q6, b6) = bit_cut_integer q5 in
       let a = bit_cut_integer q6 in
       let (_, aa) = a in
        Chara (b0, b1, b2, b3, b4, b5, b6, aa));;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zeroa _A.zero_zero_neq_one;;

let one_integera : Big_int.big_int = (Big_int.big_int_of_int 1);;

let zero_integer = ({zeroa = Big_int.zero_big_int} : Big_int.big_int zero);;

let one_integer = ({one = one_integera} : Big_int.big_int one);;

let zero_neq_one_integer =
  ({one_zero_neq_one = one_integer; zero_zero_neq_one = zero_integer} :
    Big_int.big_int zero_neq_one);;

let rec integer_of_char
  (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
    Big_int.add_big_int
      (Big_int.mult_big_int
        (Big_int.add_big_int
          (Big_int.mult_big_int
            (Big_int.add_big_int
              (Big_int.mult_big_int
                (Big_int.add_big_int
                  (Big_int.mult_big_int
                    (Big_int.add_big_int
                      (Big_int.mult_big_int
                        (Big_int.add_big_int
                          (Big_int.mult_big_int
                            (Big_int.add_big_int
                              (Big_int.mult_big_int
                                (of_bool zero_neq_one_integer b7)
                                (Big_int.big_int_of_int 2))
                              (of_bool zero_neq_one_integer b6))
                            (Big_int.big_int_of_int 2))
                          (of_bool zero_neq_one_integer b5))
                        (Big_int.big_int_of_int 2))
                      (of_bool zero_neq_one_integer b4))
                    (Big_int.big_int_of_int 2))
                  (of_bool zero_neq_one_integer b3))
                (Big_int.big_int_of_int 2))
              (of_bool zero_neq_one_integer b2))
            (Big_int.big_int_of_int 2))
          (of_bool zero_neq_one_integer b1))
        (Big_int.big_int_of_int 2))
      (of_bool zero_neq_one_integer b0);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec implode
  cs = (let ks = (map integer_of_char
                   cs) in let res = Bytes.create (List.length ks) in let rec imp i = function | [] -> res | k :: ks ->
      let l = Big_int.int_of_big_int k in if 0 <= l && l < 128 then Bytes.set res i (Char.chr l) else failwith "Non-ASCII character in literal"; imp (i + 1) ks in imp 0 ks);;

let rec lit_of_digit
  n = implode
        [char_of_integer
           (Big_int.add_big_int (Big_int.big_int_of_int 48)
             (integer_of_nat n))];;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

let rec showsl_lit x = (fun a -> x ^ a);;

let rec showsl_nat
  n = (if less_nat n (nat_of_integer (Big_int.big_int_of_int 10))
        then showsl_lit (lit_of_digit n)
        else comp (showsl_nat
                    (divide_nat n (nat_of_integer (Big_int.big_int_of_int 10))))
               (showsl_lit
                 (lit_of_digit
                   (modulo_nat n
                     (nat_of_integer (Big_int.big_int_of_int 10))))));;

let rec less_int
  k l = Big_int.lt_big_int (integer_of_int k) (integer_of_int l);;

let rec nat k = Nat (max ord_integer Big_int.zero_big_int (integer_of_int k));;

let rec showsl_int
  i = (if less_int i zero_inta
        then comp (showsl_lit "-") (showsl_nat (nat (uminus_inta i)))
        else showsl_nat (nat i));;

let rec showsl_sep
  s sep x2 = match s, sep, x2 with s, sep, [] -> showsl_lit ""
    | s, sep, [x] -> s x
    | s, sep, x :: v :: va ->
        comp (comp (s x) sep) (showsl_sep s sep (v :: va));;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec showsl_list_gen
  showslx e l s r xs =
    (if null xs then showsl_lit e
      else comp (comp (showsl_lit l) (showsl_sep showslx (showsl_lit s) xs))
             (showsl_lit r));;

let rec default_showsl_list sl = showsl_list_gen sl "[]" "[" ", " "]";;

let rec showsl_list_int xs = default_showsl_list showsl_int xs;;

type 'a showl =
  {showsl : 'a -> string -> string; showsl_list : 'a list -> string -> string};;
let showsl _A = _A.showsl;;
let showsl_list _A = _A.showsl_list;;

let showl_int =
  ({showsl = showsl_int; showsl_list = showsl_list_int} : int showl);;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

let comm_semiring_0_int =
  ({comm_semiring_comm_semiring_0 = comm_semiring_int;
     semiring_0_comm_semiring_0 = semiring_0_int}
    : int comm_semiring_0);;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

let comm_monoid_mult_int =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int;
     monoid_mult_comm_monoid_mult = monoid_mult_int;
     dvd_comm_monoid_mult = dvd_int}
    : int comm_monoid_mult);;

let comm_semiring_1_int =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_int;
     semiring_1_comm_semiring_1 = semiring_1_int}
    : int comm_semiring_1);;

let rec equal_nata
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat
  m n = Big_int.le_big_int (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type ordera = Eq | Lt | Gt;;

let rec eq _A a b = equal _A a b;;

type 'a quasi_order = {ord_quasi_order : 'a ord};;

type 'a weak_order = {quasi_order_weak_order : 'a quasi_order};;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order =
  {preorder_order : 'a preorder; weak_order_order : 'a weak_order};;

type 'a linorder = {order_linorder : 'a order};;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eq else Gt));;

let quasi_order_nat = ({ord_quasi_order = ord_nat} : nat quasi_order);;

let weak_order_nat =
  ({quasi_order_weak_order = quasi_order_nat} : nat weak_order);;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat =
  ({preorder_order = preorder_nat; weak_order_order = weak_order_nat} :
    nat order);;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let rec compare_nata x = comparator_of (equal_nat, linorder_nat) x;;

type 'a compare = {compare : 'a -> 'a -> ordera};;
let compare _A = _A.compare;;

let compare_nat = ({compare = compare_nata} : nat compare);;

type 'a compare_order =
  {compare_compare_order : 'a compare; linorder_compare_order : 'a linorder};;

let compare_order_nat =
  ({compare_compare_order = compare_nat; linorder_compare_order = linorder_nat}
    : nat compare_order);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

type rat = Frct of (int * int);;

let rec quotient_of (Frct x) = x;;

let rec equal_rata
  a b = equal_proda equal_int equal_int (quotient_of a) (quotient_of b);;

let equal_rat = ({equal = equal_rata} : rat equal);;

let rec divide_int
  k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));;

let rec gcd_int
  (Int_of_integer x) (Int_of_integer y) =
    Int_of_integer (Big_int.gcd_big_int x y);;

let rec normalize
  p = (if less_int zero_inta (snd p)
        then (let a = gcd_int (fst p) (snd p) in
               (divide_int (fst p) a, divide_int (snd p) a))
        else (if equal_inta (snd p) zero_inta then (zero_inta, one_inta)
               else (let a = uminus_inta (gcd_int (fst p) (snd p)) in
                      (divide_int (fst p) a, divide_int (snd p) a))));;

let rec times_rata
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize (times_inta aa ba, times_inta c d));;

let times_rat = ({times = times_rata} : rat times);;

let dvd_rat = ({times_dvd = times_rat} : rat dvd);;

let one_rata : rat = Frct (one_inta, one_inta);;

let one_rat = ({one = one_rata} : rat one);;

let rec uminus_rata p = Frct (let a = quotient_of p in
                              let (aa, b) = a in
                               (uminus_inta aa, b));;

let rec minus_rata
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize
                 (minus_inta (times_inta aa d) (times_inta ba c),
                   times_inta c d));;

let zero_rata : rat = Frct (zero_inta, one_inta);;

let rec plus_rata
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize
                 (plus_inta (times_inta aa d) (times_inta ba c),
                   times_inta c d));;

let plus_rat = ({plus = plus_rata} : rat plus);;

let semigroup_add_rat = ({plus_semigroup_add = plus_rat} : rat semigroup_add);;

let cancel_semigroup_add_rat =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_rat} :
    rat cancel_semigroup_add);;

let ab_semigroup_add_rat =
  ({semigroup_add_ab_semigroup_add = semigroup_add_rat} :
    rat ab_semigroup_add);;

let minus_rat = ({minus = minus_rata} : rat minus);;

let cancel_ab_semigroup_add_rat =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_rat;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_rat;
     minus_cancel_ab_semigroup_add = minus_rat}
    : rat cancel_ab_semigroup_add);;

let zero_rat = ({zeroa = zero_rata} : rat zero);;

let monoid_add_rat =
  ({semigroup_add_monoid_add = semigroup_add_rat; zero_monoid_add = zero_rat} :
    rat monoid_add);;

let comm_monoid_add_rat =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_rat;
     monoid_add_comm_monoid_add = monoid_add_rat}
    : rat comm_monoid_add);;

let cancel_comm_monoid_add_rat =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_rat;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_rat}
    : rat cancel_comm_monoid_add);;

let mult_zero_rat =
  ({times_mult_zero = times_rat; zero_mult_zero = zero_rat} : rat mult_zero);;

let semigroup_mult_rat =
  ({times_semigroup_mult = times_rat} : rat semigroup_mult);;

let semiring_rat =
  ({ab_semigroup_add_semiring = ab_semigroup_add_rat;
     semigroup_mult_semiring = semigroup_mult_rat}
    : rat semiring);;

let semiring_0_rat =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_rat;
     mult_zero_semiring_0 = mult_zero_rat; semiring_semiring_0 = semiring_rat}
    : rat semiring_0);;

let semiring_0_cancel_rat =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_rat;
     semiring_0_semiring_0_cancel = semiring_0_rat}
    : rat semiring_0_cancel);;

let uminus_rat = ({uminus = uminus_rata} : rat uminus);;

let group_add_rat =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_rat;
     minus_group_add = minus_rat; monoid_add_group_add = monoid_add_rat;
     uminus_group_add = uminus_rat}
    : rat group_add);;

let ab_group_add_rat =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_rat;
     group_add_ab_group_add = group_add_rat}
    : rat ab_group_add);;

let ring_rat =
  ({ab_group_add_ring = ab_group_add_rat;
     semiring_0_cancel_ring = semiring_0_cancel_rat}
    : rat ring);;

let numeral_rat =
  ({one_numeral = one_rat; semigroup_add_numeral = semigroup_add_rat} :
    rat numeral);;

let power_rat = ({one_power = one_rat; times_power = times_rat} : rat power);;

let monoid_mult_rat =
  ({semigroup_mult_monoid_mult = semigroup_mult_rat;
     power_monoid_mult = power_rat}
    : rat monoid_mult);;

let semiring_numeral_rat =
  ({monoid_mult_semiring_numeral = monoid_mult_rat;
     numeral_semiring_numeral = numeral_rat;
     semiring_semiring_numeral = semiring_rat}
    : rat semiring_numeral);;

let zero_neq_one_rat =
  ({one_zero_neq_one = one_rat; zero_zero_neq_one = zero_rat} :
    rat zero_neq_one);;

let semiring_1_rat =
  ({semiring_numeral_semiring_1 = semiring_numeral_rat;
     semiring_0_semiring_1 = semiring_0_rat;
     zero_neq_one_semiring_1 = zero_neq_one_rat}
    : rat semiring_1);;

let semiring_1_cancel_rat =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_rat;
     semiring_1_semiring_1_cancel = semiring_1_rat}
    : rat semiring_1_cancel);;

let neg_numeral_rat =
  ({group_add_neg_numeral = group_add_rat; numeral_neg_numeral = numeral_rat} :
    rat neg_numeral);;

let ring_1_rat =
  ({neg_numeral_ring_1 = neg_numeral_rat; ring_ring_1 = ring_rat;
     semiring_1_cancel_ring_1 = semiring_1_cancel_rat}
    : rat ring_1);;

let rec less_eq_int
  k l = Big_int.le_big_int (integer_of_int k) (integer_of_int l);;

let rec less_eq_rat
  p q = (let a = quotient_of p in
         let (aa, c) = a in
         let b = quotient_of q in
         let (ba, d) = b in
          less_eq_int (times_inta aa d) (times_inta c ba));;

let rec less_rat
  p q = (let a = quotient_of p in
         let (aa, c) = a in
         let b = quotient_of q in
         let (ba, d) = b in
          less_int (times_inta aa d) (times_inta c ba));;

let ord_rat = ({less_eq = less_eq_rat; less = less_rat} : rat ord);;

let ab_semigroup_mult_rat =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_rat} :
    rat ab_semigroup_mult);;

let comm_semiring_rat =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_rat;
     semiring_comm_semiring = semiring_rat}
    : rat comm_semiring);;

let rec showsl_rat
  x = (let (d, n) = quotient_of x in
        (if equal_inta n one_inta then showsl_int d
          else comp (comp (showsl_int d) (showsl_lit "/")) (showsl_int n)));;

let rec showsl_list_rat xs = default_showsl_list showsl_rat xs;;

let showl_rat =
  ({showsl = showsl_rat; showsl_list = showsl_list_rat} : rat showl);;

let comm_semiring_0_rat =
  ({comm_semiring_comm_semiring_0 = comm_semiring_rat;
     semiring_0_comm_semiring_0 = semiring_0_rat}
    : rat comm_semiring_0);;

let comm_monoid_mult_rat =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_rat;
     monoid_mult_comm_monoid_mult = monoid_mult_rat;
     dvd_comm_monoid_mult = dvd_rat}
    : rat comm_monoid_mult);;

let comm_semiring_1_rat =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_rat;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_rat;
     semiring_1_comm_semiring_1 = semiring_1_rat}
    : rat comm_semiring_1);;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec less_eq_list (_A1, _A2)
  x0 xs = match x0, xs with
    x :: xs, y :: ys ->
      less _A2.preorder_order.ord_preorder x y ||
        eq _A1 x y && less_eq_list (_A1, _A2) xs ys
    | [], xs -> true
    | x :: xs, [] -> false;;

let rec less_list (_A1, _A2)
  xs x1 = match xs, x1 with
    x :: xs, y :: ys ->
      less _A2.preorder_order.ord_preorder x y ||
        eq _A1 x y && less_list (_A1, _A2) xs ys
    | [], x :: xs -> true
    | xs, [] -> false;;

let rec ord_list (_A1, _A2) =
  ({less_eq = less_eq_list (_A1, _A2); less = less_list (_A1, _A2)} :
    ('a list) ord);;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with
    comp_a, x :: xa, y :: ya ->
      (match comp_a x y with Eq -> comparator_list comp_a xa ya | Lt -> Lt
        | Gt -> Gt)
    | comp_a, x :: xa, [] -> Gt
    | comp_a, [], y :: ya -> Lt
    | comp_a, [], [] -> Eq;;

let rec compare_lista _A = comparator_list (compare _A);;

let rec compare_list _A = ({compare = compare_lista _A} : ('a list) compare);;

let rec quasi_order_list (_A1, _A2) =
  ({ord_quasi_order = (ord_list (_A1, _A2))} : ('a list) quasi_order);;

let rec weak_order_list (_A1, _A2) =
  ({quasi_order_weak_order = (quasi_order_list (_A1, _A2))} :
    ('a list) weak_order);;

let rec preorder_list (_A1, _A2) =
  ({ord_preorder = (ord_list (_A1, _A2))} : ('a list) preorder);;

let rec order_list (_A1, _A2) =
  ({preorder_order = (preorder_list (_A1, _A2));
     weak_order_order = (weak_order_list (_A1, _A2))}
    : ('a list) order);;

let rec linorder_list (_A1, _A2) =
  ({order_linorder = (order_list (_A1, _A2.order_linorder))} :
    ('a list) linorder);;

let rec showsl_lista _A xs = showsl_list _A xs;;

let rec showsl_list_list _A xs = default_showsl_list (showsl_lista _A) xs;;

let rec showl_list _A =
  ({showsl = showsl_lista _A; showsl_list = showsl_list_list _A} :
    ('a list) showl);;

let rec compare_order_list (_A1, _A2) =
  ({compare_compare_order = (compare_list _A1.compare_compare_order);
     linorder_compare_order = (linorder_list (_A2, _A1.linorder_compare_order))}
    : ('a list) compare_order);;

type ('a, 'b) term = Var of 'b | Fun of 'a * ('a, 'b) term list;;

let rec equal_term _A _B = ({equal = equal_terma _A _B} : ('a, 'b) term equal)
and equal_terma _A _B
  x0 x1 = match x0, x1 with Var x1, Fun (x21, x22) -> false
    | Fun (x21, x22), Var x1 -> false
    | Fun (x21, x22), Fun (y21, y22) ->
        eq _A x21 y21 && equal_lista (equal_term _A _B) x22 y22
    | Var x1, Var y1 -> eq _B x1 y1;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec equal_chara
  (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
    (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
    equal_bool x1 y1 &&
      (equal_bool x2 y2 &&
        (equal_bool x3 y3 &&
          (equal_bool x4 y4 &&
            (equal_bool x5 y5 &&
              (equal_bool x6 y6 && (equal_bool x7 y7 && equal_bool x8 y8))))));;

let equal_char = ({equal = equal_chara} : char equal);;

let rec nat_of_char c = Nat (integer_of_char c);;

let rec less_eq_char c1 c2 = less_eq_nat (nat_of_char c1) (nat_of_char c2);;

let rec less_char c1 c2 = less_nat (nat_of_char c1) (nat_of_char c2);;

let ord_char = ({less_eq = less_eq_char; less = less_char} : char ord);;

let quasi_order_char = ({ord_quasi_order = ord_char} : char quasi_order);;

let weak_order_char =
  ({quasi_order_weak_order = quasi_order_char} : char weak_order);;

let preorder_char = ({ord_preorder = ord_char} : char preorder);;

let order_char =
  ({preorder_order = preorder_char; weak_order_order = weak_order_char} :
    char order);;

let linorder_char = ({order_linorder = order_char} : char linorder);;

let rec compare_chara x = comparator_of (equal_char, linorder_char) x;;

let compare_char = ({compare = compare_chara} : char compare);;

let rec showsl_list_char cs s = showsl_lit (implode cs) s;;

let rec showsl_char c = showsl_lit (implode [c]);;

let showl_char =
  ({showsl = showsl_char; showsl_list = showsl_list_char} : char showl);;

let compare_order_char =
  ({compare_compare_order = compare_char;
     linorder_compare_order = linorder_char}
    : char compare_order);;

type qDelta = QDelta of rat * rat;;

let rec equal_QDeltaa
  (QDelta (x1, x2)) (QDelta (y1, y2)) = equal_rata x1 y1 && equal_rata x2 y2;;

let equal_QDelta = ({equal = equal_QDeltaa} : qDelta equal);;

let one_QDeltaa : qDelta = QDelta (one_rata, zero_rata);;

let one_QDelta = ({one = one_QDeltaa} : qDelta one);;

let rec qdsnd (QDelta (a, b)) = b;;

let rec qdfst (QDelta (a, b)) = a;;

let rec plus_QDeltaa
  qd1 qd2 =
    QDelta
      (plus_rata (qdfst qd1) (qdfst qd2), plus_rata (qdsnd qd1) (qdsnd qd2));;

let plus_QDelta = ({plus = plus_QDeltaa} : qDelta plus);;

let zero_QDeltaa : qDelta = QDelta (zero_rata, zero_rata);;

let zero_QDelta = ({zeroa = zero_QDeltaa} : qDelta zero);;

let rec minus_QDeltaa
  qd1 qd2 =
    QDelta
      (minus_rata (qdfst qd1) (qdfst qd2), minus_rata (qdsnd qd1) (qdsnd qd2));;

let minus_QDelta = ({minus = minus_QDeltaa} : qDelta minus);;

let rec uminus_QDeltaa
  qd = QDelta (uminus_rata (qdfst qd), uminus_rata (qdsnd qd));;

let uminus_QDelta = ({uminus = uminus_QDeltaa} : qDelta uminus);;

let rec less_eq_QDelta
  qd1 qd2 =
    less_rat (qdfst qd1) (qdfst qd2) ||
      equal_rata (qdfst qd1) (qdfst qd2) &&
        less_eq_rat (qdsnd qd1) (qdsnd qd2);;

let rec less_QDelta
  qd1 qd2 =
    less_rat (qdfst qd1) (qdfst qd2) ||
      equal_rata (qdfst qd1) (qdfst qd2) && less_rat (qdsnd qd1) (qdsnd qd2);;

let ord_QDelta = ({less_eq = less_eq_QDelta; less = less_QDelta} : qDelta ord);;

let quasi_order_QDelta = ({ord_quasi_order = ord_QDelta} : qDelta quasi_order);;

let weak_order_QDelta =
  ({quasi_order_weak_order = quasi_order_QDelta} : qDelta weak_order);;

let preorder_QDelta = ({ord_preorder = ord_QDelta} : qDelta preorder);;

let order_QDelta =
  ({preorder_order = preorder_QDelta; weak_order_order = weak_order_QDelta} :
    qDelta order);;

let semigroup_add_QDelta =
  ({plus_semigroup_add = plus_QDelta} : qDelta semigroup_add);;

let cancel_semigroup_add_QDelta =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_QDelta} :
    qDelta cancel_semigroup_add);;

let monoid_add_QDelta =
  ({semigroup_add_monoid_add = semigroup_add_QDelta;
     zero_monoid_add = zero_QDelta}
    : qDelta monoid_add);;

let group_add_QDelta =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_QDelta;
     minus_group_add = minus_QDelta; monoid_add_group_add = monoid_add_QDelta;
     uminus_group_add = uminus_QDelta}
    : qDelta group_add);;

let linorder_QDelta = ({order_linorder = order_QDelta} : qDelta linorder);;

let ab_semigroup_add_QDelta =
  ({semigroup_add_ab_semigroup_add = semigroup_add_QDelta} :
    qDelta ab_semigroup_add);;

let cancel_ab_semigroup_add_QDelta =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_QDelta;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_QDelta;
     minus_cancel_ab_semigroup_add = minus_QDelta}
    : qDelta cancel_ab_semigroup_add);;

let comm_monoid_add_QDelta =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_QDelta;
     monoid_add_comm_monoid_add = monoid_add_QDelta}
    : qDelta comm_monoid_add);;

let cancel_comm_monoid_add_QDelta =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_QDelta;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_QDelta}
    : qDelta cancel_comm_monoid_add);;

let ab_group_add_QDelta =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_QDelta;
     group_add_ab_group_add = group_add_QDelta}
    : qDelta ab_group_add);;

let rec scaleRat_QDeltaa
  r qd = QDelta (times_rata r (qdfst qd), times_rata r (qdsnd qd));;

type 'a scaleRat = {scaleRat : rat -> 'a -> 'a};;
let scaleRat _A = _A.scaleRat;;

type 'a rational_vector =
  {ab_group_add_rational_vector : 'a ab_group_add;
    scaleRat_rational_vector : 'a scaleRat};;

type 'a ordered_rational_vector =
  {order_ordered_rational_vector : 'a order;
    rational_vector_ordered_rational_vector : 'a rational_vector};;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add;
    order_ordered_ab_semigroup_add : 'a order};;

type 'a linordered_rational_vector =
  {ordered_ab_semigroup_add_linordered_rational_vector :
     'a ordered_ab_semigroup_add;
    linorder_linordered_rational_vector : 'a linorder;
    ordered_rational_vector_linordered_rational_vector :
      'a ordered_rational_vector};;

type 'a lrv =
  {one_lrv : 'a one;
    linordered_rational_vector_lrv : 'a linordered_rational_vector};;

let scaleRat_QDelta = ({scaleRat = scaleRat_QDeltaa} : qDelta scaleRat);;

let rational_vector_QDelta =
  ({ab_group_add_rational_vector = ab_group_add_QDelta;
     scaleRat_rational_vector = scaleRat_QDelta}
    : qDelta rational_vector);;

let ordered_rational_vector_QDelta =
  ({order_ordered_rational_vector = order_QDelta;
     rational_vector_ordered_rational_vector = rational_vector_QDelta}
    : qDelta ordered_rational_vector);;

let ordered_ab_semigroup_add_QDelta =
  ({ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_QDelta;
     order_ordered_ab_semigroup_add = order_QDelta}
    : qDelta ordered_ab_semigroup_add);;

let linordered_rational_vector_QDelta =
  ({ordered_ab_semigroup_add_linordered_rational_vector =
      ordered_ab_semigroup_add_QDelta;
     linorder_linordered_rational_vector = linorder_QDelta;
     ordered_rational_vector_linordered_rational_vector =
       ordered_rational_vector_QDelta}
    : qDelta linordered_rational_vector);;

let lrv_QDelta =
  ({one_lrv = one_QDelta;
     linordered_rational_vector_lrv = linordered_rational_vector_QDelta}
    : qDelta lrv);;

type hints = Hints of int list | Simplex;;

let default_hintsa : hints = Simplex;;

type 'a default = {default : 'a};;
let default _A = _A.default;;

let default_hints = ({default = default_hintsa} : hints default);;

let rec showsl_hints
  = function
    Hints xs -> comp (showsl_lit "Linear-Combination: ") (showsl_list_int xs)
    | Simplex -> showsl_lit "Simplex";;

let rec showsl_list_hints xs = default_showsl_list showsl_hints xs;;

let showl_hints =
  ({showsl = showsl_hints; showsl_list = showsl_list_hints} : hints showl);;

type 'a monom = Abs_monom of ('a * nat) list;;

let rec rep_monom _A (Abs_monom x) = x;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec equal_monoma (_A1, _A2)
  xa xc =
    equal_lista (equal_prod _A1 equal_nat) (rep_monom _A2 xa)
      (rep_monom _A2 xc);;

let rec equal_monom (_A1, _A2) =
  ({equal = equal_monoma (_A1, _A2)} : 'a monom equal);;

let default_unita : unit = ();;

let default_unit = ({default = default_unita} : unit default);;

let rec showsl_unit x = showsl_lit "()";;

let rec showsl_list_unit xs = default_showsl_list showsl_unit xs;;

let showl_unit =
  ({showsl = showsl_unit; showsl_list = showsl_list_unit} : unit showl);;

let equal_integer = ({equal = Big_int.eq_big_int} : Big_int.big_int equal);;

let quasi_order_integer =
  ({ord_quasi_order = ord_integer} : Big_int.big_int quasi_order);;

let weak_order_integer =
  ({quasi_order_weak_order = quasi_order_integer} :
    Big_int.big_int weak_order);;

let preorder_integer =
  ({ord_preorder = ord_integer} : Big_int.big_int preorder);;

let order_integer =
  ({preorder_order = preorder_integer; weak_order_order = weak_order_integer} :
    Big_int.big_int order);;

let linorder_integer =
  ({order_linorder = order_integer} : Big_int.big_int linorder);;

let rec compare_integera x = comparator_of (equal_integer, linorder_integer) x;;

let compare_integer = ({compare = compare_integera} : Big_int.big_int compare);;

let rec showsl_list_integer
  x = comp showsl_list_int (map (fun a -> Int_of_integer a)) x;;

let rec showsl_integer x = comp showsl_int (fun a -> Int_of_integer a) x;;

let showl_integer =
  ({showsl = showsl_integer; showsl_list = showsl_list_integer} :
    Big_int.big_int showl);;

let compare_order_integer =
  ({compare_compare_order = compare_integer;
     linorder_compare_order = linorder_integer}
    : Big_int.big_int compare_order);;

type ty = BoolT | IntT;;

let rec equal_tyb x0 x1 = match x0, x1 with BoolT, IntT -> false
                    | IntT, BoolT -> false
                    | IntT, IntT -> true
                    | BoolT, BoolT -> true;;

let equal_ty = ({equal = equal_tyb} : ty equal);;

let rec rel_option r x1 x2 = match r, x1, x2 with r, None, Some y2 -> false
                     | r, Some y2, None -> false
                     | r, None, None -> true
                     | r, Some x2, Some y2 -> r x2 y2;;

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec fmlookup _A (Fmap_of_list m) = map_of _A m;;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a fset = Abs_fset of 'a set;;

let rec fset_of_list xa = Abs_fset (Set xa);;

let rec fset (Abs_fset x) = x;;

let rec image f (Set xs) = Set (map f xs);;

let rec fimage xb xc = Abs_fset (image xb (fset xc));;

let rec fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec ball (Set xs) p = list_all p xs;;

let rec fBall xa = ball (fset xa);;

let rec fmrel _C
  r m n =
    fBall (fmdom m)
      (fun x -> rel_option r (fmlookup _C m x) (fmlookup _C n x)) &&
      fBall (fmdom n)
        (fun x -> rel_option r (fmlookup _C m x) (fmlookup _C n x));;

let rec equal_fmap _A _B = fmrel _A (equal _B);;

type linear_poly = LinearPoly of (nat, rat) fmap;;

let rec linear_poly_map (LinearPoly x) = x;;

let rec equal_linear_polya
  x y = equal_fmap equal_nat equal_rat (linear_poly_map x) (linear_poly_map y);;

let equal_linear_poly = ({equal = equal_linear_polya} : linear_poly equal);;

type siga = LessF | LeF | SumF of nat | ConstF of int | ProdF of nat | EqF;;

let rec equal_sigb x0 x1 = match x0, x1 with ProdF x5, EqF -> false
                     | EqF, ProdF x5 -> false
                     | ConstF x4, EqF -> false
                     | EqF, ConstF x4 -> false
                     | ConstF x4, ProdF x5 -> false
                     | ProdF x5, ConstF x4 -> false
                     | SumF x3, EqF -> false
                     | EqF, SumF x3 -> false
                     | SumF x3, ProdF x5 -> false
                     | ProdF x5, SumF x3 -> false
                     | SumF x3, ConstF x4 -> false
                     | ConstF x4, SumF x3 -> false
                     | LeF, EqF -> false
                     | EqF, LeF -> false
                     | LeF, ProdF x5 -> false
                     | ProdF x5, LeF -> false
                     | LeF, ConstF x4 -> false
                     | ConstF x4, LeF -> false
                     | LeF, SumF x3 -> false
                     | SumF x3, LeF -> false
                     | LessF, EqF -> false
                     | EqF, LessF -> false
                     | LessF, ProdF x5 -> false
                     | ProdF x5, LessF -> false
                     | LessF, ConstF x4 -> false
                     | ConstF x4, LessF -> false
                     | LessF, SumF x3 -> false
                     | SumF x3, LessF -> false
                     | LessF, LeF -> false
                     | LeF, LessF -> false
                     | ProdF x5, ProdF y5 -> equal_nata x5 y5
                     | ConstF x4, ConstF y4 -> equal_inta x4 y4
                     | SumF x3, SumF y3 -> equal_nata x3 y3
                     | EqF, EqF -> true
                     | LeF, LeF -> true
                     | LessF, LessF -> true;;

let equal_sig = ({equal = equal_sigb} : siga equal);;

type tya = BoolTa | RatT;;

let rec equal_tyc x0 x1 = match x0, x1 with BoolTa, RatT -> false
                    | RatT, BoolTa -> false
                    | RatT, RatT -> true
                    | BoolTa, BoolTa -> true;;

let equal_tya = ({equal = equal_tyc} : tya equal);;

type sigb = LessFa | LeFa | SumFa of nat | ConstFa of rat | ProdFa of nat |
  EqFa;;

let rec equal_sigc x0 x1 = match x0, x1 with ProdFa x5, EqFa -> false
                     | EqFa, ProdFa x5 -> false
                     | ConstFa x4, EqFa -> false
                     | EqFa, ConstFa x4 -> false
                     | ConstFa x4, ProdFa x5 -> false
                     | ProdFa x5, ConstFa x4 -> false
                     | SumFa x3, EqFa -> false
                     | EqFa, SumFa x3 -> false
                     | SumFa x3, ProdFa x5 -> false
                     | ProdFa x5, SumFa x3 -> false
                     | SumFa x3, ConstFa x4 -> false
                     | ConstFa x4, SumFa x3 -> false
                     | LeFa, EqFa -> false
                     | EqFa, LeFa -> false
                     | LeFa, ProdFa x5 -> false
                     | ProdFa x5, LeFa -> false
                     | LeFa, ConstFa x4 -> false
                     | ConstFa x4, LeFa -> false
                     | LeFa, SumFa x3 -> false
                     | SumFa x3, LeFa -> false
                     | LessFa, EqFa -> false
                     | EqFa, LessFa -> false
                     | LessFa, ProdFa x5 -> false
                     | ProdFa x5, LessFa -> false
                     | LessFa, ConstFa x4 -> false
                     | ConstFa x4, LessFa -> false
                     | LessFa, SumFa x3 -> false
                     | SumFa x3, LessFa -> false
                     | LessFa, LeFa -> false
                     | LeFa, LessFa -> false
                     | ProdFa x5, ProdFa y5 -> equal_nata x5 y5
                     | ConstFa x4, ConstFa y4 -> equal_rata x4 y4
                     | SumFa x3, SumFa y3 -> equal_nata x3 y3
                     | EqFa, EqFa -> true
                     | LeFa, LeFa -> true
                     | LessFa, LessFa -> true;;

let equal_siga = ({equal = equal_sigc} : sigb equal);;

type color = R | B;;

type ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;;

type ('b, 'a) rbt = RBT of ('b, 'a) rbta;;

type 'a hint = Default | Base of 'a | Distribute of nat * 'a hint list |
  Erase of nat * 'a hint | LexStrict of 'a hint list | LexWeak of 'a hint list;;

type 'a atom = Leq of nat * 'a | Geq of nat * 'a;;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

type ('a, 'b) mapping = Mapping of ('a, 'b) rbt;;

type ('a, 'b) state =
  State of
    (nat * linear_poly) list * (nat, ('a * 'b)) mapping *
      (nat, ('a * 'b)) mapping * (nat, 'b) mapping * bool * ('a list) option;;

type 'a istate =
  IState of
    nat * (nat * linear_poly) list * ('a * qDelta atom) list *
      (linear_poly -> nat option);;

type 'a formula = Atom of 'a | NegAtom of 'a | Conjunction of 'a formula list |
  Disjunction of 'a formula list;;

type ('a, 'b) tpoly = PVar of 'a | PNum of 'b | PSum of ('a, 'b) tpoly list |
  PMult of ('a, 'b) tpoly list;;

type ('a, 'b) direction =
  Direction of
    ('b -> 'b -> bool) * (('a, 'b) state -> (nat, ('a * 'b)) mapping) *
      (('a, 'b) state -> (nat, ('a * 'b)) mapping) *
      (('a, 'b) state -> nat -> 'b option) *
      (('a, 'b) state -> nat -> 'b option) * (('a, 'b) state -> nat -> 'a) *
      (('a, 'b) state -> nat -> 'a) *
      (((nat, ('a * 'b)) mapping -> (nat, ('a * 'b)) mapping) ->
        ('a, 'b) state -> ('a, 'b) state) *
      (nat -> 'b -> 'b atom) * (nat -> 'b -> 'b atom);;

type constrainta = LT of linear_poly * rat | GT of linear_poly * rat |
  LEQ of linear_poly * rat | GEQ of linear_poly * rat | EQ of linear_poly * rat
  | LTPP of linear_poly * linear_poly | GTPP of linear_poly * linear_poly |
  LEQPP of linear_poly * linear_poly | GEQPP of linear_poly * linear_poly |
  EQPP of linear_poly * linear_poly;;

type 'a linearity = Non_Linear | Onea | Variable of 'a;;

type 'a linearitya = Non_Lineara | Oneb | Variablea of 'a;;

type 'a ns_constraint = LEQ_ns of linear_poly * 'a |
  GEQ_ns of linear_poly * 'a;;

type 'a formulaa = FAtom of 'a | FNegate of 'a formulaa |
  FConjunction of 'a formulaa list | FDisjunction of 'a formulaa list;;

type 'a poly_constraint = Poly_Ge of ('a monom * int) list |
  Poly_Eq of ('a monom * int) list;;

type 'a poly_constrainta = Poly_Gea of ('a monom * rat) list |
  Poly_Eqa of ('a monom * rat) list | Poly_Gt of ('a monom * rat) list;;

let rec id x = (fun xa -> xa) x;;

let rec plus_nat
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Big_int.big_int_of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec bex (Set xs) p = list_ex p xs;;

let rec minus_nat
  m n = Nat (max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

let zero_nat : nat = Nat Big_int.zero_big_int;;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nat then x :: xs
          else drop (minus_nat n one_nat) xs);;

let rec find uu x1 = match uu, x1 with uu, [] -> None
               | p, x :: xs -> (if p x then Some x else find p xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nat then []
          else x :: take (minus_nat n one_nat) xs);;

let rec empty _A = RBT Empty;;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec vala qd delta = plus_rata (qdfst qd) (times_rata delta (qdsnd qd));;

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
    f, k, v, Branch (R, l, x, y, r) ->
      (match compare _A.compare_compare_order k x
        with Eq -> Branch (R, l, x, f k y v, r)
        | Lt -> Branch (R, rbt_ins _A f k v l, x, y, r)
        | Gt -> Branch (R, l, x, y, rbt_ins _A f k v r))
    | f, k, v, Branch (B, l, x, y, r) ->
        (match compare _A.compare_compare_order k x
          with Eq -> Branch (B, l, x, f k y v, r)
          | Lt -> balance (rbt_ins _A f k v l) x y r
          | Gt -> balance l x y (rbt_ins _A f k v r))
    | f, k, v, Empty -> Branch (R, Empty, k, v, Empty);;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_insert_with_key _A f k v t = paint B (rbt_ins _A f k v t);;

let rec rbt_insert _A = rbt_insert_with_key _A (fun _ _ nv -> nv);;

let rec impl_of _B (RBT x) = x;;

let rec insert _A
  xc xd xe = RBT (rbt_insert _A xc xd (impl_of _A.linorder_compare_order xe));;

let rec rbt_lookup _A
  x0 k = match x0, k with
    Branch (uu, l, x, y, r), k ->
      (match compare _A.compare_compare_order k x with Eq -> Some y
        | Lt -> rbt_lookup _A l k | Gt -> rbt_lookup _A r k)
    | Empty, k -> None;;

let rec lookup _A x = rbt_lookup _A (impl_of _A.linorder_compare_order x);;

let rec of_int a = Frct (a, one_inta);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec insertb _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec inserta _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (insertb _A x xs);;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let rec merge _A qs ps = foldr (fun (a, b) -> update _A a b) ps qs;;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec bind x0 f = match x0, f with None, f -> None
               | Some x, f -> f x;;

let rec lhs (l, r) = l;;

let rec rhs (l, r) = r;;

let rec extract
  p x1 = match p, x1 with
    p, x :: xs ->
      (if p x then Some ([], (x, xs))
        else (match extract p xs with None -> None
               | Some (ys, (y, zs)) -> Some (x :: ys, (y, zs))))
    | p, [] -> None;;

let rec hd (x21 :: x22) = x21;;

let rec tl = function [] -> []
             | x21 :: x22 -> x22;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec rbt_bulkload _A xs = foldr (fun (a, b) -> rbt_insert _A a b) xs Empty;;

let rec bulkload _A xa = RBT (rbt_bulkload _A xa);;

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

let rec emptya _A = Mapping (empty _A);;

let rec lvars t = Set (map lhs t);;

let rec fmmap f (Fmap_of_list m) = Fmap_of_list (map (apsnd f) m);;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec scale
  r lp = (if equal_rata r zero_rata then fmempty else fmmap (times_rata r) lp);;

let rec scaleRat_linear_poly r p = LinearPoly (scale r (linear_poly_map p));;

let rec uminus_linear_poly lp = scaleRat_linear_poly (uminus_rata one_rata) lp;;

let rec get_var_coeff
  lp v = (match fmlookup equal_nat lp v with None -> zero_rata | Some c -> c);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

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

let rec fmfilter
  p (Fmap_of_list m) = Fmap_of_list (filter (fun (k, _) -> p k) m);;

let rec fmdrop _A a = fmfilter (fun aa -> not (eq _A aa a));;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge _A m n);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let rec set_var_coeff
  v c lp =
    (if equal_rata c zero_rata then fmdrop equal_nat v lp
      else fmupd equal_nat v c lp);;

let rec add_monom
  c v lp = set_var_coeff v (plus_rata c (get_var_coeff lp v)) lp;;

let rec add
  lp1 lp2 =
    foldl (fun lp v -> add_monom (get_var_coeff lp1 v) v lp) lp2
      (ordered_keys (equal_nat, linorder_nat) lp1);;

let rec plus_linear_poly
  p1 p2 = LinearPoly (add (linear_poly_map p1) (linear_poly_map p2));;

let rec minus_linear_poly
  lp1 lp2 = plus_linear_poly lp1 (uminus_linear_poly lp2);;

let rec constraint_to_qdelta_constraint
  = function LT (l, r) -> [LEQ_ns (l, QDelta (r, uminus_rata one_rata))]
    | GT (l, r) -> [GEQ_ns (l, QDelta (r, one_rata))]
    | LEQ (l, r) -> [LEQ_ns (l, QDelta (r, zero_rata))]
    | GEQ (l, r) -> [GEQ_ns (l, QDelta (r, zero_rata))]
    | EQ (l, r) ->
        [LEQ_ns (l, QDelta (r, zero_rata)); GEQ_ns (l, QDelta (r, zero_rata))]
    | LTPP (l1, l2) ->
        [LEQ_ns
           (minus_linear_poly l1 l2, QDelta (zero_rata, uminus_rata one_rata))]
    | GTPP (l1, l2) ->
        [GEQ_ns (minus_linear_poly l1 l2, QDelta (zero_rata, one_rata))]
    | LEQPP (l1, l2) -> [LEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa)]
    | GEQPP (l1, l2) -> [GEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa)]
    | EQPP (l1, l2) ->
        [LEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa);
          GEQ_ns (minus_linear_poly l1 l2, zero_QDeltaa)];;

let rec i_constraint_to_qdelta_constraint
  (i, c) = map (fun a -> (i, a)) (constraint_to_qdelta_constraint c);;

let rec to_ns l = maps i_constraint_to_qdelta_constraint l;;

let rec partition
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, x :: xs ->
        (let (yes, no) = partition p xs in
          (if p x then (x :: yes, no) else (yes, x :: no)));;

let rec replicate
  n x = (if equal_nata n zero_nat then []
          else x :: replicate (minus_nat n one_nat) x);;

let rec lookupa _A (Mapping t) = lookup _A t;;

let rec updatea _A k v (Mapping t) = Mapping (insert _A k v t);;

let rec b_i_l (State (x1, x2, x3, x4, x5, x6)) = x2;;

let rec the (Some x2) = x2;;

let rec indexl s = comp (comp fst the) (lookupa compare_order_nat (b_i_l s));;

let rec b_i_u (State (x1, x2, x3, x4, x5, x6)) = x3;;

let rec indexu s = comp (comp fst the) (lookupa compare_order_nat (b_i_u s));;

let rec form_or
  x0 psi = match x0, psi with Disjunction [], psi -> psi
    | Atom v, Disjunction [] -> Atom v
    | NegAtom v, Disjunction [] -> NegAtom v
    | Conjunction v, Disjunction [] -> Conjunction v
    | Disjunction (va :: vb), Disjunction [] -> Disjunction (va :: vb)
    | Disjunction (v :: va), Disjunction (vb :: vc) ->
        Disjunction ((v :: va) @ vb :: vc)
    | Disjunction (v :: va), Atom vb -> Disjunction ((v :: va) @ [Atom vb])
    | Disjunction (v :: va), NegAtom vb ->
        Disjunction ((v :: va) @ [NegAtom vb])
    | Disjunction (v :: va), Conjunction vb ->
        Disjunction ((v :: va) @ [Conjunction vb])
    | Atom v, Disjunction (va :: vb) -> Disjunction (Atom v :: va :: vb)
    | NegAtom v, Disjunction (va :: vb) -> Disjunction (NegAtom v :: va :: vb)
    | Conjunction v, Disjunction (va :: vb) ->
        Disjunction (Conjunction v :: va :: vb)
    | Atom v, Atom va -> Disjunction [Atom v; Atom va]
    | Atom v, NegAtom va -> Disjunction [Atom v; NegAtom va]
    | Atom v, Conjunction va -> Disjunction [Atom v; Conjunction va]
    | NegAtom v, Atom va -> Disjunction [NegAtom v; Atom va]
    | NegAtom v, NegAtom va -> Disjunction [NegAtom v; NegAtom va]
    | NegAtom v, Conjunction va -> Disjunction [NegAtom v; Conjunction va]
    | Conjunction v, Atom va -> Disjunction [Conjunction v; Atom va]
    | Conjunction v, NegAtom va -> Disjunction [Conjunction v; NegAtom va]
    | Conjunction v, Conjunction va ->
        Disjunction [Conjunction v; Conjunction va];;

let rec cnf_form_or
  phi psi = match phi, psi with
    Conjunction phi_s, Conjunction psi_s ->
      Conjunction (maps (fun phi -> map (form_or phi) psi_s) phi_s)
    | Atom v, psi -> form_or (Atom v) psi
    | NegAtom v, psi -> form_or (NegAtom v) psi
    | Disjunction v, psi -> form_or (Disjunction v) psi
    | phi, Atom v -> form_or phi (Atom v)
    | phi, NegAtom v -> form_or phi (NegAtom v)
    | phi, Disjunction v -> form_or phi (Disjunction v);;

let rec form_cnf_ex = function [] -> Conjunction [Disjunction []]
                      | phi :: phi_s -> cnf_form_or phi (form_cnf_ex phi_s);;

let rec form_and
  x0 psi = match x0, psi with Conjunction [], psi -> psi
    | Atom v, Conjunction [] -> Atom v
    | NegAtom v, Conjunction [] -> NegAtom v
    | Conjunction (va :: vb), Conjunction [] -> Conjunction (va :: vb)
    | Disjunction v, Conjunction [] -> Disjunction v
    | Conjunction (v :: va), Conjunction (vb :: vc) ->
        Conjunction ((v :: va) @ vb :: vc)
    | Conjunction (v :: va), Atom vb -> Conjunction ((v :: va) @ [Atom vb])
    | Conjunction (v :: va), NegAtom vb ->
        Conjunction ((v :: va) @ [NegAtom vb])
    | Conjunction (v :: va), Disjunction vb ->
        Conjunction ((v :: va) @ [Disjunction vb])
    | Atom v, Conjunction (va :: vb) -> Conjunction (Atom v :: va :: vb)
    | NegAtom v, Conjunction (va :: vb) -> Conjunction (NegAtom v :: va :: vb)
    | Disjunction v, Conjunction (va :: vb) ->
        Conjunction (Disjunction v :: va :: vb)
    | Atom v, Atom va -> Conjunction [Atom v; Atom va]
    | Atom v, NegAtom va -> Conjunction [Atom v; NegAtom va]
    | Atom v, Disjunction va -> Conjunction [Atom v; Disjunction va]
    | NegAtom v, Atom va -> Conjunction [NegAtom v; Atom va]
    | NegAtom v, NegAtom va -> Conjunction [NegAtom v; NegAtom va]
    | NegAtom v, Disjunction va -> Conjunction [NegAtom v; Disjunction va]
    | Disjunction v, Atom va -> Conjunction [Disjunction v; Atom va]
    | Disjunction v, NegAtom va -> Conjunction [Disjunction v; NegAtom va]
    | Disjunction v, Disjunction va ->
        Conjunction [Disjunction v; Disjunction va];;

let rec form_all = function [] -> Conjunction []
                   | phi :: phi_s -> form_and phi (form_all phi_s);;

let rec flatten = function Conjunction phi_s -> form_all (map flatten phi_s)
                  | Disjunction phi_s -> form_cnf_ex (map flatten phi_s)
                  | Atom v -> Conjunction [Disjunction [Atom v]]
                  | NegAtom v -> Conjunction [Disjunction [NegAtom v]];;

let rec form_ex = function [] -> Disjunction []
                  | phi :: phi_s -> form_or phi (form_ex phi_s);;

let rec is_Atom = function Atom uu -> true
                  | NegAtom v -> false
                  | Conjunction v -> false
                  | Disjunction v -> false;;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec boundsl
  s = comp (map_option snd) (lookupa compare_order_nat (b_i_l s));;

let rec boundsu
  s = comp (map_option snd) (lookupa compare_order_nat (b_i_u s));;

let rec vars_list
  lp = ordered_keys (equal_nat, linorder_nat) (linear_poly_map lp);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec sum_list _A
  xs = foldr (plus _A.semigroup_add_monoid_add.plus_semigroup_add) xs
         (zeroa _A.zero_monoid_add);;

let rec valuate _A
  lp vala =
    (let lpm = linear_poly_map lp in
      sum_list
        _A.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add
        (map (fun x ->
               scaleRat _A.scaleRat_rational_vector
                 (the (fmlookup equal_nat lpm x)) (vala x))
          (vars_list lp)));;

let rec divide_rat
  p q = Frct (let a = quotient_of p in
              let (aa, c) = a in
              let b = quotient_of q in
              let (ba, d) = b in
               normalize (times_inta aa d, times_inta c ba));;

let rec delta_0
  qd1 qd2 =
    (let c1 = qdfst qd1 in
     let c2 = qdfst qd2 in
     let k1 = qdsnd qd1 in
     let k2 = qdsnd qd2 in
      (if less_rat c1 c2 && less_rat k2 k1
        then divide_rat (minus_rata c2 c1) (minus_rata k1 k2) else one_rata));;

let rec delta_0_val
  x0 vl = match x0, vl with
    LEQ_ns (lll, rrr), vl -> delta_0 (valuate rational_vector_QDelta lll vl) rrr
    | GEQ_ns (lll, rrr), vl ->
        delta_0 rrr (valuate rational_vector_QDelta lll vl);;

let rec delta_0_val_min
  x0 vl = match x0, vl with [], vl -> one_rata
    | h :: t, vl -> min ord_rat (delta_0_val_min t vl) (delta_0_val h vl);;

let rec tabulate _A ks f = Mapping (bulkload _A (map (fun k -> (k, f k)) ks));;

let rec map2fun _A
  v = (fun x ->
        (match lookupa compare_order_nat v x with None -> zeroa _A
          | Some y -> y));;

let rec from_ns
  vl cs =
    (let delta = delta_0_val_min cs (map2fun zero_QDelta vl) in
      tabulate compare_order_nat
        (remdups equal_nat (maps vars_list (map poly cs)))
        (fun var -> vala (map2fun zero_QDelta vl var) delta));;

let rec uBI_upd _B (Direction (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) = x8;;

let rec update_B_I _A
  field_update i x c s = field_update (updatea _A x (i, c)) s;;

let rec lt _B (Direction (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) = x1;;

let rec ub _B (Direction (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) = x5;;

let rec li _B (Direction (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) = x6;;

let rec lb _B (Direction (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) = x4;;

let rec v_update
  v (State (t, bil, biu, v_old, u, uc)) = State (t, bil, biu, v, u, uc);;

let rec v (State (x1, x2, x3, x4, x5, x6)) = x4;;

let rec t (State (x1, x2, x3, x4, x5, x6)) = x1;;

let rec coeff lp = get_var_coeff (linear_poly_map lp);;

let rec rhs_eq_val (_A1, _A2, _A3, _A4)
  v x_i c e =
    (let x_j = lhs e in
     let a_i_j = coeff (rhs e) x_i in
      plus _A2 (map2fun _A3 v x_j)
        (scaleRat _A4 a_i_j (minus _A1 c (map2fun _A3 v x_i))));;

let rec update_code _A
  x c s =
    v_update
      (updatea compare_order_nat x c
        (foldl
          (fun va e ->
            updatea compare_order_nat (lhs e)
              (rhs_eq_val
                (_A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.minus_group_add,
                  _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.semigroup_add_monoid_add.plus_semigroup_add,
                  _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add,
                  _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.scaleRat_rational_vector)
                (v s) x c e)
              va)
          (v s) (t s)))
      s;;

let rec set_unsat _A
  i (State (t, bil, biu, v, u, uc)) =
    State (t, bil, biu, v, true, Some (remdups _A i));;

let rec assert_bound_codea _A (_B1, _B2)
  dir i x c s =
    (if geub _B1
          (lt _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
            dir)
          c (ub _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
              dir s x)
      then s
      else (let sa =
              update_B_I compare_order_nat
                (uBI_upd
                  _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                  dir)
                i x c s
              in
             (if ltlb (lt _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                        dir)
                   c (lb _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                       dir s x)
               then set_unsat _A
                      [i; li _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                            dir s x]
                      sa
               else (if not (member equal_nat x (lvars (t sa))) &&
                          lt _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                            dir c
                            (map2fun
                              _B2.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                              (v s) x)
                      then update_code _B2 x c sa else sa))));;

let rec b_i_u_update
  up (State (t, bil, biu, v, u, uc)) = State (t, bil, up biu, v, u, uc);;

let rec positive _B
  = Direction
      (less _B.order_linorder.preorder_order.ord_preorder, b_i_l, b_i_u,
        boundsl, boundsu, indexl, indexu, b_i_u_update, (fun a b -> Leq (a, b)),
        (fun a b -> Geq (a, b)));;

let rec b_i_l_update
  up (State (t, bil, biu, v, u, uc)) = State (t, up bil, biu, v, u, uc);;

let rec negative _B
  = Direction
      ((fun x y -> less _B.order_linorder.preorder_order.ord_preorder y x),
        b_i_u, b_i_l, boundsu, boundsl, indexu, indexl, b_i_l_update,
        (fun a b -> Geq (a, b)), (fun a b -> Leq (a, b)));;

let rec assert_bound_code _A (_B1, _B2)
  x0 s = match x0, s with
    (i, Leq (x, c)), s ->
      assert_bound_codea _A (_B1, _B2)
        (positive
          _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
        i x c s
    | (i, Geq (x, c)), s ->
        assert_bound_codea _A (_B1, _B2)
          (negative
            _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
          i x c s;;

let rec u (State (x1, x2, x3, x4, x5, x6)) = x5;;

let rec assert_bound_loop_code _A (_B1, _B2)
  ats s =
    foldl (fun sa a ->
            (if u sa then sa else assert_bound_code _A (_B1, _B2) a sa))
      s ats;;

let rec init_state _B
  t = State (t, emptya linorder_nat, emptya linorder_nat,
              tabulate compare_order_nat
                (remdups equal_nat (map lhs t @ maps (comp vars_list rhs) t))
                (fun _ -> zeroa _B),
              false, None);;

let rec min_satisfying _A
  p l = (let xs = filter p l in
          (if null xs then None
            else Some (foldl (min _A.order_linorder.preorder_order.ord_preorder)
                        (hd xs) (tl xs))));;

let rec le_ubound (_A1, _A2)
  c b = leub _A1 (less _A2.order_linorder.preorder_order.ord_preorder) c b;;

let rec ge_lbound (_A1, _A2)
  c b = gelb _A1 (less _A2.order_linorder.preorder_order.ord_preorder) c b;;

let rec in_bounds (_B1, _B2)
  x v (lb, ub) =
    ge_lbound (_B1, _B2) (v x) (lb x) && le_ubound (_B1, _B2) (v x) (ub x);;

let rec min_lvar_not_in_bounds (_B1, _B2, _B3)
  s = min_satisfying linorder_nat
        (fun x ->
          not (in_bounds (_B2, _B3) x (map2fun _B1 (v s))
                (boundsl s, boundsu s)))
        (map lhs (t s));;

let rec var x = LinearPoly (set_var_coeff x one_rata fmempty);;

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
                (scaleRat_linear_poly (divide_rat (uminus_rata one_rata) cy)
                  (minus_linear_poly (rhs e) (scaleRat_linear_poly cy (var y))))
                (scaleRat_linear_poly (divide_rat one_rata cy)
                  (var (lhs e)))));;

let rec pivot_tableau_code
  x_i x_j t =
    (let eq = eq_for_lvar_code t x_i in
     let eqa = pivot_eq eq x_j in
      map (fun e ->
            (if equal_nata (lhs e) (lhs eq) then eqa
              else subst_var_eq_code x_j (rhs eqa) e))
        t);;

let rec t_update
  t (State (t_old, bil, biu, v, u, uc)) = State (t, bil, biu, v, u, uc);;

let rec pivot_code _B
  x_i x_j s = t_update (pivot_tableau_code x_i x_j (t s)) s;;

let rec pivot_and_update_code _A
  x_i x_j c s = update_code _A x_i c (pivot_code _A x_i x_j s);;

let rec ui _B (Direction (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) = x7;;

let rec unsat_indices _A _B
  dir s vs eq =
    (let r = rhs eq in
     let lia = li _B dir s in
     let uia = ui _B dir s in
      remdups _A
        (lia (lhs eq) ::
          map (fun x ->
                (if less_rat (coeff r x) zero_rata then lia x else uia x))
            vs));;

let rec min_rvar_incdec_eq _A _B
  dir s eq =
    (let rvars = vars_list (rhs eq) in
      (match
        min_satisfying linorder_nat
          (fun x ->
            less_rat zero_rata (coeff (rhs eq) x) &&
              ltub (lt _B.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                     dir)
                (map2fun
                  _B.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                  (v s) x)
                (ub _B.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                  dir s x) ||
              less_rat (coeff (rhs eq) x) zero_rata &&
                gtlb (lt _B.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                       dir)
                  (map2fun
                    _B.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                    (v s) x)
                  (lb _B.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                    dir s x))
          rvars
        with None ->
          Inl (unsat_indices _A
                _B.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                dir s rvars eq)
        | Some a -> Inr a));;

let rec check_codea _A _B
  dir x_i s =
    (let l_i =
       the (lb _B.linordered_rational_vector_lrv.linorder_linordered_rational_vector
             dir s x_i)
       in
      (match min_rvar_incdec_eq _A _B dir s (eq_for_lvar_code (t s) x_i)
        with Inl i -> set_unsat _A i s
        | Inr x_j -> pivot_and_update_code _B x_i x_j l_i s));;

let rec lt_lbound _A
  c b = ltlb (less _A.order_linorder.preorder_order.ord_preorder) c b;;

let rec check_code _A (_B1, _B2)
  s = (if u s then s
        else (match
               min_lvar_not_in_bounds
                 (_B2.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add,
                   _B1,
                   _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
                 s
               with None -> s
               | Some x_i ->
                 (let dir =
                    (if lt_lbound
                          _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                          (map2fun
                            _B2.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                            (v s) x_i)
                          (boundsl s x_i)
                      then positive
                             _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector
                      else negative
                             _B2.linordered_rational_vector_lrv.linorder_linordered_rational_vector)
                    in
                   check_code _A (_B1, _B2) (check_codea _A _B2 dir x_i s))));;

let rec assert_all_state_code _A (_B1, _B2)
  t ats =
    check_code _A (_B1, _B2)
      (assert_bound_loop_code _A (_B1, _B2) ats
        (init_state
          _B2.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
          t));;

let rec u_c (State (x1, x2, x3, x4, x5, x6)) = x6;;

let rec assert_all_code _A (_B1, _B2)
  t asa =
    (let s = assert_all_state_code _A (_B1, _B2) t asa in
      (if u s then Inl (the (u_c s)) else Inr (v s)));;

let rec pivot_tableau_eq
  t1 eq t2 x =
    (let eqa = pivot_eq eq x in
     let m = map (subst_var_eq_code x (rhs eqa)) in
      (m t1, (eqa, m t2)));;

let rec preprocess_opt _A
  x t1 xa2 = match x, t1, xa2 with x, t1, [] -> (t1, id)
    | xa, t1, (x, p) :: t2 ->
        (if not (member equal_nat x xa)
          then (let (t, tv) = preprocess_opt _A xa t1 t2 in
                 (t, comp (fun v ->
                            updatea compare_order_nat x
                              (valuate
                                _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector
                                p (map2fun
                                    _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
                                    v))
                              v)
                       tv))
          else (match
                 find (fun xb -> not (member equal_nat xb xa)) (vars_list p)
                 with None -> preprocess_opt _A xa ((x, p) :: t1) t2
                 | Some y ->
                   (let (tt1, ((z, q), tt2)) = pivot_tableau_eq t1 (x, p) t2 y
                      in
                    let (t, tv) = preprocess_opt _A xa tt1 tt2 in
                     (t, comp (fun v ->
                                updatea compare_order_nat z
                                  (valuate
                                    _A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector
                                    q (map2fun
_A.linordered_rational_vector_lrv.ordered_rational_vector_linordered_rational_vector.rational_vector_ordered_rational_vector.ab_group_add_rational_vector.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add
v))
                                  v)
                           tv))));;

let rec atom_var = function Leq (var, a) -> var
                   | Geq (var, a) -> var;;

let rec preprocess_part_2 _C
  asa t = preprocess_opt _C (image atom_var (image snd (Set asa))) [] t;;

let rec max_var
  lp = (let vl = vars_list lp in
         (if null vl then zero_nat else foldl (max ord_nat) (hd vl) (tl vl)));;

let rec start_fresh_variable
  = function [] -> zero_nat
    | (i, h) :: t ->
        max ord_nat (plus_nat (max_var (poly h)) one_nat)
          (start_fresh_variable t);;

let rec tableau (IState (x1, x2, x3, x4)) = x2;;

let rec atoms (IState (x1, x2, x3, x4)) = x3;;

let rec is_monom l = equal_nata (size_list (vars_list l)) one_nat;;

let rec sgn_int
  i = (if equal_inta i zero_inta then zero_inta
        else (if less_int zero_inta i then one_inta
               else uminus_inta one_inta));;

let rec abs_int i = (if less_int i zero_inta then uminus_inta i else i);;

let rec inverse_rat
  p = Frct (let a = quotient_of p in
            let (aa, b) = a in
             (if equal_inta aa zero_inta then (zero_inta, one_inta)
               else (times_inta (sgn_int aa) b, abs_int aa)));;

let rec monom_var l = max_var l;;

let rec monom_coeff l = coeff l (monom_var l);;

let rec monom_to_atom
  = function
    LEQ_ns (l, r) ->
      (if less_rat (monom_coeff l) zero_rata
        then Geq (monom_var l, scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r)
        else Leq (monom_var l,
                   scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r))
    | GEQ_ns (l, r) ->
        (if less_rat (monom_coeff l) zero_rata
          then Leq (monom_var l,
                     scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r)
          else Geq (monom_var l,
                     scaleRat_QDeltaa (inverse_rat (monom_coeff l)) r));;

let rec qdelta_constraint_to_atom
  x0 v = match x0, v with
    LEQ_ns (l, r), v ->
      (if is_monom l then monom_to_atom (LEQ_ns (l, r)) else Leq (v, r))
    | GEQ_ns (l, r), v ->
        (if is_monom l then monom_to_atom (GEQ_ns (l, r)) else Geq (v, r));;

let rec firstFreshVariable (IState (x1, x2, x3, x4)) = x1;;

let rec poly_Mapping (IState (x1, x2, x3, x4)) = x4;;

let rec linear_poly_to_eq p v = (v, p);;

let rec preprocessa
  x0 v = match x0, v with [], v -> IState (v, [], [], (fun _ -> None))
    | (i, h) :: t, v ->
        (let s = preprocessa t v in
         let p = poly h in
         let is_monom_h = is_monom p in
         let va = firstFreshVariable s in
         let ta = tableau s in
         let a = atoms s in
         let m = poly_Mapping s in
          (if is_monom_h
            then IState (va, ta, (i, qdelta_constraint_to_atom h va) :: a, m)
            else (match m p
                   with None ->
                     IState
                       (plus_nat va one_nat, linear_poly_to_eq p va :: ta,
                         (i, qdelta_constraint_to_atom h va) :: a,
                         fun_upd equal_linear_poly m p (Some va))
                   | Some vaa ->
                     IState
                       (va, ta, (i, qdelta_constraint_to_atom h vaa) :: a,
                         m))));;

let rec preprocess_part_1
  l = (let start = start_fresh_variable l in
       let is = preprocessa l start in
        (tableau is, atoms is));;

let rec preprocess
  l = (let (t, asa) = preprocess_part_1 l in
       let (ta, tv) = preprocess_part_2 lrv_QDelta asa t in
        (ta, (asa, tv)));;

let rec solve_exec_ns_code _A
  s = (let (t, (asa, trans_v)) = preprocess s in
        (match assert_all_code _A (equal_QDelta, lrv_QDelta) t asa
          with Inl a -> Inl a | Inr v -> Inr (trans_v v)));;

let rec solve_exec_code _A
  cs = (let csa = to_ns cs in
         (match solve_exec_ns_code _A csa with Inl a -> Inl a
           | Inr v -> Inr (from_ns v (map snd csa))));;

let rec simplex_index _A = solve_exec_code _A;;

let rec simplex
  cs = simplex_index equal_nat (zip (upt zero_nat (size_list cs)) cs);;

let rec binda m f = (match m with Inl a -> Inl a | Inr a -> f a);;

let rec form_not = function Atom a -> NegAtom a
                   | NegAtom a -> Atom a
                   | Conjunction phi_s -> Disjunction (map form_not phi_s)
                   | Disjunction phi_s -> Conjunction (map form_not phi_s);;

let rec get_Atom = function Atom a -> a
                   | NegAtom a -> a;;

let rec simplify
  = function
    Disjunction (phi :: phi_s) ->
      form_or (simplify phi) (simplify (Disjunction phi_s))
    | Conjunction [phi] -> simplify phi
    | Conjunction (phi :: v :: va) ->
        form_and (simplify phi) (simplify (Conjunction (v :: va)))
    | Atom v -> Atom v
    | NegAtom v -> NegAtom v
    | Conjunction [] -> Conjunction []
    | Disjunction [] -> Disjunction [];;

let rec of_alist _A
  xs = foldr (fun (a, b) -> updatea _A a b) xs
         (emptya _A.linorder_compare_order);;

let rec map_sum f1 f2 x2 = match f1, f2, x2 with f1, f2, Inl a -> Inl (f1 a)
                  | f1, f2, Inr a -> Inr (f2 a);;

let rec is_Var = function Var x1 -> true
                 | Fun (x21, x22) -> false;;

let rec check b e = (if b then Inr () else Inl e);;

let rec or_ok x0 b = match x0, b with Inl a, b -> b
                | Inr a, b -> Inr a;;

let rec catch_error m f = (match m with Inl a -> f a | Inr a -> Inr a);;

let rec forallM
  f x1 = match f, x1 with f, [] -> Inr ()
    | f, x :: xs ->
        binda (catch_error (f x) (fun xa -> Inl (x, xa)))
          (fun _ -> forallM f xs);;

let rec is_neg_atom = function NegAtom uu -> true
                      | Atom v -> false
                      | Conjunction v -> false
                      | Disjunction v -> false;;

let rec showsl_hint _A
  = function Default -> showsl_lit " auto"
    | Base raw -> comp (showsl_lit " ") (showsl _A raw)
    | Distribute (i, hints) ->
        comp (comp (showsl_lit " Distribute ") (showsl_nat i))
          (showsl_list_gen id " []" " [" ", " "]" (map (showsl_hint _A) hints))
    | LexStrict hints ->
        comp (showsl_lit " LexStrict")
          (showsl_list_gen id " []" " [" ", " "]" (map (showsl_hint _A) hints))
    | LexWeak hints ->
        comp (showsl_lit " LexWeak")
          (showsl_list_gen id " []" " [" ", " "]" (map (showsl_hint _A) hints))
    | Erase (i, hint) ->
        comp (comp (comp (comp (showsl_lit " Erase ") (showsl_nat i))
                     (showsl_lit " ["))
               (showsl_hint _A hint))
          (showsl_lit " ]");;

let rec one_monom _A = Abs_monom [];;

let zero_poly : ('a monom * 'b) list = [];;

let rec var_monom _A xa = Abs_monom [(xa, one_nat)];;

let rec monom_mult_list (_A1, _A2)
  x0 n = match x0, n with [], n -> n
    | (x, p) :: m, n ->
        (match n with [] -> (x, p) :: m
          | (y, q) :: na ->
            (if eq _A1 x y
              then (x, plus_nat p q) :: monom_mult_list (_A1, _A2) m na
              else (if less _A2.order_linorder.preorder_order.ord_preorder x y
                     then (x, p) :: monom_mult_list (_A1, _A2) m n
                     else (y, q) ::
                            monom_mult_list (_A1, _A2) ((x, p) :: m) na)));;

let rec times_monom (_A1, _A2)
  xb xc =
    Abs_monom
      (monom_mult_list (_A1, _A2) (rep_monom _A2 xb) (rep_monom _A2 xc));;

let rec monom_mult_poly (_A1, _A2) (_B1, _B2)
  uu x1 = match uu, x1 with uu, [] -> []
    | (ma, c), (m, d) :: p ->
        (if eq _B1 (times _B2.mult_zero_semiring_0.times_mult_zero c d)
              (zeroa _B2.mult_zero_semiring_0.zero_mult_zero)
          then monom_mult_poly (_A1, _A2) (_B1, _B2) (ma, c) p
          else (times_monom (_A1, _A2) ma m,
                 times _B2.mult_zero_semiring_0.times_mult_zero c d) ::
                 monom_mult_poly (_A1, _A2) (_B1, _B2) (ma, c) p);;

let rec poly_add (_A1, _A2) (_B1, _B2)
  x0 q = match x0, q with [], q -> q
    | (m, c) :: p, q ->
        (match extract (fun mc -> eq (equal_monom (_A1, _A2)) (fst mc) m) q
          with None -> (m, c) :: poly_add (_A1, _A2) (_B1, _B2) p q
          | Some (q1, ((_, d), q2)) ->
            (if eq _B1
                  (plus _B2.comm_monoid_add_semiring_0.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
                    c d)
                  (zeroa _B2.mult_zero_semiring_0.zero_mult_zero)
              then poly_add (_A1, _A2) (_B1, _B2) p (q1 @ q2)
              else (m, plus _B2.comm_monoid_add_semiring_0.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
                         c d) ::
                     poly_add (_A1, _A2) (_B1, _B2) p (q1 @ q2)));;

let rec poly_mult (_A1, _A2) (_B1, _B2)
  x0 q = match x0, q with [], q -> []
    | mc :: p, q ->
        poly_add (_A1, _A2) (_B1, _B2)
          (monom_mult_poly (_A1, _A2) (_B1, _B2) mc q)
          (poly_mult (_A1, _A2) (_B1, _B2) p q);;

let rec one_poly _A _B
  = [(one_monom _A,
       one _B.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral)];;

let rec poly_of (_A1, _A2) (_B1, _B2)
  = function
    PNum i ->
      (if eq _B1 i
            (zeroa
              _B2.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero)
        then [] else [(one_monom _A2, i)])
    | PVar x ->
        [(var_monom _A2 x,
           one _B2.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral)]
    | PSum [] -> zero_poly
    | PSum (p :: ps) ->
        poly_add (_A1, _A2)
          (_B1, _B2.semiring_1_comm_semiring_1.semiring_0_semiring_1)
          (poly_of (_A1, _A2) (_B1, _B2) p)
          (poly_of (_A1, _A2) (_B1, _B2) (PSum ps))
    | PMult [] -> one_poly _A2 _B2.semiring_1_comm_semiring_1
    | PMult (p :: ps) ->
        poly_mult (_A1, _A2)
          (_B1, _B2.semiring_1_comm_semiring_1.semiring_0_semiring_1)
          (poly_of (_A1, _A2) (_B1, _B2) p)
          (poly_of (_A1, _A2) (_B1, _B2) (PMult ps));;

let zero : (nat, rat) fmap = fmempty;;

let rec all_interval_nat
  p i j = less_eq_nat j i || p i && all_interval_nat p (suc i) j;;

let rec power _A
  a n = (if equal_nata n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nat)));;

let rec eval_monom_list _A _B
  alpha x1 = match alpha, x1 with
    alpha, [] ->
      one _B.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral
    | alpha, (x, p) :: m ->
        times _B.comm_monoid_mult_comm_semiring_1.dvd_comm_monoid_mult.times_dvd
          (eval_monom_list _A _B alpha m)
          (power
            _B.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.monoid_mult_semiring_numeral.power_monoid_mult
            (alpha x) p);;

let rec eval_monom _A _B x xc = eval_monom_list _A _B x (rep_monom _A xc);;

let rec eval_poly _A _B
  alpha x1 = match alpha, x1 with
    alpha, [] ->
      zeroa _B.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero
    | alpha, mc :: p ->
        plus _B.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
          (times
            _B.comm_monoid_mult_comm_semiring_1.dvd_comm_monoid_mult.times_dvd
            (eval_monom _A _B alpha (fst mc)) (snd mc))
          (eval_poly _A _B alpha p);;

let rec poly_const (_A1, _A2) _B
  a = (if eq _A2 a (zeroa _A1) then [] else [(one_monom _B, a)]);;

let rec poly_minus (_A1, _A2) (_B1, _B2)
  f g = poly_add (_A1, _A2)
          (_B1, _B2.semiring_1_cancel_ring_1.semiring_1_semiring_1_cancel.semiring_0_semiring_1)
          f (monom_mult_poly (_A1, _A2)
              (_B1, _B2.semiring_1_cancel_ring_1.semiring_1_semiring_1_cancel.semiring_0_semiring_1)
              (one_monom _A2,
                uminus
                  _B2.neg_numeral_ring_1.group_add_neg_numeral.uminus_group_add
                  (one _B2.neg_numeral_ring_1.numeral_neg_numeral.one_numeral))
              g);;

let rec explode
  s = map char_of_integer
        (let s = s in let rec exp i l = if i < 0 then l else exp (i - 1) (let k = Char.code (Bytes.get s i) in
      if k < 128 then Big_int.big_int_of_int k :: l else failwith "Non-ASCII character in literal") in exp (Bytes.length s - 1) []);;

let rec trivial_checker _A
  lits =
    (let (asa, nas) = partition is_Atom lits in
     let pos = map get_Atom asa in
     let neg = map get_Atom nas in
      list_ex (membera _A neg) pos);;

let rec trivial_formula
  = function Disjunction phi_s -> list_ex trivial_formula phi_s
    | Conjunction phi_s -> list_all trivial_formula phi_s
    | Atom v -> false
    | NegAtom v -> false;;

let rec has_type _B
  type_of_fun x1 ty = match type_of_fun, x1, ty with
    type_of_fun, Fun (f, es), ty ->
      eq _B ty (snd (type_of_fun f)) &&
        (equal_nata (size_list es) (size_list (fst (type_of_fun f))) &&
          all_interval_nat
            (fun i ->
              has_type _B type_of_fun (nth es i) (nth (fst (type_of_fun f)) i))
            zero_nat (size_list es))
    | type_of_fun, Var v, ty -> eq _B (snd v) ty;;

let rec is_bool _B
  type_of_fun bool_types e =
    bex bool_types (has_type _B type_of_fun e) && not (is_Var e);;

let bot_set : 'a set = Set [];;

let rec is_neg_atom_clause = function NegAtom a -> false
                             | Atom a -> false
                             | Conjunction xs -> false
                             | Disjunction ls -> list_all is_neg_atom ls;;

let rec monom_list_linearity
  = function [] -> Onea
    | [(x, n)] -> (if equal_nata n one_nat then Variable x else Non_Linear)
    | v :: vb :: vc -> Non_Linear;;

let rec monom_linearity _A xa = monom_list_linearity (rep_monom _A xa);;

let rec monom_vars_list _A xa = map fst (rep_monom _A xa);;

let rec poly_vars_list (_A1, _A2)
  p = remdups _A1 (maps (comp (monom_vars_list _A2) fst) p);;

let rec monom_list_linearitya
  = function [] -> Oneb
    | [(x, n)] -> (if equal_nata n one_nat then Variablea x else Non_Lineara)
    | v :: vb :: vc -> Non_Lineara;;

let rec monom_linearitya _A xa = monom_list_linearitya (rep_monom _A xa);;

let rec negate
  = function Fun (LessF, [a; b]) -> Atom (Fun (LeF, [b; a]))
    | Fun (LeF, [a; b]) -> Atom (Fun (LessF, [b; a]))
    | Fun (EqF, [a; b]) ->
        Disjunction [Atom (Fun (LessF, [a; b])); Atom (Fun (LessF, [b; a]))]
    | Var v -> Conjunction []
    | Fun (LeF, []) -> Conjunction []
    | Fun (LeF, [v]) -> Conjunction []
    | Fun (LeF, v :: vc :: ve :: vf) -> Conjunction []
    | Fun (SumF vb, va) -> Conjunction []
    | Fun (ConstF vb, va) -> Conjunction []
    | Fun (ProdF vb, va) -> Conjunction []
    | Fun (EqF, []) -> Conjunction []
    | Fun (EqF, [v]) -> Conjunction []
    | Fun (EqF, v :: vc :: ve :: vf) -> Conjunction []
    | Fun (v, []) -> Conjunction []
    | Fun (v, [vb]) -> Conjunction []
    | Fun (v, vb :: vd :: vf :: vg) -> Conjunction [];;

let rec negatea
  = function Fun (LessFa, [a; b]) -> Atom (Fun (LeFa, [b; a]))
    | Fun (LeFa, [a; b]) -> Atom (Fun (LessFa, [b; a]))
    | Fun (EqFa, [a; b]) ->
        Disjunction [Atom (Fun (LessFa, [a; b])); Atom (Fun (LessFa, [b; a]))]
    | Var v -> Conjunction []
    | Fun (LeFa, []) -> Conjunction []
    | Fun (LeFa, [v]) -> Conjunction []
    | Fun (LeFa, v :: vc :: ve :: vf) -> Conjunction []
    | Fun (SumFa vb, va) -> Conjunction []
    | Fun (ConstFa vb, va) -> Conjunction []
    | Fun (ProdFa vb, va) -> Conjunction []
    | Fun (EqFa, []) -> Conjunction []
    | Fun (EqFa, [v]) -> Conjunction []
    | Fun (EqFa, v :: vc :: ve :: vf) -> Conjunction []
    | Fun (v, []) -> Conjunction []
    | Fun (v, [vb]) -> Conjunction []
    | Fun (v, vb :: vd :: vf :: vg) -> Conjunction [];;

let rec lp_monom
  c x = LinearPoly
          (if equal_rata c zero_rata then fmempty
            else fmupd equal_nat x c fmempty);;

let rec trivial_clause_checker _A
  f = (let Disjunction a = f in trivial_checker _A a);;

let rec apply_hint (_A1, _A2)
  uu x1 = match uu, x1 with
    n :: ns, Poly_Ge a :: asa ->
      poly_add (_A1, _A2) (equal_int, semiring_0_int)
        (poly_mult (_A1, _A2) (equal_int, semiring_0_int)
          (poly_const (zero_int, equal_int) _A2 (abs_int n)) a)
        (apply_hint (_A1, _A2) ns asa)
    | n :: ns, Poly_Eq a :: asa ->
        poly_add (_A1, _A2) (equal_int, semiring_0_int)
          (poly_mult (_A1, _A2) (equal_int, semiring_0_int)
            (poly_const (zero_int, equal_int) _A2 n) a)
          (apply_hint (_A1, _A2) ns asa)
    | [], Poly_Ge a :: asa ->
        poly_add (_A1, _A2) (equal_int, semiring_0_int) a
          (apply_hint (_A1, _A2) [] asa)
    | [], Poly_Eq a :: asa ->
        poly_add (_A1, _A2) (equal_int, semiring_0_int) a
          (apply_hint (_A1, _A2) [] asa)
    | uu, [] -> poly_const (zero_int, equal_int) _A2 zero_inta;;

let rec iA_exp_to_tpoly
  = function Var (a, ty) -> PVar a
    | Fun (SumF uu, asa) -> PSum (map iA_exp_to_tpoly asa)
    | Fun (ConstF a, []) -> PNum a
    | Fun (ProdF uv, asa) -> PMult (map iA_exp_to_tpoly asa);;

let rec iA_exp_to_poly (_A1, _A2)
  = comp (poly_of (_A1, _A2) (equal_int, comm_semiring_1_int)) iA_exp_to_tpoly;;

let rec iA_exp_to_poly_constraint (_A1, _A2)
  = function
    Fun (LeF, [a; b]) ->
      Poly_Ge
        (poly_minus (_A1, _A2) (equal_int, ring_1_int)
          (iA_exp_to_poly (_A1, _A2) b) (iA_exp_to_poly (_A1, _A2) a))
    | Fun (EqF, [a; b]) ->
        Poly_Eq
          (poly_minus (_A1, _A2) (equal_int, ring_1_int)
            (iA_exp_to_poly (_A1, _A2) b) (iA_exp_to_poly (_A1, _A2) a))
    | Fun (LessF, [a; b]) ->
        Poly_Ge
          (poly_minus (_A1, _A2) (equal_int, ring_1_int)
            (poly_minus (_A1, _A2) (equal_int, ring_1_int)
              (iA_exp_to_poly (_A1, _A2) b) (iA_exp_to_poly (_A1, _A2) a))
            (one_poly _A2 semiring_1_int));;

let rec showsl_literal s = showsl_lit s;;

let rec showsl_monom_list (_A1, _A2)
  = function
    [(x, p)] ->
      (if equal_nata p one_nat then comp (showsl_lit "x") (showsl _A2 x)
        else comp (comp (comp (showsl_lit "x") (showsl _A2 x)) (showsl_lit "^"))
               (showsl_nat p))
    | (x, p) :: v :: va ->
        comp (comp (if equal_nata p one_nat
                     then comp (showsl_lit "x") (showsl _A2 x)
                     else comp (comp (comp (showsl_lit "x") (showsl _A2 x))
                                 (showsl_literal "^"))
                            (showsl_nat p))
               (showsl_literal "*"))
          (showsl_monom_list (_A1, _A2) (v :: va))
    | [] -> showsl_literal "1";;

let rec showsl_monom (_A1, _A2)
  xa = showsl_monom_list (_A1, _A2) (rep_monom _A1 xa);;

let rec showsl_poly (_A1, _A2, _A3) (_B1, _B2, _B3)
  = function [] -> showsl_lit "0"
    | (m, c) :: p ->
        comp (if eq _B2 c (one _B1) then showsl_monom (_A2, _A3) m
               else (if eq (equal_monom (_A1, _A2)) m (one_monom _A2)
                      then showsl _B3 c
                      else comp (comp (showsl _B3 c) (showsl_lit "*"))
                             (showsl_monom (_A2, _A3) m)))
          (if null p then id
            else comp (showsl_lit " + ")
                   (showsl_poly (_A1, _A2, _A3) (_B1, _B2, _B3) p));;

let rec showsl_poly_constraint (_A1, _A2, _A3)
  = function
    Poly_Ge p ->
      comp (showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int) p)
        (showsl_lit " >= 0")
    | Poly_Eq p ->
        comp (showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int) p)
          (showsl_lit " = 0");;

let rec translate_atom (Atom e) = e;;

let rec translate_atoms x = map translate_atom x;;

let rec translate_conj (Conjunction phi_s) = translate_atoms phi_s;;

let rec poly_is_negative_constant (_A1, _A2, _A3)
  f = catch_error
        (binda
          (check (null (poly_vars_list (_A1, _A2) f))
            (showsl_lit "polynomial is not a constant"))
          (fun _ ->
            check (less_int
                    (eval_poly _A2 comm_semiring_1_int (fun _ -> zero_inta) f)
                    zero_inta)
              (showsl_lit "polynomial is not a negative constant")))
        (fun x ->
          Inl (comp (comp (comp (showsl_lit "could not that ")
                            (showsl_poly (_A1, _A2, _A3)
                              (one_int, equal_int, showl_int) f))
                      (showsl_lit " is a negative constant\092"))
                x));;

let rec vars_poly_constraint_list (_A1, _A2)
  = function Poly_Ge p -> poly_vars_list (_A1, _A2) p
    | Poly_Eq p -> poly_vars_list (_A1, _A2) p;;

let zero_linear_poly : linear_poly = LinearPoly zero;;

let rec ipoly_to_linear_poly _A
  rho x1 = match rho, x1 with rho, [] -> Some (zero_linear_poly, zero_inta)
    | rho, (mon, c) :: rest ->
        bind (ipoly_to_linear_poly _A rho rest)
          (fun (p, d) ->
            (match monom_linearity _A mon with Non_Linear -> None
              | Onea -> Some (p, plus_inta c d)
              | Variable x ->
                Some (plus_linear_poly (lp_monom (of_int c) (rho x)) p, d)));;

let rec to_simplex_constraint _A
  rho x1 = match rho, x1 with
    rho, Poly_Ge p ->
      (match ipoly_to_linear_poly _A rho p with None -> []
        | Some (q, c) -> [GEQ (q, of_int (uminus_inta c))])
    | rho, Poly_Eq p ->
        (match ipoly_to_linear_poly _A rho p with None -> []
          | Some (q, c) -> [EQ (q, of_int (uminus_inta c))]);;

let rec unsat_via_simplex (_A1, _A2)
  les = (let vs =
           remdups _A2
             (maps (vars_poly_constraint_list (_A2, _A1.linorder_compare_order))
               les)
           in
         let ren_map = of_alist _A1 (zip vs (upt zero_nat (size_list vs))) in
         let ren_fun =
           (fun v ->
             (match lookupa _A1 ren_map v with None -> zero_nat | Some n -> n))
           in
         let cs =
           maps (to_simplex_constraint _A1.linorder_compare_order ren_fun) les
           in
          (match simplex cs with Inl _ -> true | Inr _ -> false));;

let rec unsat_checker (_A1, _A2, _A3)
  hints cnjs =
    catch_error
      (match hints
        with Hints coeffs ->
          or_ok (poly_is_negative_constant
                  (_A2, _A1.linorder_compare_order, _A3)
                  (apply_hint (_A2, _A1.linorder_compare_order)
                    (zero_inta :: coeffs) cnjs))
            (poly_is_negative_constant (_A2, _A1.linorder_compare_order, _A3)
              (apply_hint (_A2, _A1.linorder_compare_order) (one_inta :: coeffs)
                cnjs))
        | Simplex ->
          check (unsat_via_simplex (_A1, _A2) cnjs)
            (showsl_lit
              "could not use simplex algorithm to prove unsatisfiability"))
      (fun x ->
        Inl (comp (comp (comp (comp (comp (showsl_lit
    "The linear inequalities\092  ")
                                      (showsl_sep
(showsl_poly_constraint (_A2, _A1.linorder_compare_order, _A3))
(showsl_lit "\092  ") cnjs))
                                (showsl_lit
                                  "\092cannot be proved unsatisfiable via hints\092  "))
                          (showsl_hints hints))
                    (showsl_literal "\092"))
              x));;

let rec check_clause (_A1, _A2, _A3)
  hints phi =
    (let es =
       map (iA_exp_to_poly_constraint (_A2, _A1.linorder_compare_order))
         (translate_conj (form_not phi))
       in
      catch_error (unsat_checker (_A1, _A2, _A3) hints es)
        (fun x ->
          Inl (comp (comp (comp (showsl_lit
                                  "Could not prove unsatisfiability of IA conjunction\092")
                            (showsl_list_gen
                              (showsl_poly_constraint
                                (_A2, _A1.linorder_compare_order, _A3))
                              "False" "" " && " "" es))
                      (showsl_literal "\092"))
                x)));;

let rec rA_exp_to_tpoly
  = function Var (a, ty) -> PVar a
    | Fun (SumFa uu, asa) -> PSum (map rA_exp_to_tpoly asa)
    | Fun (ConstFa a, []) -> PNum a
    | Fun (ProdFa uv, asa) -> PMult (map rA_exp_to_tpoly asa);;

let rec rA_exp_to_poly (_A1, _A2)
  = comp (poly_of (_A1, _A2) (equal_rat, comm_semiring_1_rat)) rA_exp_to_tpoly;;

let rec rA_exp_to_poly_constraint (_A1, _A2)
  = function
    Fun (LeFa, [a; b]) ->
      Poly_Gea
        (poly_minus (_A1, _A2) (equal_rat, ring_1_rat)
          (rA_exp_to_poly (_A1, _A2) b) (rA_exp_to_poly (_A1, _A2) a))
    | Fun (EqFa, [a; b]) ->
        Poly_Eqa
          (poly_minus (_A1, _A2) (equal_rat, ring_1_rat)
            (rA_exp_to_poly (_A1, _A2) b) (rA_exp_to_poly (_A1, _A2) a))
    | Fun (LessFa, [a; b]) ->
        Poly_Gt
          (poly_minus (_A1, _A2) (equal_rat, ring_1_rat)
            (rA_exp_to_poly (_A1, _A2) b) (rA_exp_to_poly (_A1, _A2) a));;

let rec showsl_poly_constrainta (_A1, _A2, _A3)
  = function
    Poly_Gea p ->
      comp (showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat) p)
        (showsl_lit " >= 0")
    | Poly_Eqa p ->
        comp (showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat) p)
          (showsl_lit " = 0")
    | Poly_Gt p ->
        comp (showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat) p)
          (showsl_lit " > 0");;

let rec translate_atoma (Atom e) = e;;

let rec translate_atomsa x = map translate_atoma x;;

let rec translate_conja (Conjunction phi_s) = translate_atomsa phi_s;;

let rec vars_poly_constraint_lista (_A1, _A2)
  = function Poly_Gea p -> poly_vars_list (_A1, _A2) p
    | Poly_Eqa p -> poly_vars_list (_A1, _A2) p
    | Poly_Gt p -> poly_vars_list (_A1, _A2) p;;

let rec rpoly_to_linear_poly _A
  rho x1 = match rho, x1 with rho, [] -> Some (zero_linear_poly, zero_rata)
    | rho, (mon, c) :: rest ->
        bind (rpoly_to_linear_poly _A rho rest)
          (fun (p, d) ->
            (match monom_linearitya _A mon with Non_Lineara -> None
              | Oneb -> Some (p, plus_rata c d)
              | Variablea x ->
                Some (plus_linear_poly (lp_monom c (rho x)) p, d)));;

let rec to_simplex_constrainta _A
  rho x1 = match rho, x1 with
    rho, Poly_Gea p ->
      (match rpoly_to_linear_poly _A rho p with None -> []
        | Some (q, c) -> [GEQ (q, uminus_rata c)])
    | rho, Poly_Gt p ->
        (match rpoly_to_linear_poly _A rho p with None -> []
          | Some (q, c) -> [GT (q, uminus_rata c)])
    | rho, Poly_Eqa p ->
        (match rpoly_to_linear_poly _A rho p with None -> []
          | Some (q, c) -> [EQ (q, uminus_rata c)]);;

let rec unsat_via_simplexa (_A1, _A2)
  les = (let vs =
           remdups _A2
             (maps (vars_poly_constraint_lista
                     (_A2, _A1.linorder_compare_order))
               les)
           in
         let ren_map = of_alist _A1 (zip vs (upt zero_nat (size_list vs))) in
         let ren_fun =
           (fun v ->
             (match lookupa _A1 ren_map v with None -> zero_nat | Some n -> n))
           in
         let cs =
           maps (to_simplex_constrainta _A1.linorder_compare_order ren_fun) les
           in
          (match simplex cs with Inl _ -> true | Inr _ -> false));;

let rec unsat_checkera (_A1, _A2, _A3)
  cnjs =
    catch_error
      (check (unsat_via_simplexa (_A1, _A2) cnjs)
        (showsl_lit
          "could not use simplex algorithm to prove unsatisfiability"))
      (fun x ->
        Inl (comp (comp (comp (showsl_lit "The linear inequalities\092  ")
                          (showsl_sep
                            (showsl_poly_constrainta
                              (_A2, _A1.linorder_compare_order, _A3))
                            (showsl_lit "\092  ") cnjs))
                    (showsl_lit "\092cannot be proved unsatisfiable\092"))
              x));;

let rec check_clausea (_A1, _A2, _A3)
  h phi =
    (let es =
       map (rA_exp_to_poly_constraint (_A2, _A1.linorder_compare_order))
         (translate_conja (form_not phi))
       in
      catch_error (unsat_checkera (_A1, _A2, _A3) es)
        (fun x ->
          Inl (comp (comp (comp (showsl_lit
                                  "Could not prove unsatisfiability of RA conjunction\092")
                            (showsl_list_gen
                              (showsl_poly_constrainta
                                (_A2, _A1.linorder_compare_order, _A3))
                              "False" "" " && " "" es))
                      (showsl_literal "\092"))
                x)));;

let rec create_rat
  num denom =
    divide_rat (comp of_int (fun a -> Int_of_integer a) num)
      (comp of_int (fun a -> Int_of_integer a) denom);;

let rec of_Formula = function FAtom a -> Atom a
                     | FNegate phi -> form_not (of_Formula phi)
                     | FConjunction phi_s -> form_all (map of_Formula phi_s)
                     | FDisjunction phi_s -> form_ex (map of_Formula phi_s);;

let rec remove_Atom _B
  negate_atom x1 = match negate_atom, x1 with
    negate_atom, Atom phi -> form_not (negate_atom phi)
    | negate_atom, NegAtom phi -> NegAtom phi
    | negate_atom, Disjunction phi_s ->
        Disjunction (map (remove_Atom _B negate_atom) phi_s)
    | negate_atom, Conjunction phi_s ->
        Conjunction (map (remove_Atom _B negate_atom) phi_s);;

let rec showsl_formula
  showsl_atom x1 = match showsl_atom, x1 with
    showsl_atom, Disjunction fs ->
      (let a = map (showsl_formula showsl_atom) fs in
        showsl_list_gen id "False" "Disj[" ", " "]" a)
    | showsl_atom, Conjunction fs ->
        (let a = map (showsl_formula showsl_atom) fs in
          showsl_list_gen id "True" "Conj[" ", " "]" a)
    | showsl_atom, NegAtom a ->
        comp (comp (showsl_literal "! (") (showsl_atom a)) (showsl_literal ")")
    | showsl_atom, Atom a -> showsl_atom a;;

let rec is_or_and_shape
  = function Disjunction (va :: vc :: ve :: vf) -> false
    | Disjunction (va :: Disjunction ve :: vd) -> false
    | Disjunction (va :: Conjunction (vf :: vh :: vj :: vk) :: vd) -> false
    | Disjunction (va :: Conjunction [vf] :: vd) -> false
    | Disjunction (va :: Conjunction [] :: vd) -> false
    | Disjunction (va :: NegAtom ve :: vd) -> false
    | Disjunction (va :: Atom ve :: vd) -> false
    | Disjunction [va] -> false
    | Disjunction [] -> false
    | Conjunction v -> false
    | NegAtom v -> false
    | Atom v -> false
    | Disjunction [phi_1; Conjunction [phi_2; phi_3]] -> true;;

let rec check_valid_formula _A (_B1, _B2) _C (_D1, _D2)
  showsl_atom logic_checker negate_atom phi =
    catch_error
      (let Conjunction phi_s = flatten phi in
        catch_error
          (forallM
            (fun phia ->
              catch_error
                (check
                  (trivial_clause_checker (equal_term _A (equal_prod _B1 _C))
                    phia)
                  "trivial clause checker failed")
                (fun _ ->
                  (let Conjunction phi_sa =
                     flatten (remove_Atom _B2 negate_atom phia) in
                    catch_error (forallM (logic_checker (default _D1)) phi_sa)
                      (fun x -> Inl (snd x)))))
            phi_s)
          (fun x -> Inl (snd x)))
      (fun x ->
        Inl (comp (comp (comp (showsl_lit
                                "problem in checking validity of formula ")
                          (showsl_formula showsl_atom phi))
                    (showsl_literal "\092"))
              x));;

let rec is_disj_shape
  uu uv = match uu, uv with uu, Disjunction (va :: vc :: ve :: vf) -> false
    | uu, Disjunction (va :: Disjunction ve :: vd) -> false
    | uu, Disjunction (va :: Conjunction (vf :: vh :: vj :: vk) :: vd) -> false
    | uu, Disjunction (va :: Conjunction [vf] :: vd) -> false
    | uu, Disjunction (va :: Conjunction [] :: vd) -> false
    | uu, Disjunction (va :: NegAtom ve :: vd) -> false
    | uu, Disjunction (va :: Atom ve :: vd) -> false
    | uu, Disjunction [va] -> false
    | uu, Disjunction (Disjunction vc :: vb) -> false
    | uu, Disjunction (Conjunction (vd :: vf :: vh :: vi) :: vb) -> false
    | uu, Disjunction (Conjunction [vd] :: vb) -> false
    | uu, Disjunction (Conjunction [] :: vb) -> false
    | uu, Disjunction (NegAtom vc :: vb) -> false
    | uu, Disjunction (Atom vc :: vb) -> false
    | uu, Disjunction [] -> false
    | uu, Conjunction v -> false
    | uu, NegAtom v -> false
    | uu, Atom v -> false
    | [], uv -> false
    | hint1 :: hints,
        Disjunction [Conjunction [phi_1; phi_2]; Conjunction [phi_3; phi_4]]
        -> true;;

let rec is_conj_shape uu uv = match uu, uv with uu, Disjunction v -> false
                        | uu, Conjunction (va :: vc :: ve :: vf) -> false
                        | uu, Conjunction [va] -> false
                        | uu, Conjunction [] -> false
                        | uu, NegAtom v -> false
                        | uu, Atom v -> false
                        | v :: vb :: vd :: ve, uv -> false
                        | [v], uv -> false
                        | [], uv -> false
                        | [hint1; hint2], Conjunction [phi_1; phi_2] -> true;;

let rec check_formula _A (_B1, _B2) _C (_D1, _D2)
  showsl_atom logic_checker negate_atom x3 psi = match
    showsl_atom, logic_checker, negate_atom, x3, psi with
    showsl_atom, logic_checker, negate_atom, LexStrict hints, psi ->
      (match psi
        with Atom _ ->
          Inl (comp (showsl_literal "LexStrict hint applied on ")
                (showsl_formula showsl_atom psi))
        | NegAtom _ ->
          Inl (comp (showsl_literal "LexStrict hint applied on ")
                (showsl_formula showsl_atom psi))
        | Conjunction _ ->
          Inl (comp (showsl_literal "LexStrict hint applied on ")
                (showsl_formula showsl_atom psi))
        | Disjunction a ->
          (match a
            with [] ->
              Inl (comp (showsl_literal "LexStrict hint applied on ")
                    (showsl_formula showsl_atom psi))
            | aa :: b ->
              check_formula_lex _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                logic_checker negate_atom hints aa b))
    | showsl_atom, logic_checker, negate_atom, LexWeak hints, psi ->
        (match psi
          with Atom _ ->
            Inl (comp (showsl_literal "LexWeak hint applied on ")
                  (showsl_formula showsl_atom psi))
          | NegAtom _ ->
            Inl (comp (showsl_literal "LexWeak hint applied on ")
                  (showsl_formula showsl_atom psi))
          | Conjunction _ ->
            Inl (comp (showsl_literal "LexWeak hint applied on ")
                  (showsl_formula showsl_atom psi))
          | Disjunction a ->
            (match a
              with [] ->
                Inl (comp (showsl_literal "LexWeak hint applied on ")
                      (showsl_formula showsl_atom psi))
              | aa :: b ->
                check_formula_lex_weak _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                  logic_checker negate_atom hints aa b))
    | showsl_atom, logic_checker, negate_atom, Distribute (n, hints), phi ->
        (match phi
          with Atom _ ->
            Inl (comp (showsl_literal "Distribute hint for non Disjunction ")
                  (showsl_formula showsl_atom phi))
          | NegAtom _ ->
            Inl (comp (showsl_literal "Distribute hint for non Disjunction ")
                  (showsl_formula showsl_atom phi))
          | Conjunction _ ->
            Inl (comp (showsl_literal "Distribute hint for non Disjunction ")
                  (showsl_formula showsl_atom phi))
          | Disjunction phi_s ->
            (let l = size_list phi_s in
              binda (check (less_nat n l)
                      (comp (comp (comp (showsl_literal
  "distribute hint at position ")
                                    (showsl_nat n))
                              (showsl_literal " while goal is length "))
                        (showsl_nat l)))
                (fun _ ->
                  (let pre = take n phi_s in
                   let post = drop (suc n) phi_s in
                    (match nth phi_s n
                      with Atom _ ->
                        Inl (comp (comp (comp
  (showsl_literal "Distribute hint in: \092") (showsl_formula showsl_atom phi))
                                    (showsl_literal
                                      "\092 at non-Conjunction position:\092"))
                              (showsl_formula showsl_atom (nth phi_s n)))
                      | NegAtom _ ->
                        Inl (comp (comp (comp
  (showsl_literal "Distribute hint in: \092") (showsl_formula showsl_atom phi))
                                    (showsl_literal
                                      "\092 at non-Conjunction position:\092"))
                              (showsl_formula showsl_atom (nth phi_s n)))
                      | Conjunction a ->
                        check_formula_dist _A (_B1, _B2) _C (_D1, _D2)
                          showsl_atom logic_checker negate_atom hints pre post a
                      | Disjunction _ ->
                        Inl (comp (comp (comp
  (showsl_literal "Distribute hint in: \092") (showsl_formula showsl_atom phi))
                                    (showsl_literal
                                      "\092 at non-Conjunction position:\092"))
                              (showsl_formula showsl_atom (nth phi_s n))))))))
    | showsl_atom, logic_checker, negate_atom, Erase (n, hint), phi ->
        (match phi
          with Atom _ -> Inl (showsl_literal "Erase hint to non-Disjunction")
          | NegAtom _ -> Inl (showsl_literal "Erase hint to non-Disjunction")
          | Conjunction _ ->
            Inl (showsl_literal "Erase hint to non-Disjunction")
          | Disjunction phi_s ->
            (let l = size_list phi_s in
              binda (check (less_nat n l)
                      (comp (comp (comp (showsl_literal
  "erase hint at position ")
                                    (showsl_nat n))
                              (showsl_literal " while goal is length "))
                        (showsl_nat l)))
                (fun _ ->
                  (let pre = take n phi_s in
                   let post = drop (suc n) phi_s in
                    check_formula _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                      logic_checker negate_atom hint
                      (Disjunction (pre @ Disjunction [] :: post))))))
    | showsl_atom, logic_checker, negate_atom, Base h, phi ->
        (let psi = remove_Atom _B2 negate_atom (simplify phi) in
          binda (check (is_neg_atom_clause psi)
                  (comp (showsl_literal "base hint given to ")
                    (showsl_formula showsl_atom psi)))
            (fun _ ->
              catch_error (logic_checker h psi)
                (fun x ->
                  Inl (comp (comp (comp (showsl_literal "problem in checking ")
                                    (showsl_formula showsl_atom phi))
                              (showsl_literal "\092"))
                        x))))
    | showsl_atom, logic_checker, negate_atom, Default, phi ->
        check_valid_formula _A (_B1, _B2) _C (_D1, _D2) showsl_atom
          logic_checker negate_atom phi
and check_formula_lex _A (_B1, _B2) _C (_D1, _D2)
  showsl_atom logic_checker negate_atom hints phi phi_s =
    (if is_conj_shape hints phi
      then (let [hint1; hint2] = hints in
            let Conjunction [phi_1; phi_2] = phi in
             binda (check_formula _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                     logic_checker negate_atom hint1
                     (Disjunction (phi_1 :: phi_s)))
               (fun _ ->
                 check_formula _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                   logic_checker negate_atom hint2
                   (Disjunction (phi_2 :: phi_s))))
      else (if is_disj_shape hints phi
             then (let hint1 :: hints2 = hints in
                   let Disjunction
                         [Conjunction [phi_1; phi_2];
                           Conjunction [phi_3; phi_4]]
                     = phi in
                    (match hints2
                      with [] ->
                        binda (check_formula _A (_B1, _B2) _C (_D1, _D2)
                                showsl_atom logic_checker negate_atom hint1
                                (Disjunction (phi_3 :: phi_s)))
                          (fun _ ->
                            check_formula_lex _A (_B1, _B2) _C (_D1, _D2)
                              showsl_atom logic_checker negate_atom hints2 phi_4
                              phi_s)
                      | [hint2] ->
                        binda (check_formula _A (_B1, _B2) _C (_D1, _D2)
                                showsl_atom logic_checker negate_atom hint1
                                (Disjunction (phi_1 :: phi_s)))
                          (fun _ ->
                            check_formula _A (_B1, _B2) _C (_D1, _D2)
                              showsl_atom logic_checker negate_atom hint2
                              (Disjunction (phi_2 :: phi_s)))
                      | _ :: _ :: _ ->
                        binda (check_formula _A (_B1, _B2) _C (_D1, _D2)
                                showsl_atom logic_checker negate_atom hint1
                                (Disjunction (phi_3 :: phi_s)))
                          (fun _ ->
                            check_formula_lex _A (_B1, _B2) _C (_D1, _D2)
                              showsl_atom logic_checker negate_atom hints2 phi_4
                              phi_s)))
             else Inl (comp (comp (comp (showsl_literal
  "LexStrict hint application error: ")
                                    (showsl_hint _D2 (LexStrict hints)))
                              (showsl_literal "\092applied on "))
                        (showsl_formula showsl_atom phi))))
and check_formula_dist _A (_B1, _B2) _C (_D1, _D2)
  showsl_atom logic_checker negate_atom x3 uv uw x6 = match
    showsl_atom, logic_checker, negate_atom, x3, uv, uw, x6 with
    showsl_atom, logic_checker, negate_atom, [], uv, uw, v :: va ->
      Inl (showsl_literal "Length mismatch in Distribute hints")
    | showsl_atom, logic_checker, negate_atom, v :: va, uv, uw, [] ->
        Inl (showsl_literal "Length mismatch in Distribute hints")
    | showsl_atom, logic_checker, negate_atom, h :: hs, pre, post, phi :: phi_s
        -> binda (check_formula _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                   logic_checker negate_atom h
                   (Disjunction (pre @ phi :: post)))
             (fun _ ->
               check_formula_dist _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                 logic_checker negate_atom hs pre post phi_s)
    | showsl_atom, logic_checker, negate_atom, [], pre, post, [] -> Inr ()
and check_formula_lex_weak _A (_B1, _B2) _C (_D1, _D2)
  showsl_atom logic_checker negate_atom x3 phi phi_s = match
    showsl_atom, logic_checker, negate_atom, x3, phi, phi_s with
    showsl_atom, logic_checker, negate_atom, hint :: hints, phi, phi_s ->
      (if is_or_and_shape phi
        then (let Disjunction [_; Conjunction [phi_2; phi_3]] = phi in
               binda (check_formula _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                       logic_checker negate_atom hint
                       (Disjunction (phi_2 :: phi_s)))
                 (fun _ ->
                   check_formula_lex_weak _A (_B1, _B2) _C (_D1, _D2)
                     showsl_atom logic_checker negate_atom hints phi_3 phi_s))
        else (match hints
               with [] ->
                 check_formula _A (_B1, _B2) _C (_D1, _D2) showsl_atom
                   logic_checker negate_atom hint (Disjunction (phi :: phi_s))
               | _ :: _ ->
                 Inl (showsl_literal "LexWeak hint application error")))
    | showsl_atom, logic_checker, negate_atom, [], phi, phi_s ->
        check (trivial_formula phi)
          (comp (showsl_literal "LexWeak base case error: ")
            (showsl_formula showsl_atom phi));;

let rec formula
  atom x1 = match atom, x1 with
    atom, FDisjunction phi_s -> list_all (formula atom) phi_s
    | atom, FConjunction phi_s -> list_all (formula atom) phi_s
    | atom, FNegate phi -> formula atom phi
    | atom, FAtom a -> atom a;;

let rec type_of_fun = function LessF -> ([IntT; IntT], BoolT)
                      | LeF -> ([IntT; IntT], BoolT)
                      | EqF -> ([IntT; IntT], BoolT)
                      | SumF n -> (replicate n IntT, IntT)
                      | ConstF uu -> ([], IntT)
                      | ProdF n -> (replicate n IntT, IntT);;

let rec type_of_funa = function LessFa -> ([RatT; RatT], BoolTa)
                       | LeFa -> ([RatT; RatT], BoolTa)
                       | EqFa -> ([RatT; RatT], BoolTa)
                       | SumFa n -> (replicate n RatT, RatT)
                       | ConstFa uu -> ([], RatT)
                       | ProdFa n -> (replicate n RatT, RatT);;

let rec showsl_IA_exp (_A1, _A2, _A3)
  = function
    Fun (LessF, [s; t]) ->
      comp (comp (showsl_IA_exp (_A1, _A2, _A3) s) (showsl_lit " < "))
        (showsl_IA_exp (_A1, _A2, _A3) t)
    | Fun (LeF, [s; t]) ->
        comp (comp (showsl_IA_exp (_A1, _A2, _A3) s) (showsl_lit " <= "))
          (showsl_IA_exp (_A1, _A2, _A3) t)
    | Fun (EqF, [s; t]) ->
        comp (comp (showsl_IA_exp (_A1, _A2, _A3) s) (showsl_lit " = "))
          (showsl_IA_exp (_A1, _A2, _A3) t)
    | Var v ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Var v))
    | Fun (LeF, []) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (LeF, [])))
    | Fun (LeF, [v]) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (LeF, [v])))
    | Fun (LeF, v :: vc :: ve :: vf) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (LeF, v :: vc :: ve :: vf)))
    | Fun (SumF vb, va) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (SumF vb, va)))
    | Fun (ConstF vb, va) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (ConstF vb, va)))
    | Fun (ProdF vb, va) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (ProdF vb, va)))
    | Fun (EqF, []) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (EqF, [])))
    | Fun (EqF, [v]) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (EqF, [v])))
    | Fun (EqF, v :: vc :: ve :: vf) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (EqF, v :: vc :: ve :: vf)))
    | Fun (v, []) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (v, [])))
    | Fun (v, [vb]) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (v, [vb])))
    | Fun (v, vb :: vd :: vf :: vg) ->
        showsl_poly (_A1, _A2, _A3) (one_int, equal_int, showl_int)
          (iA_exp_to_poly (_A1, _A2) (Fun (v, vb :: vd :: vf :: vg)));;

let rec showsl_RA_exp (_A1, _A2, _A3)
  = function
    Fun (LessFa, [s; t]) ->
      comp (comp (showsl_RA_exp (_A1, _A2, _A3) s) (showsl_lit " < "))
        (showsl_RA_exp (_A1, _A2, _A3) t)
    | Fun (LeFa, [s; t]) ->
        comp (comp (showsl_RA_exp (_A1, _A2, _A3) s) (showsl_lit " <= "))
          (showsl_RA_exp (_A1, _A2, _A3) t)
    | Fun (EqFa, [s; t]) ->
        comp (comp (showsl_RA_exp (_A1, _A2, _A3) s) (showsl_lit " = "))
          (showsl_RA_exp (_A1, _A2, _A3) t)
    | Var v ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Var v))
    | Fun (LeFa, []) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (LeFa, [])))
    | Fun (LeFa, [v]) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (LeFa, [v])))
    | Fun (LeFa, v :: vc :: ve :: vf) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (LeFa, v :: vc :: ve :: vf)))
    | Fun (SumFa vb, va) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (SumFa vb, va)))
    | Fun (ConstFa vb, va) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (ConstFa vb, va)))
    | Fun (ProdFa vb, va) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (ProdFa vb, va)))
    | Fun (EqFa, []) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (EqFa, [])))
    | Fun (EqFa, [v]) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (EqFa, [v])))
    | Fun (EqFa, v :: vc :: ve :: vf) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (EqFa, v :: vc :: ve :: vf)))
    | Fun (v, []) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (v, [])))
    | Fun (v, [vb]) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (v, [vb])))
    | Fun (v, vb :: vd :: vf :: vg) ->
        showsl_poly (_A1, _A2, _A3) (one_rat, equal_rat, showl_rat)
          (rA_exp_to_poly (_A1, _A2) (Fun (v, vb :: vd :: vf :: vg)));;

let rec check_valid_IA_formula (_A1, _A2, _A3)
  phi = map_sum (fun s -> s "") id
          (check_formula equal_sig (_A2, _A3) equal_ty
            (default_hints, showl_hints)
            (showsl_IA_exp (_A2, _A1.linorder_compare_order, _A3))
            (check_clause (_A1, _A2, _A3)) negate Default (of_Formula phi));;

let rec check_valid_RA_formula (_A1, _A2, _A3)
  phi = map_sum (fun s -> s "") id
          (check_formula equal_siga (_A2, _A3) equal_tya
            (default_unit, showl_unit)
            (showsl_RA_exp (_A2, _A1.linorder_compare_order, _A3))
            (check_clausea (_A1, _A2, _A3)) negatea Default (of_Formula phi));;

let rec check_valid_IA_formula_string_vars
  x = check_valid_IA_formula
        ((compare_order_list (compare_order_char, equal_char)),
          (equal_list equal_char), (showl_list showl_char))
        x;;

let rec check_valid_RA_formula_string_vars
  x = check_valid_RA_formula
        ((compare_order_list (compare_order_char, equal_char)),
          (equal_list equal_char), (showl_list showl_char))
        x;;

let rec check_valid_IA_formula_integer_vars
  x = check_valid_IA_formula
        (compare_order_integer, equal_integer, showl_integer) x;;

let rec check_valid_RA_formula_integer_vars
  x = check_valid_RA_formula
        (compare_order_integer, equal_integer, showl_integer) x;;

let rec check_well_formed_IA_formula_string_vars
  x = formula (is_bool equal_ty type_of_fun (inserta equal_ty BoolT bot_set))
        x;;

let rec check_well_formed_RA_formula_string_vars
  x = formula
        (is_bool equal_tya type_of_funa (inserta equal_tya BoolTa bot_set)) x;;

let rec check_well_formed_IA_formula_integer_vars
  x = formula (is_bool equal_ty type_of_fun (inserta equal_ty BoolT bot_set))
        x;;

let rec check_well_formed_RA_formula_integer_vars
  x = formula
        (is_bool equal_tya type_of_funa (inserta equal_tya BoolTa bot_set)) x;;

end;; (*struct Simplex_Validity_Checker*)
