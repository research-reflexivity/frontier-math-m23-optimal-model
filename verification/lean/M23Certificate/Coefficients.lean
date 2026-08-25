import Mathlib

open Polynomial

namespace M23Certificate.Coefficients

/-!
A small, executable coefficient-list model of polynomials.  It is used only as
a reflection layer: `decide` checks list arithmetic, and the lemmas below
transport those checks to mathlib's `Polynomial` type.
-/

def add {R : Type*} [Add R] [Zero R] : List R → List R → List R
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: add as bs

def scale {R : Type*} [Mul R] (a : R) : List R → List R
  | [] => []
  | b :: bs => (a * b) :: scale a bs

def mul {R : Type*} [Semiring R] : List R → List R → List R
  | [], _ => []
  | a :: as, b => add (scale a b) (0 :: mul as b)

def pow {R : Type*} [Semiring R] (a : List R) : ℕ → List R
  | 0 => [1]
  | n + 1 => mul (pow a n) a

/-- Insert `q - 1` zero coefficients after every coefficient.  The final
padding is harmless under `realize` and keeps this definition structurally
recursive and fast to normalize. -/
def expand {R : Type*} [Zero R] (q : ℕ) : List R → List R
  | [] => []
  | a :: as => a :: (List.replicate (q - 1) 0 ++ expand q as)

noncomputable def realize {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | a :: as => C a + X * realize as

@[simp] theorem realize_replicate_zero {R : Type*} [Semiring R] (n : ℕ) :
    realize (List.replicate n (0 : R)) = 0 := by
  induction n with
  | zero => simp [realize]
  | succ n ih => simp [List.replicate_succ, realize, ih]

@[simp] theorem realize_append_replicate_zero {R : Type*} [Semiring R]
    (a : List R) (n : ℕ) :
    realize (a ++ List.replicate n 0) = realize a := by
  induction a with
  | nil => simp [realize]
  | cons a as ih => simp [realize, ih]

theorem realize_replicate_zero_append {R : Type*} [CommSemiring R]
    (n : ℕ) (a : List R) :
    realize (List.replicate n 0 ++ a) = X ^ n * realize a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, realize, ih, pow_succ, mul_assoc, mul_comm]

theorem realize_expand_cons {R : Type*} [CommSemiring R]
    (q : ℕ) (hq : 0 < q) (a : R) (as : List R) :
    realize (expand q (a :: as)) = C a + X ^ q * realize (expand q as) := by
  simp [expand, realize, realize_replicate_zero_append, ← mul_assoc]
  rw [← pow_succ', Nat.sub_add_cancel hq]

def eval {R : Type*} [Semiring R] (x : R) : List R → R
  | [] => 0
  | a :: as => a + x * eval x as

@[simp] theorem coeff_realize {R : Type*} [Semiring R] (a : List R) (n : ℕ) :
    (realize a).coeff n = a.getD n 0 := by
  induction a generalizing n with
  | nil => simp [realize]
  | cons a as ih =>
      cases n with
      | zero => simp [realize]
      | succ n => simp [realize, ih]

theorem natDegree_realize_le {R : Type*} [Semiring R] (a : List R) :
    (realize a).natDegree ≤ a.length - 1 := by
  cases a with
  | nil => simp [realize]
  | cons a as =>
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      have hlen : (a :: as).length ≤ n := by
        simp only [List.length_cons] at hn ⊢
        omega
      rw [coeff_realize, List.getD_eq_default (l := a :: as) (d := 0) hlen]

@[simp] theorem eval_realize {R : Type*} [CommSemiring R] (x : R) (a : List R) :
    Polynomial.eval x (realize a) = eval x a := by
  induction a with
  | nil => simp [realize, eval]
  | cons a as ih => simp [realize, eval, ih]

@[simp] theorem map_realize {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : List R) :
    (realize a).map f = realize (a.map f) := by
  induction a with
  | nil => simp [realize]
  | cons a as ih => simp [realize, ih]

@[simp] theorem realize_add {R : Type*} [CommSemiring R] (a b : List R) :
    realize (add a b) = realize a + realize b := by
  induction a generalizing b with
  | nil => simp [add, realize]
  | cons a as ih =>
      cases b with
      | nil => simp [add, realize]
      | cons b bs =>
          simp [add, realize, ih, mul_add, add_assoc, add_left_comm, add_comm]

@[simp] theorem realize_scale {R : Type*} [CommSemiring R] (a : R) (b : List R) :
    realize (scale a b) = C a * realize b := by
  induction b with
  | nil => simp [scale, realize]
  | cons b bs => simp [scale, realize, *, mul_add, mul_assoc, mul_comm]

@[simp] theorem realize_mul {R : Type*} [CommSemiring R] (a b : List R) :
    realize (mul a b) = realize a * realize b := by
  induction a with
  | nil => simp [mul, realize]
  | cons a as ih => simp [mul, realize, ih]; ring

@[simp] theorem realize_pow {R : Type*} [CommSemiring R] (a : List R) (n : ℕ) :
    realize (pow a n) = realize a ^ n := by
  induction n with
  | zero => simp [pow, realize]
  | succ n ih => simp [pow, ih, pow_succ]

end M23Certificate.Coefficients
