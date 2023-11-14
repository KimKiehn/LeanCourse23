import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by {
      have h1:∀ (n :ℕ),  (∑ i in range (n + 1), i : ℚ)=n*(n+1)/2 := by {
        intro n
        induction n
        case zero => simp
        case succ k ih =>
          rw [sum_range_succ, ih]
          push_cast
          ring
      }

      rw[h1]
      induction n
      case zero => simp
      case succ k ik =>
        rw [sum_range_succ, ik]
        push_cast
        field_simp
        norm_cast
        ring
    }

open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min
  constructor
  · intro i j hij x hx1 hx2
    simp
    by_contra hcon
    have h2: ¬ x = ∅ := by exact ne_of_not_le hcon
    have h1: Set.Nonempty x:= by exact nmem_singleton_empty.mp h2
    obtain ⟨y, hy ⟩:= h1
    have hyi: y∈ C i:= by exact hx1 hy
    have hyj: y∈ C j:= by exact hx2 hy
    have hIJ: i<j ∨ j<i := by exact Ne.lt_or_lt hij
    have heg1: C i= {y | y∈ A i ∧ y∈  (⋃ k, ⋃ (_ : k < i), A k)ᶜ}:= by exact hC i
    have heg2: C j= {y | y∈ A j ∧ y∈  (⋃ k, ⋃ (_ : k < j), A k)ᶜ}:= by exact hC j
    obtain hilj | hjli := hIJ
    · have hyi2: y∈ A i:= by {
        rw[heg1] at hyi
        simp at hyi
        exact hyi.1
      }

      rw[heg2] at hyj
      simp at hyj
      have hnuo:  ∀ i < j, y ∉ A i:= by exact hyj.2
      specialize hnuo i
      exact hnuo hilj hyi2
    · have hyj2: y∈ A j:= by {
        rw[heg2] at hyj
        simp at hyj
        exact hyj.1
      }
      rw[heg1] at hyi
      simp at hyi
      have hnuo:  ∀ j < i, y ∉ A j:= by exact hyi.2
      specialize hnuo j
      exact hnuo hjli hyj2
  · ext x
    simp
    constructor
    · intro h1
      obtain ⟨i, hi ⟩:= h1
      use i
      specialize hC i
      have heg: C i= {y | y∈ A i ∧ y∈  (⋃ j, ⋃ (_ : j < i), A j)ᶜ}:= by exact hC
      have hsub: {y | y∈ A i ∧ y∈  (⋃ j, ⋃ (_ : j < i), A j)ᶜ}⊆ A i:= by {
        intro y hy
        exact mem_of_mem_diff hy
      }
      have hssub: C i ⊆ A i:= by exact Eq.trans_subset hC hsub
      apply hssub
      exact hi
    · intro h1
      have hfin: ∃ a ∈ {j | x ∈ A j}, ∀ x_1 ∈ {j | x ∈ A j}, ¬x_1 < a:= by{
        obtain ⟨i, hi ⟩:= h1
        have hNe: Set.Nonempty {j  | x∈ A j}:= by{
          use i
          exact hi

        }
        specialize h {j  | x∈ A j}
        exact h hNe
      }
      obtain ⟨i, hi ⟩:= hfin
      use i
      specialize hC i
      have heg: C i= {y | y∈ A i ∧ y∈  (⋃ j, ⋃ (_ : j < i), A j)ᶜ}:= by exact hC
      rw[heg]
      simp
      constructor
      · exact hi.1
      · intro j hj
        by_contra hcon
        have huse:  ∀ x_1 ∈ {j | x ∈ A j}, ¬x_1 < i:= by exact hi.2
        specialize huse j
        exact huse hcon hj





/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h



lemma exercise4_3 : Group PosReal where
  mul := fun a b ↦ ⟨a.1*b.1,   mul_pos a.2 b.2 ⟩
  mul_assoc := by{
    intro a b c
    apply PosReal.ext
    have hh: ∀ x y z : ℝ, x*y*z= x* (y*z):= by exact fun x y z => mul_assoc x y z
    have h: a.1*b.1*c.1=a.1*(b.1*c.1):= by {
      exact hh a.1 b.1 c.1
    }
    exact h
  }
  one := ⟨1,  Real.zero_lt_one ⟩
  one_mul := by{
    intro a
    ext
    have h: ∀ x :ℝ, 1*x=x:= by exact fun x => one_mul x
    exact h a.1
  }
  mul_one := by {
    intro a
    ext
    have h: ∀ x :ℝ , x*1=x:= by exact fun x => mul_one x
    exact h a.1
  }
  inv := fun a ↦ ⟨a.1⁻¹, inv_pos.mpr a.2 ⟩
  mul_left_inv := by{
    intro a
    have h: ∀ x : ℝ, x≠ 0→  x⁻¹ *x=1:= by exact fun x a => inv_mul_cancel a
    have hh: a.1≠ 0:= by{
      have help: 0<a.1:= by exact a.2
      exact ne_of_gt help
    }
    ext
    apply h a.1
    exact hh
  }

/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
      constructor
      · intro h
        rw[Nat.prime_def_lt'] at h
        push_neg at h
        by_contra hcon
        push_neg at hcon
        by_cases h1: 2≤ n
        · have  hbet: ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n:= by exact h h1
          obtain ⟨m, hm ⟩:= hbet
          have hdiv: m ∣ n:= by exact hm.2.2
          have hex:  m*(n/m)=n:= by exact Nat.mul_div_cancel' hdiv
          have hall: ∀ (a b : ℕ),2 ≤ a → 2 ≤ b → n ≠ a * b:= by exact hcon.2.2
          specialize hall m (n/m) hm.1
          have hnm: 2≤ n/m:= by{
            by_contra hc
            have hcase: n/m=0 ∨ n/m=1:= by{
              apply le_one_iff_eq_zero_or_eq_one.mp
              exact Nat.not_lt.mp hc
            }
            obtain h2 | h3 :=hcase
            · have hh: n=0:= by exact eq_zero_of_dvd_of_div_eq_zero hdiv h2
              have hdic: 2≤ 0:= by exact Eq.trans_ge hh h1
              exact not_succ_le_zero 1 hdic
            · have hh: m=n:=by{
                exact eq_of_dvd_of_div_eq_one hdiv h3
              }
              have hdic: ¬ m=n:=by{
                have hsmal: m<n:=by exact hm.2.1
                exact Nat.ne_of_lt hsmal
              }
              exact hdic hh
          }
          specialize hall hnm
          exact hall (id hex.symm)
        · have hcase: n=0 ∨ n=1:= by {
             apply le_one_iff_eq_zero_or_eq_one.mp
             exact Nat.not_lt.mp h1
          }
          obtain h2 | h3:= hcase
          · exact hcon.1 h2
          · exact hcon.2.1 h3

      · intro h
        by_contra hcon
        obtain h1 | h2 | h3:= h
        · have hc: n ≠ 0:= by exact Nat.Prime.ne_zero hcon
          exact hc h1
        · have hc : n≠ 1:= by exact Nat.Prime.ne_one hcon
          exact hc h2
        · obtain ⟨a , b, ha, hb, hc ⟩:=h3
          have ncon: ¬ Nat.Prime (n):= by exact not_prime_mul' (id hc.symm) ha hb
          exact ncon hcon

    }


lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · have hcon: 2^0-1≠ 0:= by exact Nat.Prime.ne_zero hn
    exact hcon rfl
  · have hcon: 2^1-1≠ 1:= by exact Nat.Prime.ne_one hn
    exact hcon rfl
  have hhelp: (2 : ℤ) ^ (a * b) - 1=((2 : ℤ) ^ a) ^ b - 1:= by {
    ring
  }
  have hhhh: (1: ℤ ) ^ b = 1  := by{
    exact one_pow b
  }
  have help: (1 : ℤ) ^ b - 1=0 := by{
    rw[hhhh]
    simp
  }

  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by {
          rw[hhelp]
        }
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by{
        gcongr
        apply Int.modEq_sub
      }
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by {
        rw[help]
      }
  have h2 : 2 ^ 2 ≤ 2 ^ a := by {
    refine pow_le_pow' ?ha ha
    exact Nat.le_succ 1
  }
  have h3 : 1 ≤ 2 ^ a := by {
    exact Nat.one_le_two_pow a
  }
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by{
    apply tsub_lt_tsub_right_of_le h3
    apply pow_lt_pow
    exact Nat.one_lt_succ_succ 0
    have hhh: a< a*2 := by linarith
    have hh: a*2 ≤ a* b := by exact Nat.mul_le_mul_left a hb
    exact Nat.lt_of_lt_of_le hhh hh
  }
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by {
    apply pow_le_pow
    exact Nat.le_succ 1
    exact Nat.zero_le (a * b)
  }
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  have hhui:  ∀ m < 2 ^ (a * b) - 1, m ∣ 2 ^ (a * b) - 1 → m = 1:= by exact hn.2
  specialize hhui (2 ^ a - 1) h5 h'
  exact h4 hhui


/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
      by_contra h
      push_neg at h
      obtain ⟨c, hc' ⟩:= h.1
      obtain ⟨d, hd' ⟩:= h.2
      have hc: b=(c+a)*(c-a):= by{
        have hh: b=c*c -a^2 := by exact (tsub_eq_of_eq_add_rev (id hc'.symm)).symm
        rw[hh]
        have hhh: a^2= a*a:= by exact Nat.pow_two a
        calc c * c - a ^ 2 = c *c -a *a := by rw[hhh]
          _=(c + a) * (c - a):= by exact Nat.mul_self_sub_mul_self_eq c a
      }
      have hd: a=(d+b)*(d-b):= by{
        have hh: a=d*d -b^2 := by exact (tsub_eq_of_eq_add_rev (id hd'.symm)).symm
        rw[hh]
        have hhh: b^2= b*b:= by exact Nat.pow_two b
        calc d * d - b ^ 2 = d *d -b *b := by rw[hhh]
          _=(d + b) * (d - b):= by exact Nat.mul_self_sub_mul_self_eq d b
      }
      have hca: 0< c-a := by {
        by_contra hh
        simp at hh
        have hhh: c*c  ≤ a*a:= by {
          exact Nat.mul_le_mul hh hh
        }
        have hhhh:  a*a≤ a^2:= by {
          rw[Nat.pow_two a]
        }
        have hcon': a^2 +b≤  a^2:=by{
          calc a^2+ b= c*c:=by exact hc'
            _≤ a*a:= by exact hhh
            _≤ a^2:= by exact hhhh
        }
        have hcon: b≤ 0 := by exact (Nat.add_le_add_iff_left (a ^ 2) b 0).mp hcon'
        exact Nat.lt_le_antisymm hb hcon
      }
      have hdb: 0< d-b := by {
        by_contra hh
        simp at hh
        have hhh: d*d  ≤ b*b:= by {
          exact Nat.mul_le_mul hh hh
        }
        have hhhh:  b*b≤ b^2:= by {
          rw[Nat.pow_two b]
        }
        have hcon': b^2 +a≤  b^2:=by{
          calc b^2+ a= d*d:=by exact hd'
            _≤ b*b:= by exact hhh
            _≤ b^2:= by exact hhhh
        }
        have hcon: a≤ 0 := by exact (Nat.add_le_add_iff_left (b ^ 2) a 0).mp hcon'
        exact Nat.lt_le_antisymm ha hcon
      }
      have help: ∀ x y z: ℕ, 1≤  y →  z = x *y → z ≥  x:=by {
        intro x y z hx hz
        calc z= x *y := by exact hz
          _≥  x*1:= by exact Nat.mul_le_mul_left x hx
          _≥ x:= by linarith
      }
      have hcg: c> 0:= by {
        calc c ≥  c-a:= by exact Nat.sub_le c a
          _> 0 := by exact hca
      }
      have hdg: d>0 := by{
        calc d≥ d-b := by exact Nat.sub_le d b
          _>0:= by exact hdb
      }
      have hba: b>  a := by {
        calc b= (c + a) * (c - a):= by exact hc
          _≥  c+a := by exact help (c + a) (c - a) ((c + a) * (c - a)) hca rfl
          _> a:= by exact Nat.lt_add_of_pos_left hcg
      }
      have hab: a> b:= by{
        calc a= (d+b) *(d-b):= by exact hd
          _≥ d+b := by exact help (d + b) (d - b) ((d + b) * (d - b)) hdb rfl
          _>b := by exact Nat.lt_add_of_pos_left hdg
      }
      have hfin: ¬ a>b:=by exact Nat.lt_asymm hba
      exact hfin hab
    }
