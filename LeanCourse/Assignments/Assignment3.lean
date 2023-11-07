import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra h1
  have h2: ¬ p ∧ ¬ ¬ p := by  {
    constructor
    · by_contra h3
      have h: p ∨ ¬ p:= by {
        left
        exact h3
      }
      exact h1 h
    · by_contra h3
      have h: p ∨ ¬ p:= by {
        right
        exact h3
      }
      exact h1 h
  }
  exact h2.2 h2.1

}






/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
      intro ε he
      specialize hs ε
      obtain ⟨N, hN ⟩:= hs he
      specialize hr N
      obtain ⟨N1, hN1 ⟩:= hr
      use N1
      intro n hn
      simp
      specialize hN1 n hn
      specialize hN  (r n) hN1
      exact hN
    }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
      intro ε he
      specialize hs₁ ε he
      specialize hs₃ ε he
      obtain ⟨N1, hN1 ⟩:= hs₁
      obtain ⟨N2, hN2⟩:= hs₃
      use max N1 N2
      intro n hn'
      have hn: n≥ N1 ∧ n≥ N2 := by exact (useful_fact N1 N2 n).mp hn'
      specialize hN1 n hn.1
      specialize hN2 n hn.2
      rw[abs_sub_lt_iff]
      constructor
      · calc s₂ n -a ≤ s₃ n -a := by exact sub_le_sub_right (hs₂s₃ n) a
        _<ε := by exact lt_of_abs_lt hN2
      · have h21: |a- s₁ n| < ε := by {
          calc |a- s₁ n|= |s₁ n -a|:= by exact abs_sub_comm a (s₁ n)
            _< ε := by exact hN1
        }
        have h42: a- s₁ n < ε := by exact lt_of_abs_lt h21
        calc a- s₂ n≤ a -s₁ n:= by exact sub_le_sub_left (hs₁s₂ n) a
          _<ε := by exact h42
    }


/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)



lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by {
  intro ε he
  use ⌈(1/ε)⌉₊
  intro n hn
  simp
  have h1: 1/ε  ≤ (n : ℝ  )  := by {
    calc 1/ε ≤ (⌈(1/ε)⌉₊ : ℝ):= by exact le_ceil (1 / ε)
    _≤ (n : ℝ  ):= by exact cast_le.mpr hn

  }
  have h2: 1/ε +1 ≤ (n +1 : ℝ ):= by {
    calc 1/ε +1 ≤ (n : ℝ )+1:=by exact add_le_add_right h1 1
      _=(n +1 : ℝ ):= by exact rfl
    }
  have he': 0<(1/ε)+1:= by {
    have h: 0<(1/ε ):= by exact one_div_pos.mpr he
    calc 0 < 1 := by exact Real.zero_lt_one
      _< (1/ε)+1:= by exact lt_add_of_pos_left 1 h
  }
  have he75: 0<1/ε := by exact one_div_pos.mpr he
  have htriv: ((1/ε)+1)⁻¹<(1/ε)⁻¹:=by{
    have hsdv: 1/ε < 1/ε +1:= by exact lt_add_one (1 / ε)
    exact (inv_lt_inv he' he75).mpr hsdv
  }
  have hn': 0<((n + 1 :ℝ) )⁻¹:= by exact inv_pos_of_nat
  calc |((n + 1 :ℝ) )⁻¹|=((n + 1 :ℝ) )⁻¹:= by exact abs_of_pos hn'
    _≤ ((1/ε)+1)⁻¹:= by exact inv_le_inv_of_le he' h2
    _< (1/ε)⁻¹:= by exact htriv
    _= ε:= by simp
}


/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by {

  apply exercise3_3
  · exact use_me
  · exact exercise3_4
  · intro n
    have h: -1≤ sin n:= by exact neg_one_le_sin ↑n
    refine (div_le_div_right ?hs₁s₂.hc).mpr h
    exact cast_add_one_pos n
  · intro n
    have h: sin n≤ 1:= by exact sin_le_one ↑n
    refine (div_le_div_right ?hs₂s₃.hc).mpr h
    exact cast_add_one_pos n
}

/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by {
      intro n
      by_contra hc
      have hn': u n >l:= by exact not_le.mp hc
      have hn: 0< u n -l:= by exact sub_pos.mpr hn'
      specialize h1 (u n -l) hn
      obtain ⟨N , hN⟩:= h1
      have hNN: max N n≥ N:= by exact Nat.le_max_left N n
      specialize hN (max N n) (hNN)
      have hNn: max N n≥ n:= by exact Nat.le_max_right N n
      specialize h2 n (max N n) hNn
      have h436: u (max N n)> l:=by{
        calc u (max N n)≥  u n := by exact h2
          _> l := by exact hn'
      }
      have hjpijhio: u (max N n)-l>0:= by exact sub_pos.mpr h436
      have h2135: u (max N n)-l < u n -l := by{
        calc u (max N n)- l= |u (max N n)- l|:= by exact (abs_of_pos hjpijhio).symm
          _< u n  -l:= by exact hN
      }
      have hofiho: u (max N n) < u n:= by exact (add_lt_add_iff_right (-l)).mp h2135
      have hcontra: u n <  u n :=by {
        calc u n≤ u (max N n):= by exact h2
          _< u n := by exact hofiho
      }
      exact LT.lt.false hcontra
    }


/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
      ext x
      constructor
      · intro h1
        simp
        obtain ⟨him, ht ⟩:=h1
        obtain⟨x1, hx1 ⟩:= him
        use x1
        constructor
        · constructor
          · exact hx1.1
          · simp only [hx1.2]
            exact ht
        · exact hx1.2
      · simp
        intro x1 hx1 hfx hfxx
        constructor
        · use x1
        · exact mem_of_eq_of_mem (id hfxx.symm) hfx
    }


lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by {
      ext x
      constructor
      · intro h1
        have h356: x^2 ∈ {y | y≥ 4}:= by exact h1
        have hx: x^2≥ 4:= by exact h356
        simp
        by_contra h2
        have h3: ¬ x≤ -2 ∧ ¬ 2≤x:= by exact not_or.mp h2
        have h4: x>-2 ∧ 2> x:= by {
          obtain ⟨h11,h12⟩:= h3
          constructor
          · exact not_le.mp h11
          · exact not_le.mp h12
        }
        have h5: |x|<2:=by exact abs_lt.mpr h4
        have h6: |x|^2≥ 4:= by{
          calc |x|^2=x^2:= by exact sq_abs x
            _≥4:= by exact hx
        }
        by_cases h235ut: x=0
        · have hluthe: ¬ |x|^2<4:= by exact not_lt.mpr h6
          apply hluthe
          simp
          calc x^2 = 0 := by exact sq_eq_zero_iff.mpr h235ut
            _<4:= by exact four_pos
        · have hfsghg: |x| > 0 := by exact abs_pos.mpr h235ut
          have hsrdfmfdshhmgf: 0<2:= by exact succ_pos 1
          have hsk: |x| ^ 2 < 2 *|x|:= by{
            calc |x| ^ 2 = |x| * |x|:= by exact sq |x|
            _< 2 *|x|:= by exact (mul_lt_mul_right hfsghg).mpr h5
          }
          have ht: 2 * |x| < 4:= by {
            linarith
          }
          have hre: |x| ^ 2 < 4 := by exact gt_trans ht hsk
          have h457w5: ¬ |x| ^ 2 < 4 := by exact not_lt.mpr h6
          exact h457w5 hre
      · intro h1
        simp
        simp at h1
        obtain herz | hzuz := h1
        · have h43: -x ≥ 2 := by exact le_neg.mpr herz
          have h45ze5z: (-x)*(-x)≥ 2*2:= by{
             refine _root_.mul_self_le_mul_self ?ha h43
             exact zero_le_two
          }
          calc x ^ 2= (-x)*(-x):= by ring
            _≥ 2*2 := by exact h45ze5z
            _= 4:= by ring
        · have hwe: x * x ≥ 2*2:= by {
            refine _root_.mul_self_le_mul_self ?ha hzuz
          }
          calc x ^2 = x *x := by ring
            _≥ 2 * 2:= by exact hwe
            _= 4 := by ring
    }

/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ f '' s ∪ g '' t
  let R : Set γ → Set α × Set β :=
    fun s ↦ (f ⁻¹' s, g ⁻¹' s)
  use L , R
  constructor
  · ext x y
    simp
    constructor
    · intro h
      obtain h' | h'' := h
      · obtain ⟨x1, hx1 ⟩ := h'
        obtain ⟨hx11, hx12 ⟩:= hx1
        rw [← hx12]
        exact hx11
      · obtain ⟨x1, hx1 ⟩:= h''
        obtain ⟨hx11, hx12 ⟩:= hx1
        rw [← hx12]
        exact hx11
    · intro h
      specialize h2' y
      simp at h2'
      obtain hy1 | hy2 := h2'
      · left
        obtain ⟨z, hz ⟩:= hy1
        use z
        constructor
        · exact mem_of_eq_of_mem hz h
        · exact hz
      · right
        obtain ⟨z, hz ⟩:= hy2
        use z
        constructor
        · exact mem_of_eq_of_mem hz h
        · exact hz
  · ext x y
    simp
    constructor
    · intro h123
      obtain h132 | h45 := h123
      · obtain ⟨x1, hx1 ⟩:= h132
        obtain ⟨hx11, hx12 ⟩:= hx1
        specialize hf' x1 y
        have h3rh: x1=y := by exact hf hx12
        exact mem_of_eq_of_mem (hf (id hx12.symm)) hx11
      · obtain ⟨x1, hx1 ⟩:= h45
        obtain ⟨hx11, hx12 ⟩:= hx1
        exact (h1' y x1 (id hx12.symm)).elim
    · intro h42
      left
      use y
    · constructor
      · intro h23
        simp
        simp at h23
        obtain h231 | h232 := h23
        · obtain ⟨x2 , hx2 ⟩:= h231
          obtain ⟨hx21, hx22 ⟩:= hx2
          exact (h1' x2 y hx22).elim
        · obtain ⟨x2 , hx2 ⟩:= h232
          obtain ⟨hx21, hx22 ⟩:= hx2
          exact mem_of_eq_of_mem (hg (id hx22.symm)) hx21
      · intro h69
        simp
        simp at h69
        right
        use y
