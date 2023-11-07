import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/

lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by{
      constructor
      · intro h1
        obtain⟨x,hx⟩:=h1
        obtain hP|hQ := hx
        left
        · use x
        right
        · use x
      · intro h1
        obtain hP|hQ :=h1
        · obtain ⟨x, hx⟩:= hP
          use x
          left
          exact hx
        · obtain⟨x, hx ⟩:= hQ
          use x
          right
          exact hx
    }


section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  {
    intro y

    obtain ⟨x, hx⟩:= h y
    use f x
    exact hx
  }

/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  {
    constructor
    · apply exercise2_2
    · intro h1 z
      obtain⟨y,hy⟩:= h1 z
      obtain ⟨x, hx⟩:= hf y
      use x
      simp
      calc g ( f x)= g y:= by rw[hx]
        _= z := by rw[hy]
  }

/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  {
    intro y
    obtain ⟨x, hx⟩:= hf ((y-1)/2)
    use x/3-4
    ring
    rw[hx]
    ring
  }

end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  {
    intro k
    use k
    simp
    intro n hn
    gcongr
  }

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

#check add_le_add

lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  {
    intro k
    have h1: ∃ N, ∀ n≥ N, k* t₁ n≤ s₁ n := by exact h₁ k
    have h2: ∃ N, ∀ n≥ N, k* t₂ n≤ s₂ n := by exact h₂ k
    obtain ⟨N1, hN1 ⟩:= h1
    obtain ⟨N2, hN2 ⟩:= h2
    use max N1 N2
    intro n
    rw[useful_fact]
    intro hN
    obtain ⟨h3,h4 ⟩:=  hN
    have h5: k*t₁ n≤ s₁ n:= by exact hN1 n h3
    have h6: k*t₂ n≤ s₂ n:= by exact hN2 n h4
    simp
    linarith
  }


/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  {
    let s (n: ℕ ) := (n+1)^n
    use s
    constructor
    · intro k
      use k
      simp
      intro n hn
      have hk: k≥  0:=by exact Nat.zero_le k
      have h2: k≤ n+1+1:= by {
        calc k≤n:= by exact hn
          _≤ n+1:= by exact Nat.le_add_right n 1
          _≤ n+1+1:= by exact Nat.le_add_right (n+1) 1
      }
      have h: (n+1)^n≤ (n+1+1)^n:= by {
        gcongr
        exact Nat.le_add_right n 1
      }
      have h1: k*(n+1)^n≤ k*(n+1+1)^n:=by exact Nat.mul_le_mul_left k h
      have h3: k*(n+1+1)^n≤ (n+1+1)*(n+1+1)^n:=by exact Nat.mul_le_mul_right ((n + 1 + 1) ^ n) h2
      have h4: (n+1+1)*(n+1+1)^n=(n+1+1)^(n+1):= by exact Nat.pow_succ'.symm
      apply le_trans h1
      apply le_trans h3
      exact Nat.le_of_eq h4
    · intro n
      exact NeZero.ne (s n)
  }


/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact?
  · have : 1 ≤ n := by exact?
    exact?

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by{
  intro k
  simp
  have h1: ∃ N, ∀ n≥ N, k* s (n) ≤ s (n+1) := by exact hs k
  obtain⟨N, hN⟩:=h1
  use N+1
  intro n hn
  have hh: ∃ l ≥ N, l + 1 = n:= by exact useful_fact2  hn
  obtain ⟨l, hl⟩:= hh
  obtain⟨ hgeq, heq⟩:=hl
  have h3s :  1 ≤ s l := by

    exact one_le_iff_ne_zero.mpr (h2s l)
  have h7: k*1≤ k*s (l):= by exact Nat.mul_le_mul_left k h3s

  have h8: k≤ s (l+1):= by{
    specialize hN l hgeq
    exact le_of_mul_le_of_one_le_left hN h3s
  }
  exact Eq.trans_ge (congrArg s heq) h8
  }
end Growth