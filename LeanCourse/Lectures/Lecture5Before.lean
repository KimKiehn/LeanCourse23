import LeanCourse.Common
open Real Function
noncomputable section
set_option linter.unusedVariables false


/- # Last Lecture -/

/-
We went over the quantifiers `∀` (for all) and `∃` (exists), and the connectives
`∧` (and), `∨` (or), `→` (implies), `↔` (if and only if).
For each of these we saw how to prove them, and how to use an assumption that states this.
-/







/- # Today: Logic (continued) and sets

We cover sections 3.3, 3.6 and 4.1 from Mathematics in Lean. -/

/-
We will discuss negation `¬` (not), classical logic, sequences and sets.
-/


/- ## Negation

The negation `¬ A` just means `A → False`, where `False` is a specific false statement.
We can use the same tactics as for implication:
`intro` to prove a negation, and `apply` to use one. -/

example {p : Prop} (h : p) : ¬ ¬ p := by {
  intro h1
  exact h1 h
}

example {α : Type*} {p : α → Prop} : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by {
  constructor
  · intro h x hx
    apply h
    exact ⟨x,hx ⟩
  · intro h h1
    obtain ⟨x, hx ⟩:=h1
    specialize h x hx
    exact h
}

/- We can use `exfalso` to use the fact that everything follows from `False`:
ex falso quod libet -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by {
  intro h1
  specialize h h1
  exfalso
  exact h
}

/- `contradiction` proves any goal when two hypotheses are contradictory. -/

example {p : Prop} (h : ¬ p) : p → 0 = 1 := by {
  intro h1
  contradiction
}






/-
We can use classical reasoning (with the law of the excluded middle) using the following tactics.

* `by_contra h` start a proof by contradiction.
* `by_cases h : p` to start a proof by cases on statement `p`.
* `push_neg` to push negations inside quantifiers and connectives.
-/

example {p : Prop} (h : ¬ ¬ p) : p := by {
  by_contra h1
  exact h h1
}

example (p q : Prop) (h : ¬ q → ¬ p) : p → q := by {
  intro hp
  by_contra h1

  exact h h1 hp
}

example (p q r : Prop) (h1 : p → r) (h2 : ¬ p → r) : r := by {
  by_cases hp: p
  · exact h1 hp
  · exact h2 hp
}

example {α : Type*} {p : α → Prop} : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by {
  push_neg
  rfl
}



/-- The sequence `u` of real numbers converges to `l`.
`∀ ε > 0, ...` means `∀ ε, ε > 0 → ...` -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (u : ℕ → ℝ) (l : ℝ) :
    ¬ SequentialLimit u l ↔ ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| ≥ ε := by {
      rw[SequentialLimit]
      push_neg
      rfl
    }

lemma sequentialLimit_unique (u : ℕ → ℝ) (l l' : ℝ) :
    SequentialLimit u l → SequentialLimit u l' → l = l' := by {
      intro h1 h2
      by_contra h3
      have h4 :|l - l'| > 0
      · apply abs_pos.2
        apply sub_ne_zero.2
        exact h3

      rw[SequentialLimit] at h1 h2
      specialize h1 (|l-l'|/2) (by linarith)
      obtain ⟨N,hN ⟩:=h1
      obtain ⟨N', hN' ⟩:= h2  (|l-l'|/2) (by linarith)
      let N₀ := max N N'
      specialize hN N₀ (by exact Nat.le_max_left N N')
      specialize hN' N₀ (by exact Nat.le_max_right N N')
      have : |l-l'| < |l-l'|:= by
        calc |l-l'|
          =|l-u N₀ +(u N₀ -l')|:= by ring
         _≤ |l- u N₀| +|u N₀ -l'| := by exact abs_add (l - u N₀) (u N₀ - l')
         _= |u N₀ -l| + |u N₀ -l'|:= by rw [@abs_sub_comm]
         _< |l-l'|:= by linarith
      linarith
    }


/- ## Exercises -/


/- Prove the following without using `push_neg` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  constructor
  · intro h1 h2
    obtain ⟨x, hx ⟩:= h1
    specialize h2 x
    exact h2 hx
  · intro h1
    by_contra h2
    apply h1
    intro x
    by_contra h4
    apply h2
    use x
}

lemma convergesTo_const (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  rw[SequentialLimit]
  intro ε h1
  use 0
  simp
  exact h1
}

/- The next exercise is harder, and you will probably not finish it during class. -/
lemma SequentialLimit.add {s t : ℕ → ℝ} {a b : ℝ}
    (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
      intro ε h1
      have h2: (ε/2)>0 := by exact half_pos h1
      obtain ⟨N1, hN1 ⟩:= hs (ε/2) h2
      obtain ⟨N2, hN2 ⟩:= ht (ε/2) h2
      let N := max N1 N2
      use N
      intro n hn
      specialize hN1 n (by apply le_trans (Nat.le_max_left N1 N2) hn)
      specialize hN2 n (by apply le_trans (Nat.le_max_right N1 N2) hn)
      simp
      calc |s n +t n -(a+b)|= |(s n -a)+ (t n -b)|:= by ring
        _≤ |s n -a|+|t n -b|:= by exact abs_add (s n - a) (t n - b)
        _<  ε:=by linarith
    }







/- # Sets

In set theory you can make sets with arbitrary elements.
In Lean, all sets have to be sets of elements from a specific type.
-/

#check Set ℕ
#check Set ℝ

variable {α β ι : Type*} (x : α) (s t u : Set α)

#check x ∈ s       -- \in or \mem
#check x ∉ s       -- \notin
#check s ⊆ t       -- \sub
#check s ⊂ t       -- \ssub


#check s ∩ t       -- \inter or \cap
#check s ∪ t       -- \union or \cup
#check s \ t       -- it is the normal symbol `\` on your keyboard,
                   -- but you have to write `\\` or `\ ` to enter it
#check sᶜ          -- \compl or \^c
#check (∅ : Set α) -- \empty
#check (Set.univ : Set α)

open Set

#check (univ : Set α)






/- Showing that `x` is an elements of `s ∩ t`, `s ∪ t` or `sᶜ`
corresponds by definition to conjunction, disjunction or negation. -/

#check mem_inter_iff
#check mem_union
#check mem_compl_iff

/- There are various ways to prove this:
* use lemma `mem_inter_iff`
* use `simp`
* directly apply `constructor`
* give a direct proof: `⟨xs, xt⟩`
-/
example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by {

  exact ⟨hxs, hxt ⟩
}


example (hxs : x ∈ s) : x ∈ s ∪ t := by  {
  simp [hxs]
}









/- `s ⊆ t` means that for every element `x` in `s`, `x` is also an element in `t`. -/

#check subset_def

example : s ∩ t ⊆ s ∩ (t ∪ u) := by {
  intro x hx
  constructor
  · exact mem_of_mem_inter_left hx
  · left
    exact hx.2

}

/- you can also prove it at thge level of sets, without talking about elements. -/
example : s ∩ t ⊆ s ∩ (t ∪ u) := by {
  gcongr
  exact subset_union_left t u
}





/- ## Proving two Sets are equal

You can prove that two sets are equal by applying `subset_antisymm` or using the `ext` tactic.
-/
#check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)

example : s ∩ t = t ∩ s := by  {
  ext x
  constructor
  · intro hx
    exact ⟨ hx.2, hx.1⟩
  · intro hx
    obtain ⟨h1x, h2x⟩:= hx
    constructor
    · exact h2x
    · exact h1x
}

/- We can also use existing lemmas and `calc`. -/
example : (s ∪ tᶜ) ∩ t = s ∩ t := by sorry





/-
# Set-builder notation
-/

def Evens : Set ℕ := {n : ℕ | Even n}

def Odds : Set ℕ := {n | ¬ Even n}

example : Evens ∪ Odds = univ := by sorry





example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : sᶜ = {x | x ∉ s} := by rfl
example : (∅ : Set α) = {x | False} := by rfl
example : (univ : Set α) = {x | True} := by rfl

-- alternative notation:
example : s ∩ t = {x ∈ s | x ∈ t} := by rfl


/-
# Other operations on sets
-/

/- We can take power sets of sets. -/
example (s : Set α) : 𝒫 s = {t | t ⊆ s} := by rfl -- \powerset







/- We can take unions and intersections of families of sets in three different ways:
* Given a family of sets `C : ι → Set α`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements of `ι`.
-/
example (C : ι → Set α) : ⋃ i : ι, C i = {x : α | ∃ i : ι, x ∈ C i} := by ext; simp

example (C : ι → Set α) : ⋂ i : ι, C i = {x : α | ∀ i : ι, x ∈ C i} := by ext; simp

/-
* Given a family of sets `C : ι → Set α` and `s : Set ι`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements in `s`.
-/
example (s : Set ι) (C : ι → Set α) : ⋃ i ∈ s, C i = {x : α | ∃ i ∈ s, x ∈ C i} := by ext; simp

example (s : Set ι) (C : ι → Set α) : ⋂ i ∈ s, C i = {x : α | ∀ i ∈ s, x ∈ C i} := by ext; simp

/-
* Given a collection of sets `C : Set (Set α)`
  we can take the union and intersection of `c`
  for all `c ∈ C`
-/

example (𝓒 : Set (Set α)) : ⋃₀ 𝓒 = {x : α | ∃ s ∈ 𝓒, x ∈ s} := by rfl

example (𝓒 : Set (Set α)) : ⋂₀ 𝓒 = {x : α | ∀ s ∈ 𝓒, x ∈ s} := by rfl



example (C : ι → Set α) (s : Set α) : s ∩ (⋃ i, C i) = ⋃ i, (C i ∩ s) := by sorry


/- We can take images and preimages of sets.

`f ⁻¹' s` is the preimage of `s` under `f`.
`f '' s` is the image of `s` under `f`. -/

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl

example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl


example {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by sorry
