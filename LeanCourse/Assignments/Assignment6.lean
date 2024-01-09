import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
set_option linter.unusedVariables false
noncomputable section
open BigOperators Function Set Real Filter Classical Topology
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 9 and 10, all sections

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

# You have two options for this assignment

1. Hand in the solutions to the exercises below. Deadline: 24.11.2023.
2. If you have already chosen a project, and your project doesn't require topology or analysis, you can work on your project. If you do, push a decent amount of work to your fork of the repository by 24.11. In this case you do not have to upload anything on eCampus.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/




/- Here is a technical exercise using filters,
that was useful in something I did recently. Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/
lemma exercise6_1 {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by{
  have hab : a ≠ b
  · exact haF hbF
  rw [tendsto_iff_eventually]
  constructor
  · intro h p1 h1
    apply Filter.Eventually.mono
    · exact h
    · intro i hi
      rw[hi]
      have help: ∀ᶠ (y : α) in if q then (pure a) else (pure b), p1 y:=by{
        apply Filter.Eventually.filter_mono
        have hhh: (if q then (pure a) else (pure b))≤ if q then F else G := by{
          by_cases hh:q <;> simpa[hh]
        }
        exact hhh
        exact h1
      }
      by_cases hh: q
      · simp[hh]
        simp[hh] at help
        exact help
      · simp[hh]
        simp[hh] at help
        exact help

  · intro h
    sorry
    --- I started my project
}

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` eventually means the same as
`x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
Here it lemmas are `indicator_apply` and `apply_ite` -/
lemma exercise6_2 {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ Set.indicator (s i) f) L (𝓝 (Set.indicator t f)) := by{
    rw [tendsto_pi_nhds]
    have help: ∀ x,((∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔ Tendsto (fun i ↦ if ( x ∈ s i) then (f x) else 0) L (if ( x ∈ t) then (𝓝 (f x)) else (𝓝 0))):= by{
      intro x
      have h1: pure (f x) ≤ 𝓝 (f x):= by exact pure_le_nhds_iff.mpr rfl
      apply exercise6_1
      · exact eventually_ne_nhds (ha x)
      · have hfin: {x1 | x1 ≠ f x}∈ 𝓝 0:= by{
          have hee: 0 ∈  {x1 | x1 ≠ f x}:= by {
            simp
            specialize ha x
            exact id (Ne.symm ha)
          }
          refine IsOpen.mem_nhds ?hs hee
          · exact isOpen_ne
        }
        exact hfin
      · exact h1
      · exact pure_le_nhds_iff.mpr rfl
    }
    have hellp: ∀x, (if x ∈ t then 𝓝 (f x) else 𝓝 0) =(𝓝 (if x ∈ t then f x else 0)):=by{
      exact fun x ↦ (apply_ite 𝓝 (x ∈ t) (f x) 0).symm
    }
    have hellp2: ∀ x, (fun i ↦ if x ∈ s i then f x else 0)=(fun i ↦ indicator (s i) f x):=by{
      exact fun x ↦ rfl
    }
    constructor
    · intro h x
      rw[indicator_apply]
      have help2: Tendsto (fun i ↦ if ( x ∈ s i) then (f x) else 0) L (if ( x ∈ t) then (𝓝 (f x)) else (𝓝 0)):=by{
        specialize help x
        apply help.mp
        specialize h x
        exact h
      }
      rw[hellp] at help2
      rw[hellp2] at help2
      exact help2
    · intro h x
      specialize help x
      apply help.mpr
      specialize h x
      rw[hellp]
      rw[hellp2]
      exact h
    }
section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
lemma exercise6_3 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by
  {
    by_contra h
    simp at h
    have h1: ∃ z∈ uIcc x b, f z= f a:= by {
      apply intermediate_value_uIcc
      · exact Continuous.continuousOn hf
      · rw[mem_uIcc]
        left
        constructor
        · exact LT.lt.le h
        · exact LT.lt.le h2ab
    }
    obtain ⟨z, hz ⟩:= h1
    have h2: ¬z=a := by{
      have haxb: a < min x b:= by {
        by_cases hhh: x≤ b
        · rw[min_eq_left hhh]
          have help: ¬ x = a:= by {
            by_contra h24
            have h45656: f x = f a:= by exact h2f (congrArg f (congrArg f h24))
            have heeg: ¬ f x = f a:= by exact LT.lt.ne h
            exact heeg h45656
          }
          exact Ne.lt_of_le' help hx
        · simp at hhh
          rw[min_eq_right_of_lt hhh]
          have help: ¬ b = a:= by {
            by_contra h24
            have h45656: f b = f a:= by exact h2f (congrArg f (congrArg f h24))
            have heeg: ¬ f b = f a:= by exact ne_of_gt h2ab
            exact heeg h45656
          }
          exact Ne.lt_of_le' help hab
      }
      have hsl: a < z:= by{
        have halmost: min x b ≤ z:= by {
          exact hz.1.1
        }
        exact LT.lt.trans_le haxb halmost
      }
      exact ne_of_gt hsl
    }
    have hcontra: z=a :=by {
      apply h2f
      exact hz.2
    }
    exact h2 hcontra
  }

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma exercise6_4 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b : α}
    (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by{
      rw[StrictMonoOn]
      intro c hc d hd hcd
      by_contra h
      simp at h
      have h1: f a ≤ f c:= by{
        apply exercise6_3
        · exact hf
        · exact h2f
        · exact hab
        · exact h2ab
        · exact hc
      }
      have h2: f a ≤ f d:= by{
        apply exercise6_3
        · exact hf
        · exact h2f
        · exact hab
        · exact h2ab
        · exact hd
      }
      have h3: ∃ z∈ Icc a c, f z= f d:= by{
        apply intermediate_value_Icc
        · exact hc
        · exact Continuous.continuousOn hf
        · constructor
          · exact h2
          · exact h
      }
      obtain ⟨z, hz⟩:= h3
      have h4: ¬ z= d :=by {
        have help: z< d:= by{
          calc z ≤ c:= by exact hz.1.2
            _< d := by exact hcd
        }
        exact LT.lt.ne help
      }
      have hcontra: z= d :=by {
        apply h2f
        exact hz.2
      }
      exact h4 hcontra
    }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma strictInc (f: ℝ → ℝ ) (hf : Continuous f) (h2f : Injective f)(h : f (0 :ℝ ) < f (1: ℝ )): StrictMono f:= by{
  have h3f : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := exercise6_4 (OrderDual ℝ) hf h2f hab h2ab
    convert this using 0
    exact strict_mono_on_dual_iff.symm
  have hanno: (0: ℝ )≤  (1: ℝ ):= by exact zero_le_one
  intro a b hab
  by_cases hh: (0:ℝ ) ≤ a
  · apply exercise6_4
    · exact hf
    · exact h2f
    · exact hanno
    · exact h
    · exact hh
    · have help: 0≤ b:=by{
      calc 0≤ a:= by exact hh
        _≤ b:= by exact LT.lt.le hab
      }
      exact help
    · exact hab
  · simp at hh
    by_cases hhh: b ≤ 1
    · apply h3f
      · exact hanno
      · exact h
      · have help: a≤ 1:=by {
        calc a ≤  0 := by exact LT.lt.le hh
          _≤ 1:= by exact hanno
        }
        exact help
      · exact hhh
      · exact hab
    · simp at hhh
      have help1: f a < f 0:= by {
        apply h3f
        · exact hanno
        · exact h
        · have help: a≤ 1:=by {
          calc a ≤  0 := by exact LT.lt.le hh
            _≤ 1:= by exact hanno
          }
          exact help
        · exact hanno
        · exact hh
      }
      have help2: f 1 < f b:= by {
        apply exercise6_4
        · exact hf
        · exact h2f
        · exact hanno
        · exact h
        · exact hanno
        · have help: 0≤ b:=by{
            calc 0≤ 1:= by exact hanno
            _≤ b:= by exact LT.lt.le hhh
          }
          exact help
        · exact hhh
      }
      calc f a < f 0:= by exact help1
        _< f 1:= by exact h
        _< f b:= by exact help2
}


lemma exercise6_5 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by{

  by_cases h: f (0 :ℝ ) < f (1: ℝ )
  · left
    apply strictInc
    · exact hf
    · exact h2f
    · exact h
  · simp at h
    have hcase: f 1 < f 0 ∨ f 1 = f 0:= by exact LE.le.lt_or_eq h
    obtain h1 | h2:= hcase
    · right
      have href: StrictMono (fun x↦ (-1)* f x) → StrictAnti f :=by {
        intro hh a b hab
        specialize hh hab
        simp at hh
        exact hh
      }
      apply href
      apply strictInc
      · refine Continuous.comp' ?_ hf
        · exact continuous_mul_left (-1)
      · intro a1 a2 h12
        simp at h12
        apply h2f
        exact h12
      · simp
        exact h1
    · have h43: ¬ (1: ℝ) =(0: ℝ ):= by exact one_ne_zero
      exact (h43 (h2f (h2f (congrArg f h2)))).elim

  }


/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/



lemma exercise6_6 : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by{
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0:= by{
    have h5: HasDerivWithinAt (fun x : ℝ ↦ x) 1 (Ici 0) 0:= by {
      refine HasDerivWithinAt.Ici_of_Ioi ?_
      refine hasDerivWithinAt_iff_isLittleO.mpr ?_
      simp
    }
    apply HasDerivWithinAt.congr
    apply h5
    intro x hx
    exact abs_eq_self.mpr hx
    simp
  }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0:= by{
    have h5: HasDerivWithinAt (fun x : ℝ ↦ -x) (-1) (Iic 0) 0:= by {
      refine HasDerivWithinAt.Iic_of_Iio ?_
      refine hasDerivWithinAt_iff_isLittleO.mpr ?_
      simp
    }
    apply HasDerivWithinAt.congr
    apply h5
    intro x hx
    exact abs_of_nonpos hx
    simp

  }

  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by{
    have hh: Convex ℝ (Ici (0:ℝ )):= by exact convex_Ici 0
    have hhh:  Set.Nonempty (interior (Ici (0:ℝ ))):= by{
      have hhhh: (1:ℝ )∈ interior (Ici 0):= by {
        refine mem_interior.mpr ?_
        use Ioi 0
        constructor
        · exact Ioi_subset_Ici_self
        · constructor
          · exact isOpen_Ioi
          · refine mem_Ioi.mpr ?h.right.right.a
            exact Real.zero_lt_one
      }
      exact Set.nonempty_of_mem hhhh
    }
    have hhhh:  0 ∈ closure (Ici (0:ℝ )):= by{
      refine Real.mem_closure_iff.mpr ?_
      · intro e he
        use 0
        constructor
        · exact right_mem_Iic
        · simp
          exact he
    }
    exact uniqueDiffWithinAt_convex hh hhh hhhh

  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by{
    have hh: Convex ℝ (Iic (0:ℝ) ):= by exact convex_Iic 0
    have hhh: Set.Nonempty (interior (Iic (0:ℝ ))):= by{
      have hhhh: ((-1):ℝ )∈ (interior (Iic (0:ℝ ))):=by{
        refine mem_interior.mpr ?_
        use Iio 0
        constructor
        · exact Iio_subset_Iic_self
        · constructor
          · exact isOpen_Iio
          · have hhhhh: ((-1):ℝ )< (0: ℝ ):= by exact neg_one_lt_zero
            exact hhhhh
      }
      exact Set.nonempty_of_mem hhhh
    }
    have hhhh: 0 ∈ closure (Iic (0:ℝ )):= by{
      refine Real.mem_closure_iff.mpr ?_
      intro e he
      use 0
      constructor
      · exact right_mem_Iic
      · simp
        exact he
    }
    exact uniqueDiffWithinAt_convex hh hhh hhhh
  }
  have h5: deriv (fun x :ℝ ↦ |x|) 0=1 := by{
    calc deriv (fun x :ℝ ↦ |x|) 0= derivWithin (fun x :ℝ ↦ |x|) (Ici (0:ℝ) ) 0:=by exact
      (DifferentiableAt.derivWithin h h3).symm
      _= 1:=by exact HasDerivWithinAt.derivWithin h1 h3
  }
  have h6: deriv (fun x :ℝ ↦ |x|) 0=-1:= by{
      calc deriv (fun x :ℝ ↦ |x|) 0= derivWithin (fun x :ℝ ↦ |x|) (Iic (0:ℝ) ) 0:=by exact
        (DifferentiableAt.derivWithin h h4).symm
        _=-1 := by exact HasDerivWithinAt.derivWithin h2 h4
  }
  have hcont: ¬ deriv (fun x :ℝ ↦ |x|) 0=1 := by{
    rw[h6]
    simp
  }
  exact hcont h5
}
