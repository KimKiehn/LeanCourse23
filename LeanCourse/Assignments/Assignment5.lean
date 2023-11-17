import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun := fun (m1, m2) ↦ (f m1)+(g m2)
  map_add' := by{
    intro (m1, m2) (n1, n2)
    simp
    exact add_add_add_comm (f.toFun m1) (f.toFun n1) (g.toFun m2) (g.toFun n2)

  }
  map_smul' := by simp


example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := by rfl -- should be rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

lemma ProdIsUnit (x y : {x : R // IsAUnit x}): IsAUnit (x.1*y.1):= by {
  obtain ⟨x1, hx1 ⟩:= x.2
  obtain ⟨y1, hy1 ⟩:= y.2
  use y1*x1
  rw[mul_assoc, ← mul_assoc x1, hx1, one_mul,hy1]
}

lemma IsUnitOne: IsAUnit (1: R):= by{
  use 1
  exact one_mul 1
}

def INV (x: {x:R // IsAUnit x}): {x: R // IsAUnit x}:= ⟨Exists.choose x.2, by{
  use x
  rw[mul_comm, Exists.choose_spec x.2]

} ⟩

lemma MULINV (x : {x : R // IsAUnit x}): (INV x).1* x.1=1:=by{
  rw[INV, Exists.choose_spec x.2]
}



instance exercise5_2 : Group {x : R // IsAUnit x} where
  mul := fun a b ↦ ⟨ a.1*b.1 , ProdIsUnit a b⟩
  mul_assoc := by{
    intro a b c
    ext
    push_cast
    have hh:  ∀ x y z : R, x*y*z= x* (y*z):= by exact fun x y z ↦ mul_assoc x y z
    exact hh ↑a ↑b ↑c
  }
  one := ⟨1, IsUnitOne ⟩
  one_mul := by {
    intro a
    ext
    have hh: ∀ x :R, 1*x=x:= by exact fun x ↦ one_mul x
    exact hh ↑a
  }
  mul_one := by {
    intro a
    ext
    have hh: ∀ x: R, x*1=x:= by exact fun x ↦ mul_one x
    exact hh ↑a
  }
  inv := fun x ↦ INV x
  mul_left_inv := by {
    intro a
    ext
    apply MULINV
  }

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by rfl

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by {
    intro i hi
    simp at hi
    refine Prime.dvd_choose_self h2 ?hk ?hkp
    · linarith
    · linarith
  }
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by {
      have h7: ∀ i ∈  Ioo 0 p, (Nat.choose p i: K) = (0:K):= by{
        intro i hi
        rw[CharP.cast_eq_zero_iff K p]
        specialize h5 i hi
        exact h5
      }
      apply Finset.sum_congr
      · rfl
      · intro i hi
        specialize h7 i hi
        rw[h7]
    }
    _ = 0 := by simp
  rw[sum_range_succ]
  rw[h4]
  rw[Finset.sum_insert left_not_mem_Ioo]
  rw[h6]
  simp
  exact add_comm (y ^ p) (x ^ p)


/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by{
      have help: ∃ m :M, m ≠ (0:M):=by{
        exact exists_ne 0
      }
      obtain ⟨m,hm ⟩:= help
      have hh:   ∀ f : M  →ₗ[R] M, ∀ x: R,  (x • f) m=(0: M)→ x=(0:R) ∨  f m=(0:M):= by{
          intro f x hxf
          rw[h] at hxf
          exact smul_eq_zero.mp hxf
      }
      let id: (M →ₗ[R] M):= LinearMap.id
      have hlin:  ∀ x y :R, ∀ n :M, (x*y)• n= x •(y • n) := by {
        exact fun x y n ↦ mul_smul x y n
      }
      have hllin: ∀ f : M  →ₗ[R] M, ∀ x: R, x• (f m)= f (x • m):=by exact fun f x ↦
        (LinearMap.map_smul f x m).symm
      have hhi: ((r*s-s*r)• id) m=(0:M) := by {
        calc ((r*s-s*r)• id ) m= (r*s-s*r)• (id m):= by exact h (r * s - s * r) id m
          _=(r*s)• (id m)- (s*r)• (id m):= by exact sub_smul (r * s) (s * r) (id m)
          _=r•(s • (id ( m)))-(s*r)• (id m):= by {
            specialize hlin r s (id m)
            rw[hlin]
          }
          _=r • (id (s• m))-(s*r)• (id m):= by exact rfl
          _= (r• id) ( s•m) -(s*r)• (id m):= by {
            specialize h r id (s• m)
            rw[h]
          }
          _= s• (r• id) m -(s*r)• (id m):= by {
            specialize hllin (r• id) s
            rw[hllin]
          }
          _= s• (r)• (id m) -(s*r)• (id m):= by {
            exact
              congrFun (congrArg HSub.hSub (congrArg (HSMul.hSMul s) (h r id m))) ((s * r) • id m)
          }
          _= (s*r) • (id m) -(s*r)• (id m):= by {
            specialize hlin s r (id m)
            rw[hlin]
          }
          _= 0:= by exact sub_self ((s * r) • id m)
      }
      specialize hh id (r*s-s*r) hhi
      obtain h1 | h2:= hh
      · symm
        calc s*r = s*r + 0:= by exact self_eq_add_right.mpr rfl
          _= s*r + (r*s - s*r) := by rw[h1]
          _= r*s := by exact add_sub_cancel'_right (s * r) (r * s)
      · simp at h2
        contradiction
    }
