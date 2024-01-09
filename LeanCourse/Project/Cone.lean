import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sober
import LeanCourse.Project.SpectralSpaces
import Mathlib.Algebra.Order.Ring.Cone
universe u v

variable {R : Type u}{S: Type v} [CommRing R][CommRing S]
variable {α: Type u}
variable [TopologicalSpace α] {X: Set α}

open Ring
open Topology
open Function Set Order
@[ext]
structure Cone (R: Type u) [CommRing R] where
  nonneg : Set R
  add_nonneg : ∀ {a b}, a∈ nonneg  → b ∈ nonneg  →(a + b)∈  nonneg
  mul_nonneg : ∀ {a b},a ∈  nonneg  → b∈ nonneg  → (a * b)∈ nonneg
  square_nonneg: ∀ a, (a*a)∈ nonneg



lemma Cone.zero (C:Cone R): 0∈ C.nonneg:=by{
  have: (0:R)=  0*0:= by exact (zero_mul 0).symm
  rw[this]
  exact square_nonneg C 0
}

lemma Cone.one (C:Cone R): 1∈ C.nonneg:=by{
  have: (1:R)=  1*1:= by exact (one_mul 1).symm
  rw[this]
  exact square_nonneg C 1
}

class Cone.IsProper (C: Cone R): Prop where
  proper :  (-1: R) ∉   C.nonneg

class Cone.IsPrime (P : Cone R) : Prop where

  proper : ((-1 : R)∉ P.nonneg )

  mem_or_mem' : ∀ {x y : R},(x * y)∈  P.nonneg   →(x ∈ P.nonneg  ) ∨ ((-y) ∈ P.nonneg  )

lemma Cone.prime_mem_r_or_mr (P: Cone R) (r: R) (hP: IsPrime P):
  r∈ P.nonneg ∨ -r∈ P.nonneg:=by{
  apply hP.2
  exact square_nonneg P r
}

class Cone.IsMaximal (M: Cone R): Prop where
  proper:  ((-1 : R)∉ M.nonneg )
  maximal: ∀ C: Cone R, Cone.IsProper C→ (M.nonneg  ⊆  C.nonneg )→ M.nonneg=C.nonneg



def Cone.comap (f : R →+* S) (P : Cone S): Cone R where
  nonneg := {r: R| f r ∈ P.nonneg}
  add_nonneg := by{
    intro a b ha hb
    simp
    apply P.add_nonneg
    · exact ha
    · exact hb
  }
  mul_nonneg := by{
    intro a b ha hb
    simp
    apply P.mul_nonneg
    · exact ha
    · exact hb
  }
  square_nonneg :=by{
    intro a
    simp
    exact square_nonneg P (f a)
  }

lemma Cone.comap_isPrime (f : R →+* S) (P: Cone S) (hP: Cone.IsPrime P): Cone.IsPrime (Cone.comap f P):= by{
  constructor
  · by_contra h
    have hcontra: Cone.nonneg P ( f (-1)):=by exact h
    have : f (-1)= -1:= by simp
    rw[this] at hcontra
    exact hP.1 hcontra


  · intro x y h
    have help: P.nonneg ( f x * f y)  →(P.nonneg (f x) ) ∨ (P.nonneg (- (f y)) ):= by exact fun a ↦ Cone.IsPrime.mem_or_mem' a
    have :  P.nonneg ( f x * f y):= by{
      rw[<- RingHom.map_mul f x y]
      exact h
    }
    specialize help this
    obtain h₁ | h₂ := help
    · left
      exact h₁
    · right
      rw[(RingHom.map_neg f y).symm] at h₂
      exact h₂
}

def Cone.toLocalization [Algebra R S] (M : Submonoid R) (hLoc: IsLocalization M S)(P: Cone R): Cone S where
  nonneg:={s: S| ∃ m:M, ∃r : R,∃ m': S, s=( (algebraMap R S) r)*(m'*m') ∧ ( (algebraMap R S) m)*m'=1 ∧ r∈ P.nonneg}
  add_nonneg:=by{
    intro a b ha hb
    obtain ⟨m₁ , r₁, m'₁ , h₁, h'₁ ⟩:= ha
    obtain ⟨m₂, r₂, m'₂ , h₂, h'₂ ⟩:= hb
    use (m₁*m₂)
    use (r₁* (m₂*m₂) +r₂ *(m₁*m₁) )
    use (m'₁ )*(m'₂)
    rw[h₁, h₂]
    constructor
    · ring
      rw[(algebraMap R S).map_add, (algebraMap R S).map_mul, (algebraMap R S).map_mul]
      ring
      rw[mul_comm] at h'₂
      have:  (algebraMap R S) r₁ * m'₁ ^ 2 * m'₂ ^ 2 * (algebraMap R S) ((m₂: R) )^2=  (algebraMap R S) r₁ * m'₁ ^ 2 :=by{
        symm
        calc (algebraMap R S) r₁ * m'₁ ^ 2= (algebraMap R S) r₁ * m'₁ ^ 2*1*1:= by ring
          _=(algebraMap R S) r₁ * m'₁ ^2 *( m'₂ * (algebraMap R S) ↑m₂)*( m'₂ * (algebraMap R S) ↑m₂):= by rw[h'₂.1.symm]
          _= (algebraMap R S) r₁ * m'₁ ^ 2 * m'₂ ^ 2 * (algebraMap R S) (↑m₂ )^2:= by ring
      }
      rw[(RingHom.map_pow (algebraMap R S) (↑m₂) 2), this]
      have: m'₁ ^ 2 * (algebraMap R S) r₂ * m'₂ ^ 2 * (algebraMap R S) (↑m₁  )^2= (algebraMap R S) r₂ * m'₂ ^ 2:=by{
        symm
        calc (algebraMap R S) r₂ * m'₂ ^ 2= (algebraMap R S) r₂ * m'₂ ^ 2 * 1* 1:= by ring
          _=(algebraMap R S) r₂ * m'₂ ^2 *((algebraMap R S) ↑m₁ * m'₁)*((algebraMap R S) ↑m₁ * m'₁):= by rw[h'₁.1.symm]
          _=m'₁ ^ 2 * (algebraMap R S) r₂ * m'₂ ^ 2 * (algebraMap R S) (↑m₁  )^2:=by ring
      }
      rw[(RingHom.map_pow (algebraMap R S) (↑m₁) 2), this]
    · constructor
      · push_cast
        rw[ (algebraMap R S).map_mul]
        have: (algebraMap R S) ↑m₁ * (algebraMap R S) ↑m₂ * (m'₁ * m'₂)= ((algebraMap R S) ↑m₁ *m'₁)*((algebraMap R S) ↑m₂ * m'₂):=by ring
        rw[this, h'₁.1, h'₂.1]
        exact one_mul 1
      · apply add_nonneg
        · apply mul_nonneg
          · exact h'₁.2
          · exact square_nonneg P ↑m₂
        · apply mul_nonneg
          · exact h'₂.2
          · exact square_nonneg P ↑m₁
  }
  mul_nonneg:= by{
    intro a b ha hb
    obtain ⟨m₁ , r₁, m'₁ , h₁, h'₁ ⟩:= ha
    obtain ⟨m₂, r₂, m'₂ , h₂, h'₂ ⟩:= hb
    use (m₁*m₂)
    use (r₁ *r₂)
    use (m'₁ *m'₂)
    rw[h₁, h₂ ]
    constructor
    · rw[(algebraMap R S).map_mul]
      ring
    · constructor
      · push_cast
        rw[(algebraMap R S).map_mul]
        calc (algebraMap R S) ↑m₁ * (algebraMap R S) ↑m₂ * (m'₁ * m'₂)= ((algebraMap R S) ↑m₁* m'₁)*((algebraMap R S) ↑m₂ * m'₂):= by ring
          _= 1* 1:= by rw[h'₁.1, h'₂.1]
          _= 1:= by exact one_mul 1
      · apply mul_nonneg
        exact h'₁.2
        exact h'₂.2
  }
  square_nonneg:= by{
    intro s
    have:  ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1:= by exact fun z ↦ IsLocalization.surj M z
    obtain ⟨x, hx ⟩:= this s
    have: ∀ y : M, IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
    obtain ⟨ m', hm'⟩ := IsUnit.exists_right_inv (this x.2)
    use x.2
    use (x.1*x.1)
    use m'
    constructor
    · rw[(algebraMap R S).map_mul]
      calc s *s = (s*1)* (s*1):= by ring
        _= (s* ((algebraMap R S) ↑x.2 * m'))* (s *((algebraMap R S) ↑x.2 * m')):= by rw[hm']
        _=(s* (algebraMap R S) ↑x.2) *m' * (s* (algebraMap R S) ↑x.2) *m' := by ring
        _=  (algebraMap R S) x.1 *m' *(algebraMap R S) x.1 *m' :=by rw[hx]
        _= (algebraMap R S) x.1 * (algebraMap R S) x.1 * (m' * m'):= by ring
    · constructor
      · exact hm'
      · exact square_nonneg P x.1
  }

def Cone.generated_by (I: Set R): Cone R where
  nonneg:= AddSubmonoid.closure (Submonoid.closure (I∪ {b: R| ∃ c: R, b= c*c}): Set R)
  --{r: R| ∃ s:Set R, s⊆  {a: R| ∃ t :Set R, (t)⊆ (I ∪ {b: R| ∃ c: R, b= c*c}) ∧ Set.Finite t  ∧  ∃suppP: t→ ℕ, a = finprod (fun x :t => ((x: R)^ (suppP x): R))} ∧ Set.Finite s ∧ ∃ suppA: s→ ℕ, r = finsum (fun x :s => (x: R)*(suppA x: R))}
  add_nonneg:=by{
    intro a b ha hb
    apply add_mem
    . exact ha
    · exact hb
  }
  mul_nonneg:=by{
    intro r s hr hs
    apply MulMemClass.mul_mem_add_closure hr hs
  }

  square_nonneg:=by{
    intro a
    apply AddSubmonoid.subset_closure
    apply Submonoid.subset_closure
    right
    use a
  }

lemma Cone.generated_by_mono (I J: Set R) (hIJ: I⊆ J):
(Cone.generated_by I).nonneg ⊆ (Cone.generated_by J).nonneg:=by{
  apply AddSubmonoid.closure_mono
  apply Submonoid.closure_mono
  exact union_subset_union_left {b | ∃ c, b = c * c} hIJ
}


lemma Cone.generated_by_cone (C: Cone R):
(Cone.generated_by C.nonneg).nonneg= C.nonneg:=by{
  have hle: (Cone.generated_by C.nonneg).nonneg ⊆  C.nonneg:=by{
    intro c hc
    have:  AddZeroClass (Set R):= by exact Set.addZeroClass
    let p: R→ Prop:= fun x ↦ x∈ C.nonneg
    have hInd:( c ∈ AddSubmonoid.closure (Submonoid.closure ( C.nonneg ∪ {b: R| ∃ c: R, b= c*c}): Set R)) →( ∀ x ∈ Submonoid.closure ( C.nonneg ∪ {b: R| ∃ c: R, b= c*c}), p x)→ ( p 0) →( ∀ x y, p x → p y → p (x + y))→ p c:= by {
      apply AddSubmonoid.closure_induction
    }
    apply hInd
    · exact hc
    · intro x hx
      have hInd: (x ∈ Submonoid.closure (C.nonneg ∪ {b | ∃ c, b = c * c}))→ (∀ y ∈ ( C.nonneg ∪ {b: R| ∃ c: R, b= c*c}), p y)→ (p 1)→ (∀ y z, p y→ p z→ p (y*z))→ p x:=by{
        apply Submonoid.closure_induction
      }
      apply hInd
      · exact hx
      · intro y hy
        obtain h1 | h2:= hy
        · exact h1
        · obtain⟨z, hz ⟩:= h2
          rw[hz]
          exact square_nonneg C z
      · exact one C
      · intro y z hy hz
        exact mul_nonneg C hy hz
    · exact zero C
    · intro x y hx hy
      exact add_nonneg C hx hy


  }
  have hge: C.nonneg ⊆ (Cone.generated_by C.nonneg).nonneg:=by{
    intro c hc
    apply AddSubmonoid.subset_closure
    apply Submonoid.subset_closure
    left
    exact hc
  }
  exact Subset.antisymm hle hge
}

theorem Cone.mem_generated_by_iff_finSubset (I: Set R )(r: R):
r∈ (Cone.generated_by I).nonneg↔ ∃ J:Set R, Set.Finite J∧  J⊆ I∧ r∈ (Cone.generated_by J).nonneg:=by{
  constructor
  · intro h
    have:  AddZeroClass (Set R):= by exact Set.addZeroClass
    let p: R→ Prop:= fun x ↦  ∃ J:Set R, Set.Finite J∧  J⊆ I∧ x∈ (Cone.generated_by J).nonneg
    have hInd:( r ∈ AddSubmonoid.closure (Submonoid.closure ( I ∪ {b: R| ∃ c: R, b= c*c}): Set R)) →( ∀ x ∈ Submonoid.closure ( I∪ {b: R| ∃ c: R, b= c*c}), p x)→ ( p 0) →( ∀ x y, p x → p y → p (x + y))→ p r:= by {
      apply AddSubmonoid.closure_induction
    }
    apply hInd
    · exact h
    · intro x hx
      have hInd: (x ∈ Submonoid.closure (I ∪ {b | ∃ c, b = c * c}))→ (∀ y ∈ ( I ∪ {b: R| ∃ c: R, b= c*c}), p y)→ (p 1)→ (∀ y z, p y→ p z→ p (y*z))→ p x:=by{
        apply Submonoid.closure_induction
      }
      apply hInd
      · exact hx
      · intro y hy
        obtain h1 | h2:= hy
        · use {y}
          constructor
          · exact finite_singleton y
          · constructor
            · exact singleton_subset_iff.mpr h1
            · apply AddSubmonoid.subset_closure
              apply Submonoid.subset_closure
              left
              exact rfl
        · use ∅
          constructor
          · exact finite_empty
          · constructor
            · exact empty_subset I
            · apply AddSubmonoid.subset_closure
              apply Submonoid.subset_closure
              right
              exact h2
      · use ∅
        constructor
        · exact finite_empty
        · constructor
          · exact empty_subset I
          · exact one (generated_by ∅)
      · intro y z hy hz
        obtain ⟨ J₁, hJ11, hJ12, hJ13⟩ := hy
        obtain⟨J₂ , hJ21, hJ22, hJ23 ⟩:= hz
        use J₁ ∪ J₂
        constructor
        · exact Set.Finite.union hJ11 hJ21
        · constructor
          · exact union_subset hJ12 hJ22
          · apply (generated_by (J₁ ∪ J₂)).mul_nonneg
            · apply Cone.generated_by_mono J₁
              exact (subset_union_left J₁ J₂)
              exact hJ13
            · apply Cone.generated_by_mono J₂
              exact (subset_union_right J₁ J₂)
              exact hJ23
    · use ∅
      constructor
      · exact finite_empty
      · constructor
        · exact empty_subset I
        · exact zero (generated_by ∅)
    · intro x y hx hy
      obtain ⟨ J₁, hJ11, hJ12, hJ13⟩ := hx
      obtain⟨J₂ , hJ21, hJ22, hJ23 ⟩:= hy
      use J₁∪ J₂
      constructor
      · exact Set.Finite.union hJ11 hJ21
      · constructor
        · exact union_subset hJ12 hJ22
        · apply (generated_by (J₁ ∪ J₂)).add_nonneg
          · apply Cone.generated_by_mono J₁
            exact (subset_union_left J₁ J₂)
            exact hJ13
          · apply Cone.generated_by_mono J₂
            exact (subset_union_right J₁ J₂)
            exact hJ23

  · intro h
    obtain⟨J, hJ ⟩:= h
    apply Cone.generated_by_mono J
    exact hJ.2.1
    exact hJ.2.2
}


def Cone.extend_by_elt (C: Cone R) (x:R): Cone R where
  nonneg:= {r : R| ∃ a b: R, r= a+ b*x ∧ a∈ C.nonneg ∧ b∈ C.nonneg }
  add_nonneg:=by{
        intro r r' hr hr'
        obtain ⟨a ,b, hab ⟩:= hr
        obtain ⟨a',b', hab' ⟩:=hr'
        use (a+a')
        use (b+b')
        constructor
        · rw[hab.1, hab'.1]
          ring
        · constructor
          · apply C.add_nonneg
            exact hab.2.1
            exact hab'.2.1
          · apply C.add_nonneg
            exact hab.2.2
            exact hab'.2.2
      }
  mul_nonneg:=by{
    intro r r' hr hr'
    obtain ⟨a ,b, hab ⟩:= hr
    obtain ⟨a',b', hab' ⟩:=hr'
    use (a*a'+b*b'*(x*x))
    use (a*b'+ b*a')
    constructor
    · rw[hab.1, hab'.1]
      ring
    · constructor
      · apply C.add_nonneg
        · apply C.mul_nonneg
          exact hab.2.1
          exact hab'.2.1
        · apply C.mul_nonneg
          · apply C.mul_nonneg
            exact hab.2.2
            exact hab'.2.2
          · exact square_nonneg C x
      · apply C.add_nonneg
        · apply C.mul_nonneg
          exact hab.2.1
          exact hab'.2.2
        · apply C.mul_nonneg
          exact hab.2.2
          exact hab'.2.1
  }
  square_nonneg:= by{
    intro r
    use (r*r)
    use (0:R)
    constructor
    · ring
    · constructor
      · exact square_nonneg C r
      · exact zero C
  }

lemma Cone.maximal_isPrime (M: Cone R) (hM: Cone.IsMaximal M): Cone.IsPrime M:=by{
  constructor
  · exact hM.1
  · intro x y hxy
    by_contra hcon
    push_neg at hcon
    let Mx:=Cone.extend_by_elt M x
    let My:= Cone.extend_by_elt M (-y)
    have hnpMx: (-1: R)∈ Mx.nonneg:= by{
      by_contra hcontra
      have: M.nonneg=Mx.nonneg:=by{
        apply hM.2 Mx
        exact { proper := hcontra }
        intro r hr
        use r
        use 0
        simp
        constructor
        · exact hr
        · exact zero M
      }
      have: x ∈ M.nonneg:=by{
        rw[this]
        use 0
        use 1
        simp
        constructor
        · exact zero M
        · exact one M
      }
      exact hcon.1 this
    }
    have hnpMy: ((-1:R))∈ My.nonneg:=by{
      by_contra hcontra
      have: M.nonneg=My.nonneg:=by{
        apply hM.2 My
        exact { proper := hcontra }
        intro r hr
        use r
        use 0
        simp
        constructor
        · exact hr
        · exact zero M
      }
      have: (-y)∈ M.nonneg:=by{
        rw[this]
        use 0
        use 1
        simp
        constructor
        · exact zero M
        · exact one M
      }
      exact hcon.2 this
    }
    obtain⟨a,b, hab1, hab2 ⟩:=hnpMx
    obtain⟨c, d, hcd1, hcd2 ⟩:= hnpMy
    have hab1': -(b*x)=1+a:= by{
      have: -1-(b*x)=a :=by refine sub_eq_of_eq_add hab1
      rw[this.symm]
      ring
    }
    have hcd1': d*y= 1+c:=by{
      have: -1-(d*(-y))=c:=by refine sub_eq_of_eq_add hcd1
      rw[this.symm]
      ring
    }
    have: -1= a+c+a*c +(b*x)*(d*y):=by{
      have heq: (-(b*x))*(d*y)=1+a+c+a*c:=by{
        rw[hab1', hcd1']
        ring
      }
      have: (b*x)*(d*y)= -(-(b*x)*(d*y)):=by ring
      rw[this, heq]
      ring
    }

    have hcontradiction: (-1: R)∈ M.nonneg:=by{
      rw[this]
      apply M.add_nonneg
      · apply M.add_nonneg
        · apply M.add_nonneg
          exact hab2.1
          exact hcd2.1
        · apply M.mul_nonneg
          exact hab2.1
          exact hcd2.1
      · have:b * x * (d * y)=b*d* (x*y):=by ring
        rw[this]
        apply M.mul_nonneg
        · apply M.mul_nonneg
          exact hab2.2
          exact hcd2.2
        · exact hxy
    }
    exact hM.1 hcontradiction
}

theorem Cone.exists_le_maximal (C: Cone R) (hC: IsProper C):
∃ M, Cone.IsMaximal M ∧ C.nonneg ⊆ M.nonneg:=by{
  let Z:= {P: Set R| C.nonneg⊆ P∧ (∀r t: R,r∈ P→t∈ P→ r+t∈ P∧ r*t∈ P)∧ (-1: R)∉ P}
  have hZorn: ∃ m ∈ Z, ∀ P ∈ Z, m ⊆ P → P = m:=by{
    apply zorn_subset Z
    intro K hKZ hK
    by_cases h: Nonempty K
    · use ⋃₀ K
      constructor
      · constructor
        · intro r hr
          have: ∃ P, P∈ K:= by exact nonempty_subtype.mp h
          obtain⟨P, hP ⟩:=this
          have: ⋃₀{P} ⊆⋃₀ K:= by{
            have: {P} ⊆K:=by exact singleton_subset_iff.mpr hP
            exact sUnion_mono this
          }
          have hrP: r∈ ⋃₀{P}:= by{
            simp
            have: C.nonneg ⊆  P:=by{
              have: P∈ Z:=by{
                exact hKZ hP
              }
              exact this.1
            }
            exact this hr
          }
          exact this hrP
        · constructor
          · intro r t hr ht
            obtain⟨i, hi1, hi2 ⟩:= hr
            obtain⟨j, hj1, hj2 ⟩:= ht
            have: i⊆ j ∨ j⊆ i:= by exact IsChain.total hK hi1 hj1
            obtain hij | hji:= this
            · have: (∀ (r' t' : R), r' ∈ j → t' ∈ j → r' + t' ∈ j ∧ r' * t' ∈ j):=by{
                have: j ∈ Z:=by exact hKZ hj1
                exact this.2.1
              }
              specialize this r t (hij hi2) hj2
              obtain ⟨ hp, hm⟩ := this
              constructor
              · exact mem_sUnion_of_mem hp hj1
              · exact mem_sUnion_of_mem hm hj1
            · have: (∀ (r' t' : R), r' ∈ i → t' ∈ i → r' + t' ∈ i ∧ r' * t' ∈ i):=by{
                have: i ∈ Z:=by exact hKZ hi1
                exact this.2.1
              }
              specialize this r t hi2 (hji hj2)
              obtain ⟨ hp, hm⟩ := this
              constructor
              · exact mem_sUnion_of_mem hp hi1
              · exact mem_sUnion_of_mem hm hi1
          · by_contra hcon
            obtain ⟨i, hi1, hi2 ⟩:= hcon
            have: i ∈ Z:= by exact hKZ hi1
            exact this.2.2 hi2
      · intro i hi
        exact subset_sUnion_of_mem hi
    · use C.nonneg
      constructor
      · constructor
        · exact Eq.subset rfl
        · constructor
          · intro r t hr ht
            constructor
            · exact add_nonneg C hr ht
            · exact mul_nonneg C hr ht
          · exact IsProper.proper
      · simp at h
        intro r hr
        exact ((h r) hr).elim
  }
  obtain ⟨ m, hm1, hm2⟩:=hZorn
  let M: Cone R:= {
    nonneg:=m
    add_nonneg:=by{
      intro r t hr ht
      exact (hm1.2.1 r t hr ht).1
    }
    mul_nonneg:=by{
      intro r t hr ht
      exact (hm1.2.1 r t hr ht).2
    }
    square_nonneg:=by{
      intro r
      have: r*r∈ C.nonneg:= by exact square_nonneg C r
      exact hm1.1 this
    }
  }
  use M
  constructor
  · constructor
    · exact hm1.2.2
    · intro P hpP hMP
      symm
      apply hm2
      · constructor
        · exact Subset.trans hm1.1 hMP
        · constructor
          · intro r t hr ht
            constructor
            · exact add_nonneg P hr ht
            · exact mul_nonneg P hr ht
          · exact IsProper.proper
      · exact hMP
  · exact hm1.1
}
lemma Cone.exists_le_prime (C: Cone R) (hC: IsProper C):
∃ P, Cone.IsPrime P ∧ C.nonneg ⊆ P.nonneg:=by{
  obtain⟨M, hM1, hM2 ⟩:= Cone.exists_le_maximal C hC
  use M
  constructor
  · apply Cone.maximal_isPrime
    exact hM1
  · exact hM2
}
