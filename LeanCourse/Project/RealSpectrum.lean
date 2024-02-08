import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sober
import LeanCourse.Project.SpectralSpaces
import LeanCourse.Project.Cone
import LeanCourse.Project.AlexanderSubbase
import LeanCourse.Project.IrreducibleSubbase
import Mathlib.Algebra.Order.Ring.Cone
universe u v

variable {R : Type u}{S: Type v} [CommRing R][CommRing S]
variable {α: Type u}
variable [TopologicalSpace α] {X: Set α}

open Ring
open Topology
open Function Set Order
open TopologicalSpace

/-
In this file the define the real spectrum of a ring and proof some of its properties.
In fact the real spectrum turns out to be a spectral space here we only formlaize three
out of the four necesssary conditions (soberness needs still to  be done).
-/


-- The real spectum of a ring R is defined as the set of all primecones in R
@[ext]
structure RealSpectrum (R: Type u)[CommRing R] where
  asCone : Cone R
  IsPrime :Cone.IsPrime asCone



lemma RealSpectrum.ext_neq_iff_neq' (P Q: RealSpectrum R): P≠ Q↔ P.asCone≠ Q.asCone:=by{
  constructor
  · intro h
    by_contra hcon
    exact h ((RealSpectrum.ext_iff P Q).mpr hcon)
  · intro h
    by_contra hcon
    exact h ((RealSpectrum.ext_iff P Q).mp hcon)
}

lemma RealSpectrum.ext_neq_iff_neq (P Q: RealSpectrum R):P≠ Q ↔ P.asCone.nonneg≠ Q.asCone.nonneg:=by{
  rw[RealSpectrum.ext_neq_iff_neq']
  rw[Cone.ext_neq_iff_neq]
}

-- The real spectrum can naturally be endowed with a topology




def positiveLocus (s :  R) : Set (RealSpectrum R) :=
  { P | (-s)∉  P.asCone.nonneg  }


instance harrisonTopology : TopologicalSpace (RealSpectrum R) :=
  TopologicalSpace.generateFrom (positiveLocus '' Set.univ)

def nonnegativeLocus (I: Set R): Set (RealSpectrum R):=
  {P| I ⊆ P.asCone.nonneg}

lemma positiveLocus_compl_nonnegativeLocus (r: R): nonnegativeLocus {r}=(positiveLocus (-r))ᶜ :=by{
  ext P
  constructor
  · intro hP
    simp
    by_contra hcon
    have: -(-r)∉P.asCone.nonneg:= by exact hcon
    simp at this
    exact this (hP rfl)
  · intro hP
    simp at hP
    have: -(-r)∈ P.asCone.nonneg:= by exact not_not_mem.mp hP
    simp at this
    have: {r} ⊆ P.asCone.nonneg:= by exact singleton_subset_iff.mpr this
    exact this

}
lemma RealSpectrum.nonnegativeLocus_inter (I:Set R): (nonnegativeLocus I)=⋂ r :  I, ((nonnegativeLocus ({r.1}:Set R))):=by{
  ext P
  constructor
  · intro hP
    simp
    intro r hr
    have: {r}⊆  P.asCone.nonneg:=by{
      exact singleton_subset_iff.mpr (hP hr)
    }
    exact this
  · intro hP
    intro r hr
    simp at  hP
    exact (hP r hr) rfl
}


lemma RealSpectrum.isClosed_NN (I: Set R): IsClosed (nonnegativeLocus I):=by{

  rw[RealSpectrum.nonnegativeLocus_inter I]
  apply isClosed_iInter
  intro r
  rw[positiveLocus_compl_nonnegativeLocus]
  simp
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact mem_image_of_mem positiveLocus trivial
}

/-
similar to the prime spectrum of a ring the construction of the real spectrum is
functorial.
We only describe the comap and proof its continuity, composition and id still need
to be checked.
-/
def comap (f : R →+* S) : C(RealSpectrum S, RealSpectrum R) where
  toFun y := ⟨Cone.comap f y.asCone, Cone.comap_isPrime f y.asCone y.IsPrime ⟩
  continuous_toFun := by{
    apply continuous_generateFrom
    intro P hP
    obtain ⟨r ,hr ⟩:= hP
    let f': RealSpectrum S → RealSpectrum R :=fun y ↦ { asCone := Cone.comap f y.asCone, IsPrime := by refine Cone.comap_isPrime f y.asCone y.IsPrime }
    show IsOpen ((f') ⁻¹' P)
    have hrw: (f') ⁻¹' P= positiveLocus (f r):=by{
      ext Q
      constructor
      · intro hc
        by_contra hcontra
        rw[hr.2.symm] at hc
        have : f' Q ∈  positiveLocus r:= by exact hc
        have hdiction: ¬ ((f' Q).asCone.nonneg (-r)):= by exact this
        have : Cone.nonneg (f' Q).asCone (-r)= Cone.nonneg Q.asCone (f (- r  )):= by exact rfl
        rw[this, (RingHom.map_neg f r)] at hdiction
        exact hcontra hdiction
      · intro h
        rw[hr.2.symm]
        by_contra hcon
        have : f' Q ∉ positiveLocus r:= by exact hcon
        have hdiction: ¬ ¬  ((f' Q).asCone.nonneg (-r)):= by exact this
        have : Cone.nonneg (f' Q).asCone (-r)= Cone.nonneg Q.asCone (f (- r  )):= by exact rfl
        rw[this,  (RingHom.map_neg f r)] at hdiction
        exact hdiction h

    }
    rw[hrw]
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    exact Set.mem_image_of_mem positiveLocus trivial
  }



/-
In order to adress quasi-compactness of the real spectrum we develop an algebraic
criterion for a collection of subbasic sets to be a cover. This criterion will turn
out to be finitely satisfiable resulting in finite subcovers.
-/

 lemma RealSpectrum.Cov_iff_negOne (I: Set R):
  univ ⊆ ⋃₀ (positiveLocus '' I) ↔ (-1)∈ (Cone.generated_by {r: R| -r∈ I}).nonneg:=by{
    constructor
    · intro h
      by_contra hcon
      have hcon: Cone.IsProper (Cone.generated_by {r: R| -r∈ I}):=by {
        constructor
        exact hcon
      }
      obtain⟨P, hP ⟩:=Cone.exists_le_prime (Cone.generated_by {r: R| -r∈ I}) hcon
      have: ∃ Q: (RealSpectrum R), Q.asCone=P:=by{
        use ⟨P, hP.1 ⟩
      }
      obtain⟨Q,hQ ⟩:= this
      have: Q∈ ⋃₀ (positiveLocus '' I):= by exact h trivial
      obtain⟨P', hP'1, hP' ⟩:= this
      obtain⟨r, hr1, hr2 ⟩:= hP'1
      have hQr: Q ∈  positiveLocus r:=by{
        rw[hr2]
        exact hP'
      }
      have hdiction: -r∈ P.nonneg:=by{
        apply hP.2
        apply AddSubmonoid.subset_closure
        apply Submonoid.subset_closure
        left
        have:r= - (-r):=by exact neg_eq_iff_eq_neg.mp rfl
        rw[this] at hr1
        exact hr1
      }
      have hcontra: -r∉ P.nonneg:=by{
        have: (-r)∉  Q.asCone.nonneg:= by exact hQr
        rw[hQ] at this
        exact this
      }
      exact hcontra hdiction
    · intro h
      intro Q hQ
      by_contra hcon
      simp at hcon
      let P:= Q.asCone
      have hIQ: {r | -r ∈ I}⊆ P.nonneg:=by{
        intro r hr
        specialize hcon (-r) hr
        have: ¬ (-(-r)∉  Q.asCone.nonneg):= by exact hcon
        simp at this
        exact this
      }
      have: (Cone.generated_by P.nonneg).nonneg= P.nonneg:= by apply Cone.generated_by_cone
      have hdiction: -1 ∈ P.nonneg:=by{
        rw[this.symm]
        apply Cone.generated_by_mono
        exact hIQ
        exact h
      }
      have hcontra: -1∉ P.nonneg:=by{
        have: Cone.IsPrime Q.asCone:=by{
          exact Q.IsPrime
        }
        have: -1∉  Q.asCone.nonneg:=by{
          exact this.1
        }
        exact this
      }
      exact hcontra hdiction
  }


instance compactSpace: CompactSpace (RealSpectrum R) := by{
  rw[<- isCompact_univ_iff]
  apply alexander_subbbase
  · exact rfl
  · intro C hC hCov
    --by_contra hcon
    --simp at hcon
    let I:={r: R| positiveLocus r ∈ C}
    have hC: C =positiveLocus '' I:=by{
      ext P
      constructor
      · intro hP
        have: P ∈ positiveLocus '' univ:=by{
          exact hC hP
        }
        simp at this
        obtain ⟨r, hr ⟩:= this
        use r
        constructor
        · rw[hr.symm] at hP
          exact hP
        · exact hr
      · intro hP
        obtain ⟨r, hr⟩:= hP
        rw[hr.2.symm]
        exact hr.1
    }
    rw[hC] at hCov
    rw[RealSpectrum.Cov_iff_negOne ] at hCov
    rw[Cone.mem_generated_by_iff_finSubset] at hCov
    obtain⟨ J, hJ1, hJ2, hJ3⟩ := hCov
    use (positiveLocus '' {r | -r ∈ J})
    constructor
    · rw[RealSpectrum.Cov_iff_negOne ]
      simp
      exact hJ3
    · constructor
      · rw[hC]
        suffices: {r | -r ∈ J} ⊆ I
        exact image_subset positiveLocus this
        intro r hr
        exact neg_mem_neg.mp (hJ2 hr)
      · suffices: Set.Finite {r | -r ∈ J}
        exact Finite.image positiveLocus this
        have: (fun x: R↦ -x) '' J= {r | -r ∈ J}:=by{
          ext x
          simp
        }
        rw[this.symm]
        exact Finite.image (fun x ↦ -x) hJ1
}
--That the Real Spectrum is T0 is immediate to see as the following proof shows

instance t0space: T0Space (RealSpectrum R) :=by{
  rw[t0Space_iff_not_inseparable]
  intro P Q hPQ
  have: P.asCone.nonneg ≠ Q.asCone.nonneg:=by{
    exact (RealSpectrum.ext_neq_iff_neq P Q).mp hPQ
  }
  have: (¬ P.asCone.nonneg⊆Q.asCone.nonneg )  ∨ (¬ Q.asCone.nonneg ⊆ P.asCone.nonneg):= by {
    by_contra hcon
    push_neg at hcon
    exact this (Subset.antisymm_iff.mpr hcon)
  }
  obtain h1 | h2:= this
  · have h1: ∃ r, r ∈ P.asCone.nonneg ∧ r∉ Q.asCone.nonneg:= by{
      exact not_subset.mp h1
    }
    obtain ⟨r, hr1, hr2 ⟩:= h1
    rw[not_inseparable_iff_exists_open]
    use (positiveLocus (-r))
    constructor
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      simp
    · right
      constructor
      · have: r = -(-r):= by {exact neg_eq_iff_eq_neg.mp rfl }
        rw[this] at hr2
        exact hr2
      · by_contra hcon
        have: r = -(-r):= by {exact neg_eq_iff_eq_neg.mp rfl }
        rw[this] at hr1
        exact hcon hr1
  · have h2: ∃ r, r ∈ Q.asCone.nonneg ∧ r∉ P.asCone.nonneg:= by{
      exact not_subset.mp h2
    }
    obtain ⟨r, hr1, hr2 ⟩:= h2
    rw[not_inseparable_iff_exists_open]
    use (positiveLocus (-r))
    constructor
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      simp
    · left
      constructor
      · have: r = -(-r):= by {exact neg_eq_iff_eq_neg.mp rfl }
        rw[this] at hr2
        exact hr2
      · by_contra hcon
        have: r = -(-r):= by {exact neg_eq_iff_eq_neg.mp rfl }
        rw[this] at hr1
        exact hcon hr1
}

/-
In order to show that the real spectrum is spectral one nedds to show that there
exists a basis of qausi-compact open subsets. We would like to take the basis
generated from our subbase.
In order to proof the quasi-compactness of these finite intersections we will make a
detour to the localization.
-/
lemma Cone.toLocalization_isPrime_mOne [Algebra R S] (M : Set R) (hLoc: IsLocalization (Submonoid.closure M) S) (P: (⋂ r∈ M, positiveLocus (r*r))): -1∉ (Cone.toLocalization (Submonoid.closure M) hLoc (P: RealSpectrum R).asCone).nonneg:=by{
    by_contra hcon
    obtain ⟨m , r, m', h1, h2, h3 ⟩:= hcon
    have h1: -((algebraMap R S) ↑m * (algebraMap R S) ↑m)=(algebraMap R S) r:=by{
      symm
      calc (algebraMap R S) r= (algebraMap R S) r *1 *1:= by ring
        _=(algebraMap R S) r *((algebraMap R S) ↑m * m') *((algebraMap R S) ↑m * m'):= by rw[h2]
        _= ((algebraMap R S) r * (m' * m')) * (algebraMap R S) ↑m *(algebraMap R S) ↑m:= by ring
        _= (-1) *(algebraMap R S) ↑m *(algebraMap R S) ↑m := by rw[h1]
        _=-((algebraMap R S) ↑m * (algebraMap R S) ↑m):= by ring
    }
    rw[<- ((algebraMap R S).map_mul) ↑m ↑m ] at h1
    have: -(algebraMap R S) (↑m * ↑m)= (algebraMap R S) (-(↑m * ↑m)):= by exact (RingHom.map_neg (algebraMap R S) (↑m * ↑m)).symm
    rw[this] at h1
    have this: ∃ c : (Submonoid.closure M), ↑c * (-(↑m * ↑m)) = ↑c * r:= by exact (IsLocalization.eq_iff_exists (Submonoid.closure M) S).mp h1
    obtain⟨c, hc ⟩:= this
    have hc': c *( ↑c * (-(↑m * ↑m))) =c*  (↑c * r):= by exact congrArg (HMul.hMul (c: R)) hc
    simp at hc'
    have hP: -((c: R) * (↑c * (↑m * ↑m)))∈ (P: RealSpectrum R).asCone.nonneg:= by{
      rw[hc', <- mul_assoc]
      apply (P: RealSpectrum R).asCone.mul_nonneg
      · exact (P: RealSpectrum R).asCone.square_nonneg (c:R)
      · exact h3
    }
    have: -((c: R) * (↑c * (↑m * ↑m)))= -(((c: R)*↑m  ) *(↑c* ↑m)):= by ring
    rw[this] at hP
    let s:= c* m
    have hcontra: -((s:R )*s)∉ (P: RealSpectrum R).asCone.nonneg:= by{
      let p: R→ Prop:= fun x ↦ -(x* x)∉  (P: RealSpectrum R).asCone.nonneg
      have hInd: ((s: R) ∈ Submonoid.closure (M))→ (∀ y ∈ (M), p y)→ (p 1)→ (∀ y z, p y→ p z→ p (y*z))→ p (s: R):=by{
        apply Submonoid.closure_induction
      }
      apply hInd
      · exact SetLike.coe_mem s
      · intro y hy
        have: (P: RealSpectrum R) ∈ positiveLocus (y*y):= by{
          have : (P: RealSpectrum R) ∈(⋂ r ∈ M, positiveLocus (r * r)):= by exact Subtype.mem P
          simp at this
          exact this y hy
        }
        exact this
      · have: -1 ∉ (P: RealSpectrum R).asCone.nonneg:= by exact (P: RealSpectrum R).IsPrime.1
        have hidem: -1= -((1:R)*1):=by ring
        rw[hidem] at this
        exact this
      · intro y z hy hz
        by_contra hcon
        have: -(y * z * (y * z))=(-(y*y))*((z*z)):= by ring
        rw[this] at hcon
        have: -(y*y) ∈ (P: RealSpectrum R).asCone.nonneg ∨ (-(z*z))∈ (P: RealSpectrum R).asCone.nonneg:= by {
          apply (P: RealSpectrum R).IsPrime.2 hcon
        }
        obtain hh1| hh2:= this
        · exact hy hh1
        · exact hz hh2
    }
    exact hcontra hP
}
lemma Cone.toLocalization_mem_image [Algebra R S] (M : Submonoid R) (hLoc: IsLocalization (M) S) (P: RealSpectrum R) (s: S) (x: R × M) (hx: s * (algebraMap R S) (x.2: R) = (algebraMap R S) x.1) (hsP: s ∈ (Cone.toLocalization M hLoc P.asCone).nonneg ): ∃ d :M, x.1* (x.2:R)* (d*d)∈ P.asCone.nonneg:=by{
    obtain⟨n, r, n',h ⟩:=hsP
    have this: ∃ c : M, ↑c * (x.1  * n * n) = ↑c * (↑x.2* r):= by {
      have h1: (algebraMap R S) (x.1   * n * n) =(algebraMap R S) (↑x.2* r):= by{
      symm
      calc (algebraMap R S) ( ↑x.2 * r)=   (algebraMap R S) ↑x.2 * (algebraMap R S) r:= by{
          rw[(algebraMap R S).map_mul]
        }
        _=(algebraMap R S) ↑x.2 * (algebraMap R S) r *1 *1:= by ring
        _= (algebraMap R S) ↑x.2 * (algebraMap R S) r *((algebraMap R S) ↑n * n')* ((algebraMap R S) ↑n * n'):= by rw[h.2.1]
        _= (algebraMap R S) ↑x.2 * ((algebraMap R S) r *( n'* n'))* ((algebraMap R S) ↑n* (algebraMap R S) ↑n):= by ring
        _= (algebraMap R S) ↑x.2 *(s)* (algebraMap R S) (n *n):= by rw[h.1, (algebraMap R S).map_mul ]
        _= (s* (algebraMap R S) ↑x.2)*  (algebraMap R S) (n *n):= by ring
        _= (algebraMap R S) ↑x.1 * (algebraMap R S) (n *n):= by rw[hx]
        _= (algebraMap R S) (x.1   * n * n):= by{
          simp
          ring
        }
      }
      exact (IsLocalization.eq_iff_exists M S).mp h1
    }
    obtain ⟨c, hc ⟩:= this
    have hc':(↑x.2* ↑c) *( ↑c * (x.1  *  n * n))=(↑x.2* ↑c ) * (↑c * (↑x.2* r)):=by exact congrArg (HMul.hMul ((x.2:R)* (c:R) )) hc
    have hP: (↑x.2* ↑c) *( ↑c * (x.1  *  n * n))∈ (P: RealSpectrum R).asCone.nonneg:=by{
      rw[hc']
      have:  ↑x.2 * ↑c * (↑c * ( ↑x.2 * r))=(↑x.2* ↑x.2)*(↑c* ↑c)* r:= by ring
      rw[this]
      apply (P: RealSpectrum R).asCone.mul_nonneg
      · apply (P: RealSpectrum R).asCone.mul_nonneg
        · exact (P: RealSpectrum R).asCone.square_nonneg (x.2: R)
        · exact (P: RealSpectrum R).asCone.square_nonneg (c: R)
      · exact h.2.2
    }
    use c*n
    have: ↑x.2 * ↑c * (↑c * (x.1 * ↑n * ↑n)) =x.1 * ↑x.2 * (↑(c * n) * ↑(c * n)):= by{
      push_cast
      ring
    }
    rw[this.symm]
    exact hP
}



lemma Cone.toLocalization_isPrime_mem_or_mem' [Algebra R S] (M : Submonoid R) (hLoc: IsLocalization (M) S) (P: RealSpectrum R): ∀ {x y : S},(x * y)∈  (Cone.toLocalization M hLoc P.asCone).nonneg   →(x ∈ (Cone.toLocalization M hLoc P.asCone).nonneg  ) ∨ ((-y) ∈ (Cone.toLocalization M hLoc P.asCone).nonneg  ):=by{
    intro s s' hss'
    have:  ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1:= by exact fun z ↦ IsLocalization.surj M z
    obtain⟨ x, hx⟩ := this s
    obtain ⟨ y, hy⟩ := this s'
    have: ∀ y :  M, IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
    obtain ⟨ m, hm⟩ := IsUnit.exists_right_inv (this x.2)
    obtain ⟨ m', hm'⟩ := IsUnit.exists_right_inv (this y.2)
    have hhelp: ∃ d :M, (x.1* y.1)* ((x.2:R)*(y.2: R))* (d*d)∈ P.asCone.nonneg:=by{
      apply Cone.toLocalization_mem_image M hLoc (P: RealSpectrum R) (s*s') (x.1*y.1, x.2*y.2)
      · simp
        calc s * s' * ((algebraMap R S) ↑x.2 * (algebraMap R S) ↑y.2)=(s* (algebraMap R S) ↑x.2 )*(s'* (algebraMap R S) ↑y.2 ):=by ring
          _= (algebraMap R S) x.1 * (algebraMap R S) y.1:=by rw[hx,hy]
      · exact hss'
    }
    obtain⟨ d, hd⟩ := hhelp
    have hPrim: (x.1*  ↑x.2 * ↑d * ↑d ) ∈ (P: RealSpectrum R).asCone.nonneg ∨ -(y.1 * ↑y.2)∈ (P: RealSpectrum R).asCone.nonneg:=by{
      have: (x.1*y.1)*((x.2: R)*(y.2 :R))*((d:R)*(d:R))=(x.1*  ↑x.2 * ↑d * ↑d)*(y.1 * ↑y.2):= by ring
      rw[this] at hd
      apply (P: RealSpectrum R).IsPrime.2 hd
    }
    obtain h1 | h2:= hPrim
    · left
      use x.2 * d
      use x.1 * ↑x.2 * (d:R)* (d: R)
      have: ∀ y :  M, IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
      obtain ⟨ mm, hmm⟩ := IsUnit.exists_right_inv (this (x.2 * d))
      use mm
      constructor
      · have : x.1 * ↑x.2 * ↑d * ↑d= (x.1* ( ↑d))* (↑x.2 * ↑d ):= by ring
        rw[this, (algebraMap R S).map_mul, mul_assoc]
        push_cast at hmm
        have: (algebraMap R S) (↑x.2 * ↑d) * (mm * mm)=(algebraMap R S) (↑x.2 * ↑d) * mm * mm:= by ring
        rw[this, hmm, (algebraMap R S).map_mul, mul_assoc ]
        have: (algebraMap R S) (↑d) * (1 * mm)= m:=by{
          symm
          rw[mul_comm] at hm
          calc m= m*1:= by exact (mul_one m).symm
            _=m *((algebraMap R S) (↑x.2 * (↑d)) * mm):= by{
                rw[hmm.symm]
              }

            _= m* ((algebraMap R S) ↑x.2 * (algebraMap R S) (↑d) *mm):= by {
              rw[(algebraMap R S).map_mul]
            }
            _=m * (algebraMap R S) ↑x.2* (algebraMap R S) (↑d) *mm:= by ring
            _= 1* (algebraMap R S) (↑d) *mm:= by rw[hm]
            _= (algebraMap R S) (↑d) * (1 * mm):=by ring
        }
        rw[this]
        calc s = s*1:= by exact (mul_one s).symm
          _=(s*(algebraMap R S) ↑x.2) * m:=by{
            rw[hm.symm]
            rw[mul_assoc]
            }
          _= (algebraMap R S) x.1 *m:= by rw[hx]

      · constructor
        · exact hmm
        · exact h1
    · right
      use y.2
      use -(y.1*y.2)
      use m'
      constructor
      · suffices: s' = (algebraMap R S) ((y.1 * ↑y.2)) * (m' * m')
        rw[this]
        simp
        rw[(algebraMap R S).map_mul, mul_assoc]
        have: (algebraMap R S) ↑y.2 * (m' * m')= ((algebraMap R S) ↑y.2 * m')*m':= by ring
        rw[this, hm', hy.symm, mul_assoc]
        simp
        rw[ hm']
        simp

      · constructor
        · exact hm'
        · exact h2


}

lemma RealSpectrum.inter_multClosure (M : Set R): (⋂ r∈ M, positiveLocus (r*r))= (⋂ r∈ (Submonoid.closure M), positiveLocus (r*r)):=by{
  ext P
  constructor
  · intro h
    simp
    simp at h
    intro r hr
    let p: R→ Prop:= fun x ↦   P ∈ positiveLocus (x * x)
    apply Submonoid.closure_induction (p:=p)
    · exact hr
    · intro y hy
      exact h y hy
    · simp
      by_contra hcon
      exact hcon P.IsPrime.1
    · intro y z hy hz
      by_contra hcon
      simp at hcon
      have: -(y*z*(y*z))∈ P.asCone.nonneg:= by exact not_not_mem.mp hcon
      have heq: -(y*z*(y*z))= (-(y*y))*(z*z):=by ring
      rw[heq ] at this
      have: (-(y*y))∈ P.asCone.nonneg ∨ -(z*z)∈ P.asCone.nonneg:= by{
        exact P.IsPrime.2 this
      }
      obtain h1 | h2:= this
      · exact hy h1
      · exact hz h2
  · intro h
    have: M ⊆ (Submonoid.closure M):= by exact Submonoid.subset_closure
    simp at h
    simp
    intro P hP
    exact h P (this hP)
}

lemma Cone.toLocalization_isPrime [Algebra R S] (M : Set R) (hLoc: IsLocalization (Submonoid.closure M) S) (P: (⋂ r∈ M, positiveLocus (r*r))): Cone.IsPrime (Cone.toLocalization (Submonoid.closure M) hLoc (P: RealSpectrum R).asCone):= by{
  constructor
  · exact toLocalization_isPrime_mOne M hLoc P
  · exact fun {x y} a ↦ toLocalization_isPrime_mem_or_mem' (Submonoid.closure M) hLoc (↑P) a
}

/-
The now formlized results allow us to describe the real spectrum of the localization
as a certain subset of the real spectrum of the original ring. Where the homeomorphism
is in one direction given by the comap
-/

def RealSpectrum.toLocalization [Algebra R S] (M : Set R) (hLoc: IsLocalization (Submonoid.closure M) S): C((⋂ r∈ M, positiveLocus (r*r)), RealSpectrum S) where
  toFun y := ⟨(Cone.toLocalization (Submonoid.closure M) hLoc (y: RealSpectrum R).asCone), Cone.toLocalization_isPrime M hLoc y  ⟩
  continuous_toFun := by{
    apply continuous_generateFrom
    intro Q hQ
    let f': (⋂ r∈ M, positiveLocus (r*r)) → RealSpectrum S :=fun y ↦ ⟨(Cone.toLocalization (Submonoid.closure M) hLoc (y: RealSpectrum R).asCone), Cone.toLocalization_isPrime M hLoc y  ⟩
    show IsOpen ((f') ⁻¹' Q)
    obtain⟨s, hs ⟩:= hQ
    have:  ∀ z : S, ∃ x : R × (Submonoid.closure M), z * algebraMap R S x.2 = algebraMap R S x.1:= by exact fun z ↦ IsLocalization.surj (Submonoid.closure M) z
    obtain⟨x, hx ⟩:= this s
    have: ∀ y :  (Submonoid.closure M), IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
    obtain ⟨ m, hm⟩ := IsUnit.exists_right_inv (this x.2)
    have hs': s= algebraMap R S x.1 * m:=by{
      calc s= s*1:= by exact (mul_one s).symm
        _=s*((algebraMap R S) ↑x.2 * m):= by rw[hm]
        _=(s*(algebraMap R S) ↑x.2)*m:= by rw[mul_assoc]
        _= algebraMap R S x.1 * m:= by rw[hx]
    }
    have: ((((f') ⁻¹' Q)))= {P:↑(⋂ r∈ M, positiveLocus (r*r))| (P: RealSpectrum R)∈  (positiveLocus (x.1*x.2))}:=by{
      ext P
      constructor
      · intro hP
        rw[hs.2.symm] at hP
        have hP: f' P ∈  positiveLocus s:= by exact hP
        by_contra hcon
        have hcon: - (x.1*x.2)∈ (P:RealSpectrum R).asCone.nonneg:= by exact not_not_mem.mp hcon
        have hcontra: - (algebraMap R S) x.1* ((algebraMap R S) x.2*m)*m∈ (f' P).asCone.nonneg:=by{
            use x.2
            use -(x.1*x.2)
            use m
            constructor
            · simp
              ring
            · constructor
              · exact hm
              · exact hcon
        }
        rw[hm] at hcontra
        simp at hcontra
        rw[hs'.symm] at hcontra
        exact hP hcontra
      · intro hP
        rw[hs.2.symm]
        suffices: f' P ∈ positiveLocus s
        exact this
        have: -s ∉ (f' P).asCone.nonneg:=by{
          by_contra hcon
          have: ∃ d :(Submonoid.closure M), (-x.1* (x.2:R))* (d*d)∈ (P: RealSpectrum R).asCone.nonneg:=by{
            apply Cone.toLocalization_mem_image (Submonoid.closure M) hLoc (P: RealSpectrum R) (-s) (-x.1,x.2)
            · simp
              exact hx
            · exact hcon
          }
          obtain⟨d, hd ⟩:= this
          obtain h1 | h2:=  (P: RealSpectrum R).IsPrime.2 hd
          · have: -x.1 * ↑x.2 ∉ (P: RealSpectrum R).asCone.nonneg:=by{
              have: -(x.1* (x.2:R))∉ (P: RealSpectrum R).asCone.nonneg:= by exact hP
              have hrw: -x.1 * ↑x.2=-(x.1* (x.2:R)):= by ring
              rw[hrw]
              exact this
            }
            exact this h1
          · have: (P: RealSpectrum R)∈ (⋂ r∈ (Submonoid.closure M), positiveLocus (r*r)):=by{
              rw[(RealSpectrum.inter_multClosure M).symm]
              exact Subtype.mem P
            }
            simp at this
            specialize this d (Subtype.mem d)
            exact this h2
        }
        exact this


    }
    rw[this]
    apply IsOpen.preimage continuous_subtype_val
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    exact mem_image_of_mem positiveLocus trivial
}

lemma RealSpectrum.comap_localization' [Algebra R S] (M : Set R) (hLoc: IsLocalization (Submonoid.closure M) S) (Q:RealSpectrum S): (comap (algebraMap R S)) Q ∈  (⋂ r∈ M, positiveLocus (r*r)):=by{
  simp
  by_contra hcon
  push_neg at hcon
  obtain ⟨m, hm1, hm2 ⟩:= hcon
  have hm2: - (m*m) ∈ ((comap (algebraMap R S)) Q ).asCone.nonneg:= by exact not_not_mem.mp hm2
  have hQ: (algebraMap R S) (- (m*m))∈ Q.asCone.nonneg:= by{
    exact hm2
  }
  have: ∃ n:(Submonoid.closure M), (n:R)=m:= by {
    have hm1: m ∈ (Submonoid.closure M):= by{
      apply Submonoid.subset_closure
      exact hm1
    }
    exact CanLift.prf m hm1
  }
  obtain⟨n, hn ⟩:= this
  have: ∀ y :  (Submonoid.closure M), IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
  obtain ⟨ m', hm'⟩ := IsUnit.exists_right_inv (this n)
  have: (algebraMap R S) (- (m*m))* (m'*m')∈ Q.asCone.nonneg:=by{
    apply Q.asCone.mul_nonneg
    · exact hQ
    · exact Q.asCone.square_nonneg m'
  }
  have hrw: (algebraMap R S) (- (m*m))* (m'*m')=-1:=by{
    simp
    calc (algebraMap R S) m * (algebraMap R S) m * (m' * m')=((algebraMap R S) m* m')*((algebraMap R S) m* m'):= by ring
      _=1*1:= by{
        rw[hn.symm]
        rw[hm']
      }
      _=1:= by simp
  }
  rw[hrw] at this
  exact Q.IsPrime.1 this
}



theorem RealSpectrum.localization_hoemo_subset [Algebra R S] (M : Set R) (hLoc: IsLocalization (Submonoid.closure M) S): (⋂ r∈ M, positiveLocus (r*r)) ≃ₜ  RealSpectrum S:=by{
  let f: (⋂ r∈ M, positiveLocus (r*r))→ RealSpectrum S:= fun y↦ (RealSpectrum.toLocalization M hLoc).toFun y
  let g: RealSpectrum S → (⋂ r∈ M, positiveLocus (r*r)):= fun y ↦  ⟨  ((comap (algebraMap R S)) y), (RealSpectrum.comap_localization' M hLoc y)⟩
  have hfcont: Continuous f:= by exact (toLocalization M hLoc).continuous_toFun
  have hgcont: Continuous g:=by{
    refine Continuous.subtype_mk ?h fun x ↦ comap_localization' M hLoc x
    exact (comap (algebraMap R S)).2
  }
  have hLI: LeftInverse f g:=by{
    intro P
    ext s
    constructor
    · intro hs
      obtain⟨m, r, m', h1, h2, h3 ⟩:= hs
      rw[h1]
      apply P.asCone.mul_nonneg
      · exact h3
      · exact  P.asCone.square_nonneg m'
    · intro hs
      have:  ∀ z : S, ∃ x : R × (Submonoid.closure M), z * algebraMap R S x.2 = algebraMap R S x.1:= by exact fun z ↦ IsLocalization.surj (Submonoid.closure M) z
      obtain ⟨x, hx ⟩:= this s
      use x.2
      use x.1*x.2
      have: ∀ y :  (Submonoid.closure M), IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
      obtain ⟨m', hm' ⟩:= IsUnit.exists_right_inv (this x.2)
      use m'
      have hs':s=(algebraMap R S) (x.1 * ↑x.2) * (m' * m'):=by{
        calc s= s*1*1:= by ring
          _=  s * ((algebraMap R S) (x.2:R) * m')* ((algebraMap R S) (x.2:R) * m'):= by rw[hm']
          _=((s* (algebraMap R S) (x.2:R))*(algebraMap R S) (x.2:R))*(m'*m'):= by ring
          _= ((algebraMap R S) (x.1)* (algebraMap R S) (x.2:R))*(m'*m'):= by rw[hx]
          _= (algebraMap R S) (x.1 * ↑x.2) * (m' * m'):=by simp
      }
      constructor
      · exact hs'
      · constructor
        · exact hm'
        · simp
          rw[hs'] at hs
          have: (algebraMap R S) (x.1 * ↑x.2) ∈ P.asCone.nonneg:=by{
            have : (algebraMap R S) (x.1 * ↑x.2)=((algebraMap R S) (x.1 * ↑x.2) *(m' * m'))*((algebraMap R S) ↑x.2* (algebraMap R S) ↑x.2):=by{
              calc (algebraMap R S) (x.1 * ↑x.2)= (algebraMap R S) (x.1 * ↑x.2)*1 *1:= by ring
                _= (algebraMap R S) (x.1 * ↑x.2) *((algebraMap R S) ↑x.2 * m')* ((algebraMap R S) ↑x.2 * m'):= by rw[hm']
                _= ((algebraMap R S) (x.1 * ↑x.2) *(m' * m'))*((algebraMap R S) ↑x.2* (algebraMap R S) ↑x.2):= by ring
            }
            rw[this]
            apply P.asCone.mul_nonneg
            · exact hs
            · exact P.asCone.square_nonneg ((algebraMap R S) (x.2:R))
          }
          exact this

  }
  have hRI: LeftInverse g f:=by{
    intro P
    ext r
    constructor
    · intro hr
      have hr: (algebraMap R S) r ∈ (f P).asCone.nonneg:= by exact hr
      have: ∃ d :(Submonoid.closure M), r* ((1 : (Submonoid.closure M)):R)* (d*d)∈ (P: RealSpectrum R).asCone.nonneg:=by{
        apply Cone.toLocalization_mem_image (Submonoid.closure M) (hLoc) (P: RealSpectrum R) ((algebraMap R S) r) (r,(1: (Submonoid.closure M)))
        · simp
        · exact hr
      }
      obtain ⟨d, hd ⟩:= this
      simp at hd
      have:  r∈ (P: RealSpectrum R).asCone.nonneg ∨ - ((d: R)*(d:R))∈  (P: RealSpectrum R).asCone.nonneg:= by {
        apply (P: RealSpectrum R).IsPrime.2
        exact hd
      }
      obtain h1 | h2:= this
      · exact h1
      · have:  (P: RealSpectrum R) ∈ ⋂ r∈ (Submonoid.closure M), positiveLocus (r*r):= by {
          rw[(RealSpectrum.inter_multClosure M).symm]
          exact Subtype.mem P
        }
        simp at this
        have : - ((d: R)*(d:R))∉ (P: RealSpectrum R).asCone.nonneg:=by{
          have hd: (d: R) ∈ Submonoid.closure M:= by exact SetLike.coe_mem d
          specialize this d hd
          exact this
        }
        exact (this h2).elim
    · intro hr
      suffices: (algebraMap R S) r ∈ (f P).asCone.nonneg
      exact this
      use 1
      use r
      use 1
      constructor
      · simp
      · constructor
        · simp
        · exact hr
  }
  let fhomeo: (⋂ r ∈ M, positiveLocus (r * r)) ≃ₜ RealSpectrum S:={
    toFun := f
    invFun := g
    left_inv := hRI
    right_inv := hLI
    continuous_toFun := hfcont
    continuous_invFun := hgcont
  }
  exact fhomeo


}

theorem RealSpetrum.QcOfInterSquares (M: Set R): CompactSpace (⋂ r∈ M, positiveLocus (r*r)) :=by{
  let S:= (Localization (Submonoid.closure M))
  have: (⋂ r∈ M, positiveLocus (r*r)) ≃ₜ  RealSpectrum S:=by{
    apply RealSpectrum.localization_hoemo_subset
    · exact Localization.isLocalization
  }
  have: RealSpectrum S  ≃ₜ (⋂ r∈ M, positiveLocus (r*r)):= by exact Homeomorph.symm this
  apply Homeomorph.compactSpace this

}

theorem RealSpetrum.QcOfInterSquares' (M: Set R): IsCompact (⋂ r∈ M, positiveLocus (r*r)) :=by{
  exact isCompact_iff_compactSpace.mpr (QcOfInterSquares M)
}

/-
To conclude the quasi-compactness of the elements of the subbase we can identify
an element of the base with a closed (clopen) subset of one of sets we showed to be
quasi-compact.
-/

noncomputable section
open Classical
theorem RealSpetrum.QcOfFinInter (M:Set R)(hM: Set.Finite M): IsCompact (⋂ r∈ M, positiveLocus (r)):=by{
  let SV:={f: M → R|(∀m:M,( f m=1 ∨ f m=-1))  ∧  ∃ m:M , f m = -1}
  by_cases hNonemp: Nonempty M
  · let U:= ⋃ f∈  SV, ⋂ m: M, positiveLocus (f (m) * m)
    apply isCompact_subset_compl_open (⋂ r∈ M, positiveLocus (r*r)) (⋂ r∈ M, positiveLocus (r)) U
    · refine isOpen_biUnion ?_
      intro f hf
      have hfmO: ∀ m:M, IsOpen ( positiveLocus (f (m) * m)):=by{
        intro m
        apply TopologicalSpace.isOpen_generateFrom_of_mem
        exact mem_image_of_mem positiveLocus trivial
      }
      have: Finite M:=by exact finite_coe_iff.mpr hM
      exact isOpen_iInter_of_finite hfmO
    · intro P hP
      simp
      intro m hm
      by_contra hcon
      have: (- m)*m∈ P.asCone.nonneg:=by{
        have: -(m*m) ∈ P.asCone.nonneg:= by exact not_not_mem.mp hcon
        simp
        exact this
      }
      simp at hP
      specialize hP m hm
      obtain h1| h2:= P.IsPrime.2 this
      · exact hP h1
      · exact hP h2
    · exact QcOfInterSquares' M
    · by_contra hcon
      have: Nonempty ((U ∩ ⋂ r ∈ M, positiveLocus r): Set (RealSpectrum R)):=by{
        exact nonempty_iff_ne_empty'.mpr hcon
      }
      obtain ⟨P, hP', hP ⟩:= this
      simp at hP'
      obtain⟨ f, hf1, hf2⟩ := hP'
      obtain⟨m, hm, hm2 ⟩:= hf1.2
      specialize hf2 m hm
      rw[hm2] at hf2
      simp at hP
      specialize hP m hm
      obtain h1 | h2:= Cone.prime_mem_r_or_mr P.asCone m P.IsPrime
      · have: - ((-1)* m)∉ P.asCone.nonneg:=by exact hf2
        simp at this
        exact this h1
      · exact hP h2
    · intro P hP
      simp at hP
      let f:M→ R:=fun m ↦ if (m:R) ∉ P.asCone.nonneg then (-1:R) else (1:R)
      by_cases hcases: ∀ m∈ M, m∈ P.asCone.nonneg
      · left
        simp
        intro m hm
        by_contra hcon
        have: (-m)*m∈ P.asCone.nonneg:=by{
          apply P.asCone.mul_nonneg
          · exact not_not_mem.mp hcon
          · exact hcases m hm
        }
        simp at this
        specialize hP m hm
        exact hP this
      · simp at hcases
        right
        simp
        use f
        constructor
        · constructor
          · intro m hm
            by_cases hcase: (m:R) ∉ P.asCone.nonneg
            · right
              exact if_pos hcase
            · left
              exact if_neg hcase
          · obtain⟨m ,hm1, hm2 ⟩:= hcases
            use m
            use hm1
            exact if_pos hm2
        · intro m hm
          by_cases hcase: (m:R) ∉ P.asCone.nonneg
          · simp
            rw[if_neg hcase]
            have: -(-m)=m:=by ring
            rw[this.symm] at hcase
            exact hcase
          · simp
            simp at hcase
            rw[if_pos hcase]
            by_contra hcon
            have: (-m)*m∈ P.asCone.nonneg:=by{
              apply P.asCone.mul_nonneg
              · exact not_not_mem.mp hcon
              · exact hcase
            }
            simp at this
            exact (hP m hm) this
  · have: M=∅:=by{
      exact not_nonempty_iff_eq_empty'.mp hNonemp
    }
    rw[this]
    simp
    exact isCompact_univ
}

/-
We are now able to combine all previous computations to deduce the quasi-compactness
of the topology base generated by the positive loci
-/

theorem RealSpectrum.baseOfQC: ∃ B: Set (Set (RealSpectrum R)), IsTopologicalBasis B ∧ (∀ O₁ ∈ B, ∀ O₂ ∈ B, O₁ ∩ O₂ ∈ B) ∧ ∀ O ∈ B, IsCompact O:=by{
    refine ⟨ _, TopologicalSpace.isTopologicalBasis_of_subbasis rfl, ?_⟩
    constructor
    · intro O₁ hO1 O₂ hO2
      refine
        (Set.mem_image (fun f ↦ ⋂₀ f) {f | Set.Finite f ∧ f ⊆ positiveLocus '' Set.univ}
              (O₁ ∩ O₂)).mpr
          ?left.left.a
      obtain ⟨f₁ , hf1 ⟩:= hO1
      obtain ⟨f₂ , hf2 ⟩:= hO2
      use f₁ ∪ f₂
      constructor
      · constructor
        · refine Set.finite_union.mpr ?h.left.left.a
          constructor
          · exact hf1.1.1
          · exact hf2.1.1
        · refine Set.union_subset_iff.mpr ?h.left.right.a
          constructor
          · exact hf1.1.2
          · exact hf2.1.2
      · rw[<- hf1.2, <- hf2.2]
        simp
        exact Set.sInter_union f₁ f₂
    · intro O hO
      obtain ⟨f, hf ⟩:= hO
      by_cases hNonEmptyR: Nonempty (R)
      · let posLoc':= Function.invFun (positiveLocus (R:=R))
        classical
        let M:= posLoc' '' f
        have hMfin: Set.Finite M:=by exact Finite.image posLoc' hf.1.1
        have hOM: O= ⋂ r∈ M, positiveLocus (r):=by{
          rw[hf.2.symm]
          simp
          ext P
          simp
          constructor
          · intro hP i hi
            have: positiveLocus (invFun positiveLocus i)=i:= by {
              apply invFun_eq
              have: i∈ positiveLocus '' univ:= by{
                apply hf.1.2
                exact hi
              }
              obtain ⟨a, ha ⟩:= this
              use a
              exact ha.2
            }
            rw[this]
            exact hP i hi
          · intro hP i hi
            have: positiveLocus (invFun positiveLocus i)=i:= by {
              apply invFun_eq
              have: i∈ positiveLocus '' univ:= by{
                apply hf.1.2
                exact hi
              }
              obtain ⟨a, ha ⟩:= this
              use a
              exact ha.2
            }
            rw[this.symm]
            exact hP i hi
        }
        rw[hOM]
        apply RealSpetrum.QcOfFinInter M hMfin
      · exact (hNonEmptyR AddTorsor.Nonempty).elim
}

--The following theorem shows that a prime cone is a generic point in the associated
--nonnegative locus

theorem RealSpectrum.closureOfPoint (P: RealSpectrum R): closure {P} = nonnegativeLocus (P.asCone.nonneg):=by{
  apply  subset_antisymm
  · apply closure_minimal
    · simp
      exact fun {a} ↦ mem_preimage.mp
    · exact isClosed_NN P.asCone.nonneg
  · intro Q hQ
    have hQ: P.asCone.nonneg⊆ Q.asCone.nonneg:= by exact hQ
    unfold closure
    simp
    intro A hAC hAP
    let U:= Aᶜ
    have hUO: IsOpen U:= by exact isOpen_compl_iff.mpr hAC
    have hUP: P ∉ U := by exact not_mem_compl_iff.mpr hAP
    obtain ⟨ S, hS1, hS2⟩ := IsTopologicalBasis.open_eq_sUnion (isTopologicalBasis_of_subbasis rfl) hUO
    rw[hS2] at hUP
    simp at hUP
    have hUQ: ∀ x ∈ S, Q ∉ x:=by{
      intro x hx
      specialize hUP x hx
      have : x ∈ (fun f ↦ ⋂₀ f) '' {f | Set.Finite f ∧ f ⊆ positiveLocus '' univ}:=by{
        apply hS1
        exact hx
      }
      obtain ⟨y, hy1, hy2 ⟩:= this
      rw[hy2.symm] at hUP
      rw[hy2.symm]
      simp
      simp at hUP
      obtain ⟨B, hB1, hB2 ⟩:= hUP
      use B
      constructor
      · exact hB1
      · have: B∈ positiveLocus '' univ:=by{
          apply hy1.2
          exact hB1
        }
        obtain ⟨r, hr ⟩:=this
        rw[hr.2.symm]
        have: -r ∈ P.asCone.nonneg:=by{
          rw[hr.2.symm] at hB2
          exact not_not_mem.mp hB2
        }
        by_contra hcon
        exact hcon (hQ this)
    }
    have: Q ∉ U:=by{
      rw[hS2]
      simp
      exact hUQ
    }
    exact not_not_mem.mp this
}
lemma nonnegativeLocus.antimono (I J: Set R) (hIJ: I⊆ J): nonnegativeLocus J⊆ nonnegativeLocus I:=by{
  intro P hP
  have: I⊆ P.asCone.nonneg:=by{
    exact Subset.trans hIJ hP
  }
  exact this
}

lemma nonnegativeLocus_GeneratedCone (I: Set R): nonnegativeLocus I= nonnegativeLocus (Cone.generated_by I).nonneg:=by{
  apply Subset.antisymm
  · intro P hP
    have hfinish: (Cone.generated_by I).nonneg ⊆ P.asCone.nonneg:=by{
      have: P.asCone.nonneg= (Cone.generated_by P.asCone.nonneg).nonneg:=by{
        exact (Cone.generated_by_cone P.asCone).symm
      }
      rw[this]
      apply Cone.generated_by_mono
      exact hP
    }
    exact hfinish
  · apply nonnegativeLocus.antimono
    exact Cone.generated_by.subset I
}


--The following lemma uses the choice theorem for closed, irreducible sets
--to conclude that they can be presented as the nonnegativelocus of a cone

lemma IrredClosed_exists_cone (V: Set (RealSpectrum R))(hIrred: IsIrreducible V) (hClosed: IsClosed V): ∃ C: Cone R, V= nonnegativeLocus C.nonneg:= by{
  rw[isIrreducible_iff_sUnion_closed] at hIrred
  have hB: ∃ B': Set (Set (RealSpectrum R)), B' ⊆ (positiveLocus '' Set.univ)  ∧ V=⋂₀ (compl '' B'):=by{
    apply IrredGenFromClosed
    · rfl
    · exact hClosed
    · intro V₁ hc hf hcov
      specialize hIrred (Set.Finite.toFinset hf)
      have help: ∃ z ∈ Finite.toFinset hf, V ⊆ z:=by{
        apply hIrred
        · intro z hz
          have: z ∈ V₁:=by exact (Finite.mem_toFinset hf).mp hz
          exact hc z this
        · simp
          exact Eq.subset hcov
      }
      obtain⟨ V', hV'1, hV'2⟩ := help
      use V'
      have : V'∈ V₁ := by exact (Finite.mem_toFinset hf).mp hV'1
      constructor
      · exact this
      · apply Subset.antisymm
        · exact hV'2
        · rw[hcov]
          exact subset_sUnion_of_mem this
  }
  obtain⟨B', hB' ⟩:= hB
  let I:=  positiveLocus ⁻¹' B'
  let J:={r | -r ∈ I}
  use (Cone.generated_by J)
  rw[(nonnegativeLocus_GeneratedCone J).symm]
  rw[RealSpectrum.nonnegativeLocus_inter J]
  rw[hB'.2]
  have:  ⋂ r:J, nonnegativeLocus {(r:R)}=  ⋂ r:J, (positiveLocus ((-r):R))ᶜ:=by{
    apply iInter_congr
    intro r
    exact positiveLocus_compl_nonnegativeLocus (r:R)
  }
  rw[this]
  ext P
  constructor
  · intro hP
    simp
    intro r hr
    simp at hP
    exact hP (positiveLocus (-r)) hr
  · intro hP
    simp
    simp at hP
    intro U hU
    have: U∈ positiveLocus '' univ:=by{
      apply hB'.1
      exact hU
    }
    obtain⟨r, hr ⟩:= this
    rw[hr.2.symm]
    specialize hP (-r)
    simp at hP
    rw[hr.2.symm] at hU
    exact hP hU
}

/-
Using the presentation of irreducible sets as nonnegative loci of cones we can
strengthen the statment to obtain a presentation as nonnegativ locus of a prime cone
In fact one can prove that {Irred Closed}={NN(P)| P prime cone}
-/

lemma IrredClosed_exists_primecone (V: Set (RealSpectrum R))(hIrred: IsIrreducible V) (hClosed: IsClosed V): ∃ P: RealSpectrum R, V= nonnegativeLocus P.asCone.nonneg:= by{
  let P: RealSpectrum R:={
    asCone := {
      nonneg := ⋂ Q∈ V, Q.asCone.nonneg
      add_nonneg := by{
        intro a b ha hb
        simp
        intro Q hQ
        simp at ha hb
        exact Q.asCone.add_nonneg (ha Q hQ) (hb Q hQ)
      }
      mul_nonneg := by{
        intro a b ha hb
        simp
        intro Q hQ
        simp at ha hb
        exact Q.asCone.mul_nonneg (ha Q hQ) (hb Q hQ)
      }
      square_nonneg := by{
        intro r
        simp
        intro Q h
        exact Q.asCone.square_nonneg r
      }
    }
    IsPrime := {
      proper := by{
        by_contra hcon
        have: V.Nonempty :=by exact IsIrreducible.nonempty hIrred
        obtain⟨Q', hQ ⟩:= this
        have: ⋂ Q∈ V, Q.asCone.nonneg⊆ Q'.asCone.nonneg:=by{
          exact iInter₂_subset Q' hQ
        }
        exact Q'.IsPrime.1 (this hcon)
      }
      mem_or_mem' := by{
        intro r s hrs
        simp at hrs
        simp
        have hirr: IsPreirreducible V:= by exact hIrred.2
        rw[isPreirreducible_iff_closed_union_closed ] at hirr
        specialize hirr (nonnegativeLocus {r}) (nonnegativeLocus {-s})
        have: V ⊆ nonnegativeLocus {r} ∨ V ⊆ nonnegativeLocus {-s}:=by{
          specialize hirr (RealSpectrum.isClosed_NN {r}) (RealSpectrum.isClosed_NN {-s})
          apply hirr
          intro Q hQ
          simp
          by_contra hcon
          push_neg at hcon
          have hcontra: (r*s)∉ Q.asCone.nonneg:=by{
            by_contra hdiction
            obtain h1| h2:= Q.IsPrime.2 hdiction
            · have: Q∈ nonnegativeLocus {r}:= by exact singleton_subset_iff.mpr h1
              exact hcon.1 this
            · have: Q∈ nonnegativeLocus {-s}:= by exact singleton_subset_iff.mpr h2
              exact hcon.2 this
          }
          exact hcontra (hrs Q hQ)
        }
        obtain h1 | h2:= this
        · left
          intro Q hQ
          exact h1 hQ rfl
        · right
          intro Q hQ
          exact h2 hQ rfl
      }
    }

  }
  use P
  apply Subset.antisymm
  · intro Q' hQ
    have: P.asCone.nonneg⊆ Q'.asCone.nonneg:=by{
      have: P.asCone.nonneg=⋂  Q∈ V, Q.asCone.nonneg:= by rfl
      rw[this]
      exact iInter₂_subset Q' hQ
    }
    exact this
  · obtain⟨C, hC ⟩:= IrredClosed_exists_cone V hIrred hClosed
    rw[hC]
    apply nonnegativeLocus.antimono
    intro r hr
    simp
    intro Q hQ
    rw[hC] at hQ
    have: C.nonneg⊆ Q.asCone.nonneg:= by exact hQ
    apply this
    exact hr
}
/-
Now we can combine all these results to conclude that the Real Spectrum is a spectral
space
-/

theorem RealSpectrum.isSpectral:  SpectralSpace ( RealSpectrum R):= by{
  rw[SpectralSpace_iff]
  constructor
  · exact baseOfQC
  · constructor
    · exact t0space
    · constructor
      · constructor
        intro V hIrred hClosed
        obtain ⟨P, hP ⟩:=  IrredClosed_exists_primecone V hIrred hClosed
        use P
        rw[hP]
        refine isGenericPoint_def.mpr ?h.a
        exact closureOfPoint P
      · exact _root_.compactSpace
}
