import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sober
import LeanCourse.Project.SpectralSpaces
import LeanCourse.Project.Cone
import LeanCourse.Project.AlexanderSubbase
import Mathlib.Algebra.Order.Ring.Cone
universe u v

variable {R : Type u}{S: Type v} [CommRing R][CommRing S]
variable {α: Type u}
variable [TopologicalSpace α] {X: Set α}

open Ring
open Topology
open Function Set Order
open TopologicalSpace




-- The real spectum of a ring R is defined as the set of all primecones in R
@[ext]
structure RealSpectrum (R: Type u)[CommRing R] where
  asCone : Cone R
  IsPrime :Cone.IsPrime asCone



-- The real spectrum can naturally be endowed with a topology

def positiveLocus (s :  R) : Set (RealSpectrum R) :=
  { P | (-s)∉  P.asCone.nonneg  }


instance harrisonTopology : TopologicalSpace (RealSpectrum R) :=
  TopologicalSpace.generateFrom (positiveLocus '' Set.univ)



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


instance t0space: T0Space (RealSpectrum R) :=by{
  rw[t0Space_iff_not_inseparable]
  intro P Q hPQ
  have: P.asCone.nonneg ≠ Q.asCone.nonneg:=by{
    have: P.asCone≠  Q.asCone:=by{
      sorry
    }
    sorry
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



theorem RealSpectrum.isSpectral:  SpectralSpace ( RealSpectrum R):= by{
  rw[SpectralSpace_iff]
  constructor
  · refine ⟨ _, TopologicalSpace.isTopologicalBasis_of_subbasis rfl, ?_⟩
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

        sorry
      · sorry
  · constructor
    · exact t0space
    · constructor
      · sorry
      · exact _root_.compactSpace

}
