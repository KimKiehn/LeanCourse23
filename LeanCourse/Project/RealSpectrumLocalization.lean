import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sober
import LeanCourse.Project.SpectralSpaces
import LeanCourse.Project.Cone
import LeanCourse.Project.AlexanderSubbase
import Mathlib.Algebra.Order.Ring.Cone
import LeanCourse.Project.RealSpectrum
universe u v

variable {R : Type u}{S: Type v} [CommRing R][CommRing S]
variable {α: Type u}
variable [TopologicalSpace α] {X: Set α}

open Ring
open Topology
open Function Set Order
open TopologicalSpace

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

lemma Cone.toLocalization_isPrime_mem_or_mem' [Algebra R S] (M : Submonoid R) (hLoc: IsLocalization (M) S) (P: RealSpectrum R): ∀ {x y : S},(x * y)∈  (Cone.toLocalization M hLoc P.asCone).nonneg   →(x ∈ (Cone.toLocalization M hLoc P.asCone).nonneg  ) ∨ ((-y) ∈ (Cone.toLocalization M hLoc P.asCone).nonneg  ):=by{
    intro s s' hss'
    have:  ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1:= by exact fun z ↦ IsLocalization.surj M z
    obtain⟨ x, hx⟩ := this s
    obtain ⟨ y, hy⟩ := this s'
    have: ∀ y :  M, IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
    obtain ⟨ m, hm⟩ := IsUnit.exists_right_inv (this x.2)
    obtain ⟨ m', hm'⟩ := IsUnit.exists_right_inv (this y.2)
    obtain ⟨n , r, n', h ⟩:= hss'
    have this: ∃ c : M, ↑c * (x.1  *  y.1 * n * n) = ↑c * (↑y.2 *↑x.2* r):= by {
      have h1: (algebraMap R S) (x.1  *  y.1 * n * n) =(algebraMap R S) (↑y.2 *↑x.2* r):= by{
      symm
      calc (algebraMap R S) (↑y.2 * ↑x.2 * r)=   (algebraMap R S) ↑y.2  *(algebraMap R S) ↑x.2 * (algebraMap R S) r:= by{
          rw[(algebraMap R S).map_mul]
          rw[(algebraMap R S).map_mul]
        }
        _=(algebraMap R S) ↑y.2  *(algebraMap R S) ↑x.2 * (algebraMap R S) r *1 *1:= by ring
        _= (algebraMap R S) ↑y.2  *(algebraMap R S) ↑x.2 * (algebraMap R S) r *((algebraMap R S) ↑n * n')* ((algebraMap R S) ↑n * n'):= by rw[h.2.1]
        _= (algebraMap R S) ↑y.2  *(algebraMap R S) ↑x.2 * ((algebraMap R S) r *( n'* n'))* ((algebraMap R S) ↑n* (algebraMap R S) ↑n):= by ring
        _= (algebraMap R S) ↑y.2  *(algebraMap R S) ↑x.2 *(s*s')* (algebraMap R S) (n *n):= by rw[h.1, (algebraMap R S).map_mul ]
        _= (s* (algebraMap R S) ↑x.2)* (s'* (algebraMap R S) ↑y.2)* (algebraMap R S) (n *n):= by ring
        _= (algebraMap R S) ↑x.1 * (algebraMap R S) ↑y.1 * (algebraMap R S) (n *n):= by rw[hx, hy]
        _= (algebraMap R S) (x.1  *  y.1 * n * n):= by{
          simp
          ring
        }
      }
      exact (IsLocalization.eq_iff_exists M S).mp h1
    }
    obtain ⟨c, hc ⟩:= this
    have hc':(↑y.2 *↑x.2* ↑c) *( ↑c * (x.1  *  y.1 * n * n))=(↑y.2 *↑x.2* ↑c ) * (↑c * (↑y.2 *↑x.2* r)):=by exact congrArg (HMul.hMul ((y.2: R) *(x.2:R)* (c:R) )) hc
    have hP: (↑y.2 *↑x.2* ↑c) *( ↑c * (x.1  *  y.1 * n * n))∈ (P: RealSpectrum R).asCone.nonneg:=by{
      rw[hc']
      have: ↑y.2 * ↑x.2 * ↑c * (↑c * (↑y.2 * ↑x.2 * r))=(↑y.2* ↑y.2)*(↑x.2* ↑x.2)*(↑c* ↑c)* r:= by ring
      rw[this]
      apply (P: RealSpectrum R).asCone.mul_nonneg
      · apply (P: RealSpectrum R).asCone.mul_nonneg
        · apply (P: RealSpectrum R).asCone.mul_nonneg
          · exact (P: RealSpectrum R).asCone.square_nonneg (y.2: R)
          · exact (P: RealSpectrum R).asCone.square_nonneg (x.2: R)
        · exact (P: RealSpectrum R).asCone.square_nonneg (c: R)
      · exact h.2.2
    }
    have hPrim: (x.1*  ↑x.2 * ↑c * ↑c * ↑n * ↑n) ∈ (P: RealSpectrum R).asCone.nonneg ∨ -(y.1 * ↑y.2)∈ (P: RealSpectrum R).asCone.nonneg:=by{
      have: (↑y.2 *↑x.2* ↑c) *( ↑c * (x.1  *  y.1 * n * n))=(x.1*  ↑x.2 * ↑c * ↑c * ↑n * ↑n)*(y.1 * ↑y.2):= by ring
      rw[this] at hP
      apply (P: RealSpectrum R).IsPrime.2 hP
    }
    obtain h1 | h2:= hPrim
    · left
      use x.2 * c*n
      use x.1 * ↑x.2 * ↑c * ↑c * ↑n * ↑n
      have: ∀ y :  M, IsUnit (algebraMap R S y):= by exact fun y ↦ IsLocalization.map_units S y
      obtain ⟨ mm, hmm⟩ := IsUnit.exists_right_inv (this (x.2 * c*n))
      use mm
      constructor
      · have : x.1 * ↑x.2 * ↑c * ↑c * ↑n * ↑n= (x.1* ( ↑c* ↑n))* (↑x.2 * ↑c*↑n ):= by ring
        rw[this, (algebraMap R S).map_mul, mul_assoc]
        push_cast at hmm
        have: (algebraMap R S) (↑x.2 * ↑c * ↑n) * (mm * mm)=(algebraMap R S) (↑x.2 * ↑c * ↑n) * mm * mm:= by ring
        rw[this, hmm, (algebraMap R S).map_mul, mul_assoc ]
        have: (algebraMap R S) (↑c * ↑n) * (1 * mm)= m:=by{
          symm
          rw[mul_comm] at hm
          calc m= m*1:= by exact (mul_one m).symm
            _=m *((algebraMap R S) (↑x.2 * (↑c * ↑n)) * mm):= by{
                rw[hmm.symm]
                rw[mul_assoc]
              }

            _= m* ((algebraMap R S) ↑x.2 * (algebraMap R S) (↑c * ↑n) *mm):= by {
              rw[(algebraMap R S).map_mul]
            }
            _=m * (algebraMap R S) ↑x.2* (algebraMap R S) (↑c * ↑n) *mm:= by ring
            _= 1* (algebraMap R S) (↑c * ↑n) *mm:= by rw[hm]
            _= (algebraMap R S) (↑c * ↑n) * (1 * mm):=by ring
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

lemma Cone.toLocalization_isPrime [Algebra R S] (M : Set R) (hLoc: IsLocalization (Submonoid.closure M) S) (P: (⋂ r∈ M, positiveLocus (r*r))): Cone.IsPrime (Cone.toLocalization (Submonoid.closure M) hLoc (P: RealSpectrum R).asCone):= by{
  constructor
  · exact toLocalization_isPrime_mOne M hLoc P
  · exact fun {x y} a ↦ toLocalization_isPrime_mem_or_mem' (Submonoid.closure M) hLoc (↑P) a
}
def RealSpectrum.toLocalization [Algebra R S] (M : Set R) (hLoc: IsLocalization (Submonoid.closure M) S): C((⋂ r∈ M, positiveLocus (r*r)), RealSpectrum S) where
  toFun y := ⟨(Cone.toLocalization (Submonoid.closure M) hLoc (y: RealSpectrum R).asCone), Cone.toLocalization_isPrime M hLoc y  ⟩
  continuous_toFun := by{
    apply continuous_generateFrom
    intro Q hQ
    obtain⟨s, hs ⟩:= hQ
    have:  ∀ z : S, ∃ x : R × (Submonoid.closure M), z * algebraMap R S x.2 = algebraMap R S x.1:= by exact fun z ↦ IsLocalization.surj (Submonoid.closure M) z
    obtain⟨x, hx ⟩:= this s
    have: ((fun y ↦ { asCone := Cone.toLocalization (Submonoid.closure M) hLoc (y: RealSpectrum R).asCone, IsPrime := (_ : Cone.IsPrime (Cone.toLocalization (Submonoid.closure M) hLoc (y: RealSpectrum R).asCone)) }) ⁻¹' Q)= (positiveLocus ((x.1*x.1)*x.2))∩ (⋂ r∈ M, positiveLocus (r*r)):=by{
      ext P
      constructor
      · intro hP
        rw[hs.2.symm] at hP
        sorry
        sorry
      · sorry

    }
    have hOpen: IsOpen ( (positiveLocus ((x.1*x.1)*x.2))∩ (⋂ r∈ M, positiveLocus (r*r))):=by{
      have: IsOpen ((positiveLocus ((x.1*x.1)*x.2)): Set (RealSpectrum R)):=by{
        apply TopologicalSpace.isOpen_generateFrom_of_mem
        exact mem_image_of_mem positiveLocus trivial
      }
      sorry
    }

}
