import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sober

--We use the Bourbaki terminology of quasi compactness (q.c.) in our abbreviations even though Lean uses compact.
import LeanCourse.Common
open Topology
open TopologicalSpace
variable {X : Type*} [t: TopologicalSpace X]
universe u

/-
In this file we formalize the notion of a spectral space and give and equivalent characterization of it.
-/
-- we start by some elementary topology which wass not completely in the mathlib
theorem IsTopologyBasis.mono (B B' :Set ( Set X))(hB: (IsTopologicalBasis B)) (hBB': B ⊆ B' ) (hB': ∀ O: Set X, O ∈ B' → IsOpen O): IsTopologicalBasis B':=by{
  constructor
  · intro O₁ ho1 O₂ ho2 x hx
    have hO: IsOpen (O₁ ∩ O₂) :=by{
      exact IsOpen.inter (hB' O₁ ho1) (hB' O₂ ho2)
    }
    obtain ⟨O, ho⟩:=IsTopologicalBasis.exists_subset_of_mem_open hB hx hO
    use O
    constructor
    · exact hBB' ho.1
    · exact ho.2
  · have hsup: Set.univ  ⊆ ⋃₀ B':=by {
      calc Set.univ ⊆ ⋃₀ B:= by exact Set.univ_subset_iff.mpr hB.sUnion_eq
        _⊆ ⋃₀ B':= by exact Set.sUnion_mono hBB'
    }
    exact Set.univ_subset_iff.mp hsup
  · have help: t = generateFrom B:= by exact hB.eq_generateFrom
    have hsup: t ≤  generateFrom B':= by {
      apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
      exact hB'
    }
    have hsub': generateFrom B'≤ generateFrom B:= by {
      apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
      intro O hO
      have hfin: O ∈ B':= by exact hBB' hO
      exact TopologicalSpace.isOpen_generateFrom_of_mem hfin
    }
    have hsub: t ≥ generateFrom B':= by{
      calc t ≥  generateFrom B:= by exact Eq.le (id help.symm)
        _≥ generateFrom B':= by exact hsub'
    }
    exact le_antisymm hsup hsub
}

theorem isCompact_iff_finite_subcover'{K: Set X} :
    IsCompact K ↔ ∀ (C: Set (Set X)),
      (∀ U∈ C, IsOpen (U)) → (K ⊆ ⋃₀ C) → ∃ s: Set (Set X) , K ⊆ ⋃₀ s ∧ s⊆  C ∧ (Set.Finite s) := by{
        rw[isCompact_iff_finite_subcover]
        constructor
        · intro h C hC hC'
          rw[Set.sUnion_eq_iUnion] at hC'
          have help: (∀ (i : ↑C), IsOpen (↑i: Set X)):=by  {
            intro U
            specialize hC U
            apply hC
            exact Subtype.mem U
          }
          specialize h (fun U : C ↦ U)  help hC'
          obtain ⟨s, hs ⟩:= h
          use Subtype.val '' s.toSet
          constructor
          · rw[Set.sUnion_eq_iUnion]
            convert hs using 1
            ext x
            simp
          · constructor
            · exact Subtype.coe_image_subset C ↑s
            · apply Set.toFinite
        · intro h ι U hU hU'
          have hO:  (∀ U_1 ∈ {O | ∃ i, O = U i}, IsOpen U_1):=by {
            intro U_1 hU1
            obtain ⟨i, hi⟩:=hU1
            rw[hi]
            exact hU i
          }
          have hO': K ⊆ ⋃₀ {O | ∃ i, O = U i}:=by {
            intro x hx
            obtain ⟨i, hi ⟩:= Set.mem_iUnion.mp (hU' hx)
            apply Set.mem_sUnion.mpr
            use U i
            constructor
            · use i
            · exact hi
          }
          obtain ⟨s, hs ⟩:= h {O : Set X| ∃ i : ι, O= U i} hO hO'
          let h:= Set.Finite.toFinset  hs.2.2
          by_cases hNonEmptyiota: Nonempty ι
          · let V:= Function.invFun U
            classical
            let s':= h.image V
            use s'
            intro x hx
            obtain ⟨O , hO⟩:= hs.1 hx
            apply Set.mem_iUnion.mpr
            use Function.invFun U O
            simp
            constructor
            · use O
              constructor
              · exact hO.1
              · rfl
            · have hinvFun:  U (Function.invFun U O)=O :=by{
                apply Function.invFun_eq
                · obtain ⟨i, hi ⟩:= hs.2.1 hO.1
                  use i
                  symm
                  exact hi
              }
              rw[hinvFun]
              exact hO.2
          · simp at hNonEmptyiota
            simp at hU'
            use ∅
            simp
            exact hU'
      }
lemma isCompact_subset_compl_open (K: Set X)(K': Set X)(U: Set X)(hU: IsOpen U)(hKK': K'⊆K )(hK: IsCompact K) (hUK': U∩ K' =∅ )(hKUK': K⊆  K'∪ U): IsCompact K':=by{
  rw[isCompact_iff_finite_subcover']
  intro C hCO hC
  rw[isCompact_iff_finite_subcover'] at hK
  specialize hK (C∪{U})
  have: ∃ s, K ⊆ ⋃₀ s ∧ s ⊆ C ∪ {U} ∧ Set.Finite s:=by{
    apply hK
    · intro U' hU'
      simp at hU'
      obtain h1 | h2:= hU'
      · rw[h1]
        exact hU
      · specialize hCO U' h2
        exact hCO
    · have: K' ∪ U ⊆ ⋃₀ (C ∪ {U}):=by{
        have: ⋃₀ (C ∪ {U})= (⋃₀ (C)) ∪ U:= by {
          rw[Set.sUnion_union]
          have: ⋃₀ {U}=U:=by{
            exact Set.sUnion_singleton U
          }
          rw[this]
        }
        rw[this]
        exact Set.union_subset_union_left U hC
      }
      exact Set.Subset.trans hKUK' this
  }
  obtain⟨s, hs ⟩:= this
  use (s∩ C)
  constructor
  · intro x hx
    simp
    by_contra hcon
    simp at hcon
    have hcontra: x∈ U:=by{
      have: x∈ ⋃₀ s:=by{
        apply hs.1
        apply hKK'
        exact hx
      }
      simp at this
      obtain⟨t, ht ⟩:= this
      have: t=U:=by{
        have htC: ¬ t∈ C:=by{
          by_contra hcontra
          specialize hcon t ht.1 hcontra
          exact hcon ht.2
        }
        have: t∈ C∪ {U}:=by exact hs.2.1 ht.1
        simp at this
        obtain h1| h2:= this
        · exact h1
        · exact (htC h2).elim
      }
      rw[this.symm]
      exact ht.2
    }
    have: x∈ U∩ K':=by{
      exact Set.mem_inter hcontra hx
    }
    have:  ¬ U∩ K'= ∅:=by{
      intro f
      rw[f] at this
      exact this
    }
    exact this hUK'
  · constructor
    · exact Set.inter_subset_right s C
    · exact Set.Finite.inter_of_left hs.2.2 C

}
-- I recognized too late that the following lemma already exists
/-lemma IsTopologicalBasis.open_compact_eq_fin_iUnion {B : Set (Set X)} (hB : IsTopologicalBasis B) {O : Set X}
    (hou : IsOpen O) (hcomp: IsCompact O): ∃ (β : Type u_1), ∃ (α: Finset β) (f : α → Set X), (O = ⋃ i, f i) ∧ ∀ i, f i ∈ B:=by{
      obtain ⟨β, hbeta ⟩:= IsTopologicalBasis.open_eq_iUnion hB hou
      obtain ⟨V, hV ⟩:= hbeta
      have hFinCov: ∃ α: Finset β, O ⊆ ⋃ i ∈ α, V i :=by{
        rw[isCompact_iff_finite_subcover] at hcomp
        have hOpen: ∀ (i : β ), IsOpen (V i):= by{
          intro i
          have : V i ∈ B:= by exact hV.2 i
          exact IsTopologicalBasis.isOpen hB this
        }
        specialize hcomp V hOpen (Eq.subset hV.1)
        exact hcomp
      }
      obtain ⟨α, halpha ⟩:= hFinCov
      have hCov: O = ⋃ i ∈ α, V i:= by{
        have : ⋃ i ∈ α, V i ⊆ O:= by{
          calc ⋃ i ∈ α, V i ⊆ ⋃ i : β, V i:=by apply Set.iUnion₂_subset_iUnion
            _⊆ O := by exact Eq.subset (id hV.1.symm)
        }
        exact Set.Subset.antisymm halpha this
      }
      use β, α
      use ( V ∘ (fun (a : α) ↦ a) )
      simp
      constructor
      · rw[hCov]
        ext x
        constructor
        · intro hx
          simp at hx
          obtain ⟨i, hi ⟩:= hx
          simp
          use i
        · intro hx
          simp at hx
          obtain ⟨i, hi ⟩:= hx
          simp
          use i
      · intro i hi
        exact hV.2 i
    }-/


  lemma IsTopologicalBasis.open_compact_eq_fin_sUnion {B : Set (Set X)} (hB : IsTopologicalBasis B) {O : Set X}
    (hou : IsOpen O) (hcomp: IsCompact O): ∃ (F: Set (Set X)), (O = ⋃₀ F) ∧ F ⊆ B ∧ Set.Finite F:=by{
      obtain ⟨C, hC ⟩:= IsTopologicalBasis.open_eq_sUnion hB hou
      have hFinCov: ∃ F: Set (Set X), O ⊆ ⋃₀ F ∧ F ⊆ C ∧ Set.Finite F:=by{
        rw[isCompact_iff_finite_subcover'] at hcomp
        have hOpen: ∀ U ∈ C, IsOpen U:= by{
          intro U hU
          have : U ∈ B:= by exact hC.1 hU
          exact IsTopologicalBasis.isOpen hB this
        }
        specialize hcomp C hOpen (Eq.subset hC.2)
        obtain ⟨F, hF ⟩:= hcomp
        use F
      }
      obtain ⟨F, hF ⟩:=hFinCov
      use F
      constructor
      · have:  ⋃₀ F ⊆ O:=by{
          calc ⋃₀ F ⊆ ⋃₀ C:= by exact Set.sUnion_mono hF.2.1
            _⊆ O:= by exact Eq.subset hC.2.symm
        }
        exact Set.Subset.antisymm hF.1 this
      · constructor
        · calc F ⊆ C:= by exact hF.2.1
            _⊆ B:= by exact hC.1
        · exact hF.2.2
    }



lemma BaseOfQc_iff: (∃ (B:Set ( Set X)), (IsTopologicalBasis B) ∧ (∀ O₁∈ B, ∀ O₂ ∈ B, O₁ ∩ O₂ ∈ B)∧ (∀ O∈ B, IsCompact O))
 ↔ (IsTopologicalBasis {O : Set X| IsOpen O ∧ IsCompact O } ∧ (∀ O₁ ∈ {O: Set X | IsOpen O ∧ IsCompact O }, ∀ O₂ ∈{O: Set X| IsOpen O ∧ IsCompact O }, IsCompact (O₁ ∩ O₂))):= by{
  constructor
  · intro h
    obtain ⟨B, hb ⟩:= h
    constructor
    · apply IsTopologyBasis.mono
      · exact hb.1
      · intro O hO
        constructor
        · exact IsTopologicalBasis.isOpen hb.1 hO
        · exact hb.2.2 O hO
      · intro O hO
        exact hO.1
    · intro O₁ hO1 O₂ hO2
      have hCov1: ∃ (F: Set (Set X)), (O₁ = ⋃₀ F) ∧ F ⊆ B ∧ Set.Finite F:=by{
        apply IsTopologicalBasis.open_compact_eq_fin_sUnion
        · exact hb.1
        · exact hO1.1
        · exact hO1.2
      }
      have hCov2: ∃ (F: Set (Set X)), (O₂  = ⋃₀ F) ∧ F ⊆ B ∧ Set.Finite F:=by{
        apply IsTopologicalBasis.open_compact_eq_fin_sUnion
        · exact hb.1
        · exact hO2.1
        · exact hO2.2
      }
      obtain ⟨F₁, hF1 ⟩:=hCov1
      obtain ⟨  F₂, hF2⟩ := hCov2
      have hFin: Set.Finite (F₁  ×ˢ F₂) :=by {
        rw[Set.finite_prod]
        constructor
        · left
          exact hF1.2.2
        · left
          exact hF2.2.2
      }
      have hCov: O₁ ∩ O₂= ⋃₀ {U: Set X | ∃ O ∈ (F₁ ×ˢ F₂ ), U= O.1 ∩ O.2 }:=by{
        rw[hF2.1, hF1.1]
        simp
        ext x
        simp
        constructor
        · intro hx
          obtain⟨U₁, hU1 ⟩:= hx.1
          obtain⟨U₂, hU2 ⟩:= hx.2
          use (U₁ ∩ U₂)
          constructor
          · use U₁, U₂
            simp
            constructor
            · exact hU1.1
            · exact hU2.1
          · simp
            constructor
            · exact hU1.2
            · exact hU2.2
        · intro hx
          obtain ⟨U, hU ⟩:= hx
          obtain ⟨U₁,  U₂, hU1, hU2 ⟩:= hU.1
          constructor
          · use U₁
            constructor
            · exact hU1.1
            · have help: U ⊆  U₁:= by{
                rw[hU2]
                exact Set.inter_subset_left U₁ U₂
              }
              exact help hU.2
          · use U₂
            constructor
            · exact hU1.2
            · have help: U⊆ U₂:= by{
                rw[hU2]
                exact Set.inter_subset_right U₁ U₂
              }
              exact help hU.2
      }
      rw[hCov]
      have hFin': Set.Finite {U: Set X | ∃ O ∈ F₁ ×ˢ F₂, U = O.1 ∩ O.2}:=by{
        have : {U | ∃ O ∈ F₁ ×ˢ F₂, U = O.1 ∩ O.2}= ((fun (U : ( (Set X) × (Set X)))↦ (((U.1: Set X) ∩ (U.2: Set X))) ) '' (F₁ ×ˢ F₂)):= by{
          simp
          ext x
          constructor
          · intro hx
            obtain ⟨U₁, U₂, hU ⟩:= hx
            use (U₁, U₂)
            constructor
            · constructor
              · exact hU.1.1
              · exact hU.1.2
            · simp
              exact hU.2.symm
          · intro hx
            obtain ⟨U, hU ⟩:= hx
            use U.1, U.2
            constructor
            · have : U ∈ F₁ ×ˢ F₂:= by exact hU.1
              exact this
            · simp at hU
              exact hU.2.symm
        }
        rw[this]
        exact Set.Finite.image (fun U ↦ U.1 ∩ U.2) hFin
      }
      apply Set.Finite.isCompact_sUnion
      · exact hFin'
      · intro U hU
        obtain ⟨O, hO⟩:= hU
        rw[hO.2]
        have hO12B: O.1∈ B ∧ O.2 ∈B:= by{
          have : O.1∈ F₁ ∧ O.2 ∈ F₂:= by exact hO.1
          constructor
          · exact hF1.2.1 this.1
          · exact hF2.2.1 this.2
        }
        have :(∀ O₁ ∈ B, ∀ O₂ ∈ B, O₁ ∩ O₂ ∈ B):= by exact hb.2.1
        specialize this O.1 hO12B.1 O.2 hO12B.2
        apply hb.2.2
        exact this
  · intro h
    use {O | IsOpen O ∧ IsCompact O}
    constructor
    · exact h.1
    · constructor
      · intro O1 hO1 O2 hO2
        constructor
        · exact IsOpen.inter hO1.1 hO2.1
        · have help:  ∀ O₁ ∈ {O | IsOpen O ∧ IsCompact O}, ∀ O₂ ∈ {O | IsOpen O ∧ IsCompact O}, IsCompact (O₁ ∩ O₂):=by exact h.2
          specialize help O1 hO1 O2 hO2
          exact help
      · intro O hO
        exact hO.2
 }

noncomputable section
open Classical



@[mk_iff SpectralSpace_iff]
class SpectralSpace (X : Type*) [ TopologicalSpace X]: Prop where
  BasisOfQCOpens:   (∃ (B:Set ( Set X)), (IsTopologicalBasis B) ∧ (∀ O₁∈ B, ∀ O₂ ∈ B, O₁ ∩ O₂ ∈ B)∧ (∀ O∈ B, IsCompact O))
  T0: T0Space X
  sober:  QuasiSober X
  quasiCompact: CompactSpace X
