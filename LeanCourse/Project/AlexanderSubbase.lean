import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sober
import LeanCourse.Project.SpectralSpaces
import Mathlib.Algebra.Order.Ring.Cone
universe u v

variable {α: Type u}
open Topology
open TopologicalSpace
variable {X : Type*} [T: TopologicalSpace X]

open Ring
open Topology

/-
This file contains a proof of the Alexander subbase theorem used to deduce the
compactness of sets in a topological space whose topology is generated from a
subbase.
The first theorem and lemmas are just other versions of compactness equivalences.
The proof of the subbase theorem itself will rely on the ultrafilter lemma (not on AC).
-/

theorem isCompact_iff_finite_subfamily_closed' {K: Set X} :
    IsCompact K ↔ ∀ (I: Set (Set X)),
      (∀ A∈ I, IsClosed (A)) → (K ∩ ⋂₀ I = ∅) →
      ∃ t: Set (Set X) ,   t ⊆ I ∧ Set.Finite t ∧( K  ∩ ⋂₀ t) = ∅:= by{
        rw[isCompact_iff_finite_subfamily_closed]
        constructor
        · intro h C hC hC'
          rw[Set.sInter_eq_iInter] at hC'
          have help: (∀ (i : ↑C), IsClosed (↑i: Set X)):=by  {
            intro U
            specialize hC U
            apply hC
            exact Subtype.mem U
          }
          specialize h (fun U : C ↦ U)  help hC'
          obtain ⟨s, hs ⟩:= h
          use Subtype.val '' s.toSet
          constructor
          · exact Subtype.coe_image_subset C ↑s
          · constructor
            · apply Set.toFinite
            · rw[Set.sInter_eq_iInter]
              convert hs using 1
              ext x
              simp
        · intro h ι U hU hU'
          have hO:  (∀ U_1 ∈ {O | ∃ i, O = U i}, IsClosed U_1):=by {
            intro U_1 hU1
            obtain ⟨i, hi⟩:=hU1
            rw[hi]
            exact hU i
          }
          have hO': K ∩ ⋂₀ {O | ∃ i, O = U i}=∅ :=by {
            rw[<- hU']
            ext x
            constructor
            · intro hx
              constructor
              · exact hx.1
              · simp
                intro i
                have: x ∈ ⋂₀ {O | ∃ i, O = U i}:= by exact hx.2
                specialize this (U i)
                apply this
                use i
            · intro hx
              constructor
              · exact hx.1
              · simp
                have:x∈  ⋂ i, U i:= by exact hx.2
                simp at this
                exact this

          }
          obtain ⟨s, hs2, hs3, hs1 ⟩:= h {O : Set X| ∃ i : ι, O= U i} hO hO'
          let h:= Set.Finite.toFinset  hs3
          by_cases hNonEmptyiota: Nonempty ι
          · let V:= Function.invFun U
            classical
            let s':= h.image V
            use s'
            have hsub: K ∩ ⋂ i ∈ s', U i ⊆ ∅:= by{
              rw[hs1.symm]
              intro x hx
              constructor
              · exact hx.1
              · have hx2: x ∈ ⋂ i ∈ s', U i:= by exact hx.2
                simp
                intro t ht
                simp at hx2
                specialize hx2 t ht
                have: U (Function.invFun U t) =t:=by{
                  apply Function.invFun_eq
                  obtain⟨i, hi ⟩:=hs2 ht
                  use i
                  exact hi.symm
                }
                rw[this.symm]
                exact hx2
            }
            exact Set.subset_eq_empty hsub rfl
          · simp at hNonEmptyiota
            simp at hU'
            use ∅
            simp
            exact hU'
      }
lemma generateFrom_isOpen_elts (O: Set X)(B: Set (Set X))(hT: T = (TopologicalSpace.generateFrom B)) (hO: IsOpen O):
  ∀ x ∈ O, ∃ t ∈ (fun f => ⋂₀ f) '' { f : Set (Set X) | f.Finite ∧ f ⊆ B } , x ∈ t ∧ t ⊆ O :=by{

  let B':=(fun f => ⋂₀ f) '' { f : Set (Set X) | f.Finite ∧ f ⊆ B }
  have hBasis:  IsTopologicalBasis (B'):= by exact isTopologicalBasis_of_subbasis hT
  exact fun x a ↦ IsTopologicalBasis.exists_subset_of_mem_open hBasis a hO


}

theorem alexander_subbbase {K: Set X}(B: Set (Set X))(hT: T = (TopologicalSpace.generateFrom B))(hAlex: ∀ (C: Set (Set X)), (C ⊆ B) → (K ⊆ ⋃₀ C) → ∃ s: Set (Set X) , K ⊆ ⋃₀ s ∧ s⊆  C ∧ (Set.Finite s)):
    IsCompact K:= by{
      apply isCompact_iff_finite_subfamily_closed'.mpr
      intro I hClosed hInter
      by_contra hcon
      simp at hcon
      let F':={S: Set X| ∃ t : Set (Set X), t ⊆ I ∧ Set.Finite t ∧ K ∩ (⋂₀ t) ⊆ S}
      let F: Filter X  :={
        sets:= F'
        univ_sets :=by{
          use ∅
          simp
        }
        sets_of_superset:=by{
          intro A A' hA hAA'
          obtain ⟨t, ht1, ht2, ht3 ⟩ := hA
          use t
          constructor
          · exact ht1
          · constructor
            · exact ht2
            · exact Set.Subset.trans ht3 hAA'
        }
        inter_sets:= by{
          intro A A' hA hA'
          obtain ⟨t, ht1, ht2, ht3 ⟩:= hA
          obtain ⟨s, hs1, hs2,hs3 ⟩:= hA'
          use (t∪ s)
          constructor
          · exact Set.union_subset ht1 hs1
          · constructor
            · exact Set.Finite.union ht2 hs2
            · have: K ∩ ⋂₀ (t ∪ s)= (K ∩ ⋂₀ t) ∩ (K ∩ ⋂₀ s):= by{
                ext x
                constructor
                · intro hx
                  have hx2: x ∈ ⋂₀ (t ∪ s):= by exact hx.2
                  simp at hx2
                  constructor
                  · constructor
                    · exact hx.1
                    · simp
                      intro f hf
                      apply hx2 f
                      left
                      exact hf
                  · constructor
                    · exact hx.1
                    · simp
                      intro f hf
                      apply hx2 f
                      right
                      exact hf
                · intro hx
                  constructor
                  · exact hx.1.1
                  . simp
                    intro f hf
                    obtain hft | hfs := hf
                    · have hx2: x ∈ ⋂₀ t:= by exact hx.1.2
                      simp at hx2
                      apply hx2 f hft
                    · have hx2: x ∈ ⋂₀ s:= by exact hx.2.2
                      simp at hx2
                      apply hx2 f hfs
              }
              rw[this]
              exact Set.inter_subset_inter ht3 hs3
        }
      }
      have:  Filter.NeBot F:=by{
        by_contra hcontra
        have: ∅ ∈ F:= by{
          simp at hcontra
          exact Filter.empty_mem_iff_bot.mpr hcontra
        }
        obtain ⟨t, ht1, ht2, ht3 ⟩:= this
        have: K ∩ ⋂₀ t = ∅:= by exact Set.subset_eq_empty ht3 rfl
        exact hcon t ht1 ht2 this
      }
      have: ∃ U': Ultrafilter X, U' ≤ F :=by{
        apply Ultrafilter.exists_le
      }
      obtain ⟨U', hU' ⟩:= this
      let Bc:= Set.compl '' B
      have hNonEmpInter: ¬ (K∩ ⋂₀ (Bc ∩ U'.sets)=∅):= by{
        by_contra hcon
        let C:= Set.compl '' (Bc ∩ U'.sets)
        have: K⊆ ⋃₀ C:=by{
          intro x hx
          by_contra hcontra
          have: x ∈(⋃₀ C)ᶜ:=by exact hcontra
          have heq: (⋃₀ C)ᶜ = ⋂₀ (Bc ∩ U'.sets):=by{
            ext y
            constructor
            · intro hy
              simp
              intro O hO hOU'
              simp at hy
              specialize hy O hO hOU'
              exact Set.not_not_mem.mp hy
            · intro hy
              simp
              intro O hO hOU'
              simp at hy
              specialize hy O hO hOU'
              exact Set.not_not_mem.mpr hy
          }
          rw[heq] at this
          have: x∈  (K ∩ (⋂₀ (Bc ∩ U'.sets))):=by{
            constructor
            · exact hx
            · exact this
          }
          have hdiction: ¬ x ∈  (K∩ ⋂₀ (Bc ∩ U'.sets)):= by{
            rw[hcon]
            exact Set.not_mem_empty x
          }
          exact hdiction this

        }
        have h': C ⊆  B:=by{
          intro O hO
          obtain ⟨O', hO' ⟩:=hO
          obtain ⟨O'', hO'' ⟩:= hO'.1.1
          rw[hO'.2.symm, hO''.2.symm]
          have: Set.compl (Set.compl O'')= O'':=by{
            ext z
            constructor
            · intro hz
              exact Set.not_not_mem.mp hz
            · intro hz
              exact Set.not_not_mem.mpr hz
          }
          rw[this]
          exact hO''.1
        }
        obtain⟨s, hs1, hs2, hs3 ⟩:=  hAlex C h' this
        let t:= Set.compl '' s
        have: K ∩ (⋂₀ t)= ∅:=by{
          rw[<- Set.disjoint_iff_inter_eq_empty, <- Set.subset_compl_iff_disjoint_right]
          have heq: (⋂₀ t)ᶜ=⋃₀ s:=by{
            ext z
            constructor
            · intro hz
              simp at hz
              obtain⟨O, hO1, hO2 ⟩:= hz
              use O
              constructor
              · exact hO1
              · exact Set.not_not_mem.mp hO2
            · intro hz
              simp at hz
              simp
              obtain ⟨O, hO1, hO2 ⟩:= hz
              use O
              constructor
              · exact hO1
              · exact Set.not_not_mem.mpr hO2
          }
          rw[heq]
          exact hs1
        }
        have: ∅ ∈ U':=by{
          rw[<- this]
          apply Filter.inter_mem
          · suffices: K ∈ F
            exact hU' this
            use ∅
            constructor
            · exact Set.empty_subset I
            · constructor
              · exact Set.finite_empty
              · simp
                exact Eq.subset rfl
          · rw[Filter.sInter_mem ]
            · intro O hU
              obtain ⟨O', hO'1, hO'2 ⟩:= hU
              have: O' ∈ C:= by exact hs2 hO'1
              obtain⟨O'', hO'' ⟩:= this
              rw[hO'2.symm, hO''.2.symm]
              have: Set.compl (Set.compl O'')= O'':= by{
                ext z
                constructor
                · intro hz
                  exact Set.not_not_mem.mp hz
                · intro hz
                  exact Set.not_not_mem.mpr hz
              }
              rw[this]
              exact hO''.1.2
            · exact Set.Finite.image Set.compl hs3
        }
        have: ¬ Filter.NeBot (U': Filter X):= by{
          simp
          exact Filter.empty_mem_iff_bot.mp this
        }
        have hdiction: Filter.NeBot (U': Filter X):= by{
          exact (this (Ultrafilter.neBot U')).elim
        }
        exact this hdiction
      }
      have: Set.Nonempty (K ∩ ⋂₀ (Bc ∩ U'.sets)) :=by{
        exact Set.nmem_singleton_empty.mp hNonEmpInter
      }
      rw[Set.nonempty_def] at this
      obtain ⟨x, hx ⟩:= this
      have: K ⊆ ⋃₀ (Set.compl '' I):=by{
        rw[<- Set.disjoint_compl_right_iff_subset, Set.disjoint_iff_inter_eq_empty ]
        have:  (⋃₀ (Set.compl '' I))ᶜ= ⋂₀ I:=by{
          ext z
          constructor
          · intro hz
            simp at hz
            intro A hA
            specialize hz A hA
            exact Set.not_not_mem.mp hz
          · intro hz
            simp
            intro A hA
            specialize hz A hA
            exact Set.not_not_mem.mpr hz
        }
        rw[this]
        exact hInter
      }
      obtain⟨O, hO1, hO2 ⟩:= this hx.1
      have: IsOpen O:=by{
        obtain ⟨A, hA1, hA2 ⟩:= hO1
        have: IsClosed A:=by exact hClosed A hA1
        have hrw: Oᶜ  = A :=by exact compl_eq_comm.mpr hA2
        rw[<- isClosed_compl_iff, hrw]
        exact this
      }

      have: ∃ (s:Set (Set X)), s⊆ B ∧  Set.Finite s ∧ x∈ ⋂₀ s ∧ ⋂₀ s⊆ O:= by{
        rw[hT] at this
        have: ∀ x ∈ O, ∃ V ∈ (fun f => ⋂₀ f) '' { f : Set (Set X) | f.Finite ∧ f ⊆ B } , x ∈ V ∧ V ⊆ O :=by{
          apply generateFrom_isOpen_elts
          exact hT
          rw[hT.symm] at this
          exact this
        }
        specialize this x hO2
        obtain ⟨V', hV' ⟩:= this
        obtain ⟨s, hs1, hs2 ⟩:= hV'.1
        use s
        constructor
        · exact hs1.2
        · constructor
          · exact hs1.1
          · simp at hs2
            constructor
            · rw[hs2]
              exact hV'.2.1
            · rw[hs2]
              exact hV'.2.2
      }
      obtain⟨s, hs1, hs2, hs3, hs4 ⟩ := this
      have: ∀ V ∈ s, V ∈ U'.sets:=by{
        intro V hV
        obtain hV1 | hV2:= Ultrafilter.mem_or_compl_mem U' V
        · exact hV1
        · have hcontra: x ∈ Vᶜ :=by{
            have: Vᶜ ∈ (Bc ∩ U'.sets):=by{
              constructor
              · use V
                constructor
                · exact hs1 hV
                · exact rfl
              · exact hV2
            }
            apply hx.2
            exact this
          }

          exact (hcontra (hs3 V hV)).elim
      }
      have hcontra: ⋂₀ s∈ (U': Filter X):=by{
        rw[Filter.sInter_mem]
        intro V hV
        specialize this V hV
        exact this
        exact hs2
      }
      obtain ⟨C, hC1, hC2 ⟩:= hO1
      have hdiction: C ∈ (U': Filter X):=by{
        suffices: C∈ F
        exact hU' this
        use {C}
        constructor
        · exact Set.singleton_subset_iff.mpr hC1
        · constructor
          · exact Set.finite_singleton C
          · simp
      }
      have hcontradiction: ∅ ∈ (U': Filter X):=by{
        have :  (⋂₀ s ) ∩ C=∅:=by{
          rw[<- Set.disjoint_iff_inter_eq_empty,<- Set.subset_compl_iff_disjoint_right]
          have: Cᶜ =O:= by exact hC2
          rw[this]
          exact hs4
        }
        rw[this.symm]
        exact Filter.inter_mem hcontra hdiction
      }
      have: ¬ Filter.NeBot (U': Filter X):= by{
        simp
        exact Filter.empty_mem_iff_bot.mp hcontradiction
      }
      have hfinally: Filter.NeBot (U': Filter X):= by{
        exact (this (Ultrafilter.neBot U')).elim
      }
      exact this hfinally
  }
