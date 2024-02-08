import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sober


import LeanCourse.Common
open Topology
open TopologicalSpace
variable {X : Type*} [t: TopologicalSpace X]
universe u

/-
the following theorem is the missing part within the proof that the Real Spectrum is spectral
but it is a completely general statement on open irreducible sets in a topological
space whose topology is given by a subbase.
Here a short outline on how the proof can proceed:
U= ⋃ ⋂ B_i,j where the intersection is finite. One then chooses for every i some i_j
such that B_i,i_j⊆ U. Such i_j exsits as the right handside can be rewritten as
⋂ B_i,j ∪ ⋃ ⋂ B_i',j. where the outer intersection is finite and thus one can use the
irreducibility to obtain such i_j.
The collection of these B_i,i_j will then be the desired representation of U.
-/

theorem IrredGenFromOpen (B: Set (Set X))(hT: t = (TopologicalSpace.generateFrom B))(U: Set X)(hOpen: IsOpen U)(hCoIrred: ∀ V: Set (Set X),(∀ V'∈ V, IsOpen V')→ Set.Finite V→ U=⋂₀ V→ ∃ V'∈ V, U=V'): ∃ B': Set (Set X), B' ⊆ B ∧ U=⋃₀ B':=by{
  obtain ⟨ S, hS1, hS2⟩ := IsTopologicalBasis.open_eq_sUnion (isTopologicalBasis_of_subbasis hT) hOpen
  have hsOpen: ∀ s ∈ S, IsOpen s:=by {
    intro s hs
    have: s∈ (fun f ↦ ⋂₀ f) '' {f | Set.Finite f ∧ f ⊆ B}:=by{
      apply hS1
      exact hs
    }
    simp at this
    obtain ⟨f , hf ⟩:= this
    rw[hf.2.symm]
    apply Set.Finite.isOpen_sInter hf.1.1
    intro O hO
    have: O∈ B:=by{
      apply hf.1.2
      exact hO
    }
    rw[hT]
    exact TopologicalSpace.isOpen_generateFrom_of_mem this
  }
  have hNonemp: Nonempty { f : Set (Set X) | f.Finite ∧ f ⊆ B }:=by{
    use ∅
    constructor
    · exact Set.finite_empty
    · exact Set.empty_subset B
  }
  let Fin:= (fun f: { f : Set (Set X) | f.Finite ∧ f ⊆ B }  ↦ ⋂₀ (f:Set (Set X)))
  let D:= Function.invFun Fin
  have hSrw: U=⋃ s: S, Fin (D s):=by{
    rw[hS2]
    ext x
    constructor
    · intro hx
      simp at hx
      obtain⟨ s, hs⟩ := hx
      use s
      constructor
      · simp
        use s
        constructor
        · exact hs.1
        · have: Fin (D s)=s:=by{
            apply Function.invFun_eq
            have: s ∈ (fun f ↦ ⋂₀ f) '' {f | Set.Finite f ∧ f ⊆ B}:=by{
              apply hS1
              exact hs.1
            }
            simp at this
            obtain ⟨ s', hs'⟩ := this
            have: s' ∈ {f | Set.Finite f ∧ f ⊆ B}:=by{
              constructor
              · exact hs'.1.1
              · exact hs'.1.2
            }
            use ⟨s', this ⟩
            simp
            exact hs'.2

          }
          exact this
      · exact hs.2
    · intro hx
      simp at hx
      obtain⟨ s, hs⟩ := hx
      use s
      constructor
      · exact hs.1
      · sorry
  }
  let C:= ⋃ s': S, {C': Set (Set X) | C'⊆ (D s')∧ ∀O∈ C', U= ⋃ s: {s: S|s≠ s' }, s ∪ O}

  have hnonemC': ∀ C' :  C, Set.Nonempty (C': Set (Set X)):=by {
    intro C''
    obtain ⟨C', hC' ⟩:= C''
    simp
    obtain⟨S', hS'1, hS'2 ⟩:= hC'
    obtain⟨s', hs' ⟩:= hS'1
    simp at hs'
    let V:=⋃ O: (D (s'): Set (Set X)), {(⋃₀ {s: Set X | s∈ S ∧ s≠ s'}) ∪ O }
    specialize hCoIrred V
    have: (∀ V' ∈ V, IsOpen V'):=by{
      intro V' hV'
      simp at hV'
      obtain ⟨ O, hO1, hO2⟩:= hV'
      rw[hO2.symm]
      apply IsOpen.union
      · apply isOpen_sUnion
        intro s hs
        simp at hs
        apply hsOpen
        exact hs.1
      · have: (((Function.invFun (fun f ↦ ⋂₀ ↑f) ↑s')): Set (Set X)) ∈ { f : Set (Set X) | f.Finite ∧ f ⊆ B }:=by{
          sorry
        }
        simp at this
        have: O ∈ B:=by{
          apply this.2
          sorry
          -- apply hO1
        }
        rw[hT]
        exact TopologicalSpace.isOpen_generateFrom_of_mem this
    }
    specialize hCoIrred this
    have : Set.Finite V:=by{
      have: Finite ↑↑(D ↑s'):=by{
        have: Set.Finite ((D ↑s'): Set (Set X)):= by {
          obtain⟨f, hf ⟩:= D ↑s'
          simp
          exact hf.1
        }
        exact Set.finite_coe_iff.mpr this
      }
      apply Set.finite_iUnion
      intro O
      exact Set.finite_singleton (⋃₀ {s | s ∈ S ∧ s ≠ ↑s'} ∪ ↑O)
    }
    specialize hCoIrred this
    have : U = ⋂₀ V:=by{
      rw[hSrw]
      sorry
    }
    specialize hCoIrred this
    obtain ⟨V', hV'1, hV'2 ⟩ := hCoIrred
    simp at hV'1
    obtain ⟨A, hA ⟩:= hV'1
    use A
    rw[hs'.symm] at hS'2
    simp at hS'2
    sorry
  }
  let chosen: ∀ C': C, Set X := fun C'  ↦ (hnonemC' C' ).some
  have  hchosen: ∀ C': C, chosen C' ∈ (C': Set (Set X)):=by{
    exact fun C' ↦ Set.Nonempty.some_mem (hnonemC' C')
  }
  use (Set.range chosen)
  constructor
  · intro V hV
    obtain⟨C'', hC'' ⟩:= hV
    rw[hC''.symm]
    obtain⟨C', hC' ⟩:=C''
    obtain⟨S', hS' ⟩:= hC'
    sorry
  · sorry
}

--By Taking complements we get the analogue version for closed sets

lemma IrredGenFromClosed  (B: Set (Set X))(hT: t = (TopologicalSpace.generateFrom B))(C: Set X)(hClosed: IsClosed C)(hIrred: ∀ V: Set (Set X),(∀ V'∈ V, IsClosed V')→ Set.Finite V→ C=⋃₀ V→ ∃ V'∈ V, C=V'): ∃ B': Set (Set X), B' ⊆ B ∧ C=⋂₀ (compl '' B'):=by{
  let U:= Cᶜ
  have hU: ∃ B': Set (Set X), B' ⊆ B ∧ U=⋃₀ B':=by{
    apply IrredGenFromOpen
    · exact hT
    · exact isOpen_compl_iff.mpr hClosed
    · intro V hVO hVFin hVInter
      let W:= compl '' V
      have: ∃ W' ∈ W, C = W':=by{
        apply hIrred
        · intro W' hW'
          obtain ⟨V', hV' ⟩:= hW'
          rw[hV'.2.symm]
          simp
          exact hVO V' hV'.1
        · exact Set.Finite.image compl hVFin
        · have: compl C= compl (⋃₀ W):=by {
            simp
            simp at hVInter
            rw[hVInter]
            exact Set.sInter_eq_biInter
          }
          have : compl (compl C)= compl (compl (⋃₀ W)):= by exact congrArg compl this
          have hrw: (⋃₀ W)ᶜᶜ= (⋃₀ W):= by exact compl_compl (⋃₀ W)
          rw[hrw.symm, this.symm]
          exact eq_compl_comm.mpr rfl
      }
      obtain⟨ W', hW'1, hW'2⟩ := this
      use (compl W')
      constructor
      · exact (Set.mem_compl_image W' V).mp hW'1
      · rw[hW'2.symm]
  }
  obtain⟨ B', hB'1, hB'2⟩ := hU
  use B'
  constructor
  · exact hB'1
  · have: compl C= compl ( ⋂₀ (compl '' B')):= by{
      simp
      have: U= Cᶜ := by rfl
      rw[this.symm]
      rw[hB'2]
      exact Set.sUnion_eq_biUnion
    }
    have: compl (compl C)= compl (compl ( ⋂₀ (compl '' B'))):= by exact congrArg compl this
    have hrw:  ( ⋂₀ (compl '' B'))=compl (compl ( ⋂₀ (compl '' B'))):= by exact eq_compl_comm.mpr rfl
    rw[hrw, this.symm]
    exact eq_compl_comm.mpr rfl
}
