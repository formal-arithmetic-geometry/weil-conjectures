/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.GDelta.Basic
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension drop for nowhere-dense closed subsets

Source: Stacks Project, Tag 02P2, the nowhere-dense closed support and the finite-dimensional
Noetherian dimension argument (blueprint: lem-sc-hilbert-nowhere-dense-dimension-drop).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A nowhere-dense closed subset of a nonempty locally Noetherian scheme of finite
Krull dimension `d` has Krull dimension strictly less than `d`.
Source: Stacks Project, Tag 02P2, dimension argument for the nowhere-dense closed support
(blueprint: lem-sc-hilbert-nowhere-dense-dimension-drop).

Proof:
1. For each point `w` of `Z`, choose an affine open neighbourhood `U`. Its coordinate
ring is Noetherian, so its underlying space is Noetherian. Let `C` be an irreducible
component of `U` containing `w`, and let `η` be its generic point.
2. If `η` lies in `Z`, closedness implies that all of `C` lies in the inverse image of
`Z`. A Noetherian irreducible component contains a nonempty open of `U` (Stacks, Tag
0052 (3)). Its image is a nonempty open of `X` contained in `Z`, contradicting nowhere
density. Thus `η` is a generalization of `w` outside `Z`.
3. Apply the proved source-library theorem
`topologicalKrullDim_lt_of_forall_exists_specializes` with ambient closed subset `X`.
It extends a specialization chain in `Z` by an outside generalization. The equality
`dim X = d` supplies `dim X < d + 1`, so `dim Z < d`. The same chain argument handles
the empty case and `d = 0` without any separate nonemptiness assumption on `Z`.
-/
theorem Scheme.topologicalKrullDim_lt_of_isNowhereDense
    (X : Scheme.{u}) [Nonempty X] [IsLocallyNoetherian X]
    (d : ℕ) (hX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (Z : Set X) (hZ : IsClosed Z) (hnow : IsNowhereDense Z) :
    topologicalKrullDim Z < (d : WithBot ℕ∞) := by
  apply topologicalKrullDim_lt_of_forall_exists_specializes
    (Z := Set.univ) isClosed_univ hZ (Set.subset_univ Z)
  · intro w _
    obtain ⟨U, hU, hwU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := w)
      (by trivial)
    let : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hnoeth : TopologicalSpace.NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
    let : QuasiSober U := U.isOpenEmbedding'.quasiSober
    let w' : U := ⟨w, hwU⟩
    let C := irreducibleComponent w'
    have hC : C ∈ irreducibleComponents U :=
      irreducibleComponent_mem_irreducibleComponents w'
    have hgen := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    refine ⟨(hC.1.genericPoint : U).1, Set.mem_univ _,
      Topology.IsInducing.subtypeVal.specializes_iff.mpr
        (hgen.specializes (mem_irreducibleComponent (x := w'))), ?_⟩
    intro hη
    have hCZ : C ⊆ (Subtype.val : U → X) ⁻¹' Z := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hη)
        (hZ.preimage continuous_subtype_val)
    obtain ⟨O, hO, ⟨b, hbO⟩, hOC⟩ :=
      @TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
        (U : Set X) _ hnoeth C hC
    have hopen : IsOpen ((Subtype.val : U → X) '' O) :=
      U.isOpenEmbedding'.isOpenMap _ hO
    have hsub : (Subtype.val : U → X) '' O ⊆ Z := by
      rintro _ ⟨x, hx, rfl⟩
      exact hCZ (hOC hx)
    have hb : (b : X) ∈ interior Z :=
      interior_mono hsub (by rw [hopen.interior_eq]; exact ⟨b, hbO, rfl⟩)
    rw [hZ.isNowhereDense_iff.mp hnow] at hb
    exact hb
  · have hd : topologicalKrullDim X < (d : WithBot ℕ∞) + 1 := by
      rw [hX]
      exact_mod_cast Nat.lt_succ_self d
    exact (topologicalKrullDim_subspace_le X Set.univ).trans_lt hd

end AlgebraicGeometry
