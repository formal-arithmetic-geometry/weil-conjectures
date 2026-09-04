/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# `Spec` of a restriction map and the canonical isomorphisms of affine opens

We record that `Spec` of a restriction map between affine opens intertwines the canonical
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, and that the algebra map
realizing `Γ(X, X.basicOpen f)` as a localization is the restriction map of the structure
sheaf.

We also record that an open of an affine scheme is covered by finitely many basic opens
as soon as it is quasi-compact (`AlgebraicGeometry.exists_finite_basicOpen_cover`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Spec` of a restriction map intertwines the canonical isomorphisms
`Spec Γ(X, U) ≅ U` with the inclusion of opens. -/
lemma specMap_res_isoSpec_inv {U V : X.affineOpens} (hUV : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hUV).op) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ X.homOfLE hUV := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι,
    V.2.map_fromSpec U.2 (homOfLE (X := X.Opens) hUV).op]

/-- The algebra map exhibiting the sections over a basic open as a localization is the
restriction map of the structure sheaf. -/
lemma algebraMap_basicOpen_eq {U : X.Opens} (f : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

/-- A quasi-compact open of an affine scheme is a finite union of basic opens. -/
lemma exists_finite_basicOpen_cover [IsAffine X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → Γ(X, ⊤)) (_ : ∀ i, X.basicOpen (u i) ≤ U),
      U = ⨆ i, X.basicOpen (u i) := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} ↦ (X.basicOpen a.1 : Set X))
    (fun a ↦ (X.basicOpen a.1).2) (by
      intro x hx
      obtain ⟨a, ha1, ha2⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
      exact Set.mem_iUnion.mpr ⟨⟨a, ha1⟩, ha2⟩)
  refine ⟨{a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} // a ∈ t}, inferInstance,
    fun a ↦ a.1.1, fun a ↦ a.1.2, le_antisymm ?_ (iSup_le fun a ↦ a.1.2)⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

end AlgebraicGeometry
