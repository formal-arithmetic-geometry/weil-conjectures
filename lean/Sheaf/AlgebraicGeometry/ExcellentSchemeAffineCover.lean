/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.GRingAffineCover
import Sheaf.AlgebraicGeometry.JTwoAffineCover
import Sheaf.AlgebraicGeometry.UniversallyCatenaryAffineCover
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Excellence detected on affine open covers

Source: Stacks Project, Morphisms, Tag 0HAB (blueprint: lem-trf-excellent-scheme-affine-cover).
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u v

set_option autoImplicit false

/-- Excellence of affine coordinate rings descends from an affine open cover.

Source: Stacks Project, Morphisms, Tag 0HAB, implication (3) implies (2) and final
assertion (blueprint: lem-trf-excellent-scheme-affine-cover).

The proof first obtains local Noetherianity from the excellent chart rings. It then applies
locality of the G-ring, J-2, and universally catenary conditions on affine opens, and
recombines these conditions with the definition of excellence. For an open subscheme,
the affine-open basis supplies a cover and restriction identifies its section rings with
those on the ambient scheme. -/
theorem isExcellent_of_affine_open_cover
    {X : Scheme.{u}} {I : Type v} (U : I → X.Opens)
    (hcover : TopologicalSpace.IsOpenCover U)
    (haff : ∀ i : I, IsAffineOpen (U i))
    (hexc : ∀ i : I, IsExcellent Γ(X, U i)) :
    (∀ V : X.Opens, IsAffineOpen V → IsExcellent Γ(X, V)) ∧
      (∀ W : X.Opens,
        ∀ V : (W.toScheme).affineOpens, IsExcellent Γ(W.toScheme, V)) := by
  let A : I → X.affineOpens := fun i ↦ ⟨U i, haff i⟩
  have hA : ⨆ i, (A i : X.Opens) = ⊤ := hcover.iSup_eq_top
  have : IsLocallyNoetherian X :=
    isLocallyNoetherian_of_affine_cover hA (fun i ↦ (hexc i).1.1)
  have hG := isGRing_of_affine_open_cover A hA (fun i ↦ (hexc i).1.2.1)
  have hJ := j2_of_affine_open_cover X I A hA (fun i ↦ (hexc i).1.2.2)
  -- The range of the cover is small even when its original index type is not.
  have hRange : ⨆ j : Set.range U, (j : X.Opens) = ⊤ := by
    exact (iSup_range' (fun V : X.Opens ↦ V) U).trans hcover.iSup_eq_top
  have hRangeAff : ∀ j : Set.range U, IsAffineOpen (j : X.Opens) := by
    rintro ⟨_, i, rfl⟩
    exact haff i
  have hRangeCat : ∀ j : Set.range U, IsUniversallyCatenary Γ(X, (j : X.Opens)) := by
    rintro ⟨_, i, rfl⟩
    exact (hexc i).2
  have hC := universallyCatenary_of_affineOpenCover X
    (fun j : Set.range U ↦ (j : X.Opens)) hRangeAff hRange hRangeCat
  have hAll : ∀ V : X.Opens, IsAffineOpen V → IsExcellent Γ(X, V) := by
    intro V hV
    exact ⟨⟨(hG ⟨V, hV⟩).1, hG ⟨V, hV⟩, hJ ⟨V, hV⟩⟩, hC V hV⟩
  refine ⟨hAll, ?_⟩
  intro W V
  exact hAll (W.ι ''ᵁ (V : W.toScheme.Opens))
    (V.property.image_of_isOpenImmersion W.ι)

end AlgebraicGeometry
