/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
import Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Supported maps are eventually killed by Koszul augmentations

Source: Stacks Project, Tags 08DC, 08DD and 09IR.
(blueprint: lem-pc-koszul-supported-augmentation-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A map from a shifted structure object into an object supported on the complement
of the finite principal open is killed by an augmentation in the Koszul power system.
No orthogonality hypothesis is made.
Source: Stacks Project, Equation 36.9.4.1, Tag 08DC; Proposition 36.9.5, Tag 08DD;
Lemma 36.15.2, Tag 09IR, reduction to an object restricting to zero.
(blueprint: lem-pc-koszul-supported-augmentation-vanishing).

Proof: Move the shift on the source to the inverse shift on the target. This shifted
object still has quasi-coherent cohomology and restricts to zero. Apply the canonical
colimit comparison of `affine_perfect_open_represent_cohomology` to it. At index zero,
precompose the given map with the augmentation. Its image in the colimit is zero:
the comparison is restriction followed by the inverse restricted augmentation,
and restriction of the target is zero. Equality in this filtered colimit of Hom
sets is witnessed at some later index b. The transition maps preserve zero, and
compatibility of the augmentations identifies the transitioned map with
precomposition by the b-th augmentation. Move the target shift back to the source.
For arbitrary localization universes, choose the standard localizations while applying
the comparison theorem and transport the complexes and maps using the canonical
localization equivalences. The derived restrictions commute with this transport
because both are induced by the same restriction on complexes. Transport restriction
to the scheme of the open by `Scheme.Modules.overEquiv`; that equivalence preserves
zero. This supplies the extra localizations required by the comparison theorem
without adding assumptions to the assertion. If r = 0, the tail complex is zero,
so every augmentation already kills the map. The zero ring and E = 0 give zero
Hom groups. The argument requires no regularity or nonzero hypothesis on f. -/
theorem koszul_supported_augmentation_eventually_zero
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (hres : IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E.obj))
    (n : ℤ) (φ : (koszulOpenStructure A)⟦n⟧ ⟶ E.obj) :
    ∃ e : ℕ, (koszulOpenUnit A r f e)⟦n⟧' ≫ φ = 0 := by
  sorry

end AlgebraicGeometry
