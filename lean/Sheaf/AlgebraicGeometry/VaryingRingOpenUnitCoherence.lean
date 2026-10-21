/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOperations
import Sheaf.SixFunctors.OpenTensorNormalizationData
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Identity coherence for varying-ring open extension

Source: Stacks Project, Tag 03DI, `lemma-extension-by-zero`, for the ordinary
open adjunction; its identity normalization and exact localization are additional
categorical calculations (blueprint: lem-sp-varying-ring-open-unit-coherence).

The identity chosen by the derived open adjunction agrees with the localization of
its ordinary unit-preserving identity. The open compositor at two identities is
outer whiskering of that same identity, after equality transport.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.VaryingRing

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory

/-- Exact localization and the identity unit law for open extension on arbitrary
varying-ring systems. Source: Stacks Project, Tag 03DI, `lemma-extension-by-zero`,
for the ordinary adjunction; the following normalization argument is categorical
(blueprint: lem-sp-varying-ring-open-unit-coherence).

Proof plan:
1. Let `L = pull R φ (𝟙 X)` and `B = extension R φ (𝟙 X)`. Their ordinary
   identity comparisons are the unit-preserving left-adjoint comparisons displayed
   below. The exact-derived adjunction localizes the ordinary unit, and `gId` is
   the localization of the ordinary inverse-image identity followed by the exact
   derived identity comparison. The conjugate-unit equation characterizes the
   ordinary open identity `b` by `L(b_M) ∘ η_M = e_M⁻¹`.
2. Apply exact-derived transformation pasting to this equation. The localization
   `h = D(b)` followed by the exact-derived identity satisfies the same derived
   unit equation as `jId`; uniqueness of the conjugate comparison gives `jId = h`.
3. Transport the ordinary inverse-image compositor at two identities to `L → LL`.
   Inverse-image unit coherence identifies it with `e_L⁻¹`. The composite open
   adjunction has unit `L(η_B) ∘ η`; its conjugate-unit equation characterizes the
   ordinary open compositor `k : BB → B`.
4. Naturality of `η` at `b_M`, the equation from step 1, and naturality of `e` at
   `η_M` show that `B(b_M)` satisfies precisely that equation. Uniqueness gives
   `k = B(b)` as natural transformations.
5. Exact-derived transformation pasting localizes this equality with the specified
   exact-composition and identity comparisons. The localized compositor is the
   chosen `jComp`, since both preserve the localized units. Substitute `h = jId`
   from step 2. This holds on the entire unbounded derived category, without any
   flatness, boundedness, finiteness, or coefficient-evaluation assumption. -/
theorem open_unit_coherence
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    (X : Scheme.{u}) :
    (jId R φ X).hom =
      (Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso (moduleJAdj R φ (𝟙 X))
          (Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X))) ≪≫
        Functor.mapDerivedCategoryIdIso (Modules R φ X)).hom ∧
    (jComp R φ (𝟙 X) (𝟙 X)).hom ≫
        (eqToHom (by simp only [Category.id_comp]) :
          J R φ ((𝟙 X) ≫ (𝟙 X)) ⟶ J R φ (𝟙 X)) =
      Functor.whiskerLeft (J R φ (𝟙 X)) (jId R φ X).hom := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
