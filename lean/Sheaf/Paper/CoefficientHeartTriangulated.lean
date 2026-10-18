/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.PbcQbarStandardCohomology
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Bounded constructible field-coefficient complexes form a thick triangulated subcategory

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-coefficient-heart-ii,
`sk-cor-coefficient-heart-ii-triangulated.md`
(blueprint: det-cor-coefficient-heart-ii-triangulated).

The property is the recorded finite-constant-model notion, not the different upstream
stratified-local-finite-presentation property. The two coefficient choices carry their
canonical ring-object structures. The algebraic-closure coefficient has sections valued
in a finite subextension, as required by the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- On a Noetherian scheme, bounded constructible complexes over each finite extension
`E` of `ℚ_ℓ` and over the finite-subextension-valued condensed `ℚ̄_ℓ` form replete thick
triangulated full subcategories of the ambient derived categories of `Λ_X`-modules.
`IsTriangulated` includes zero, all integer shifts and extension closure; together with
isomorphism closure, rotation gives the two-out-of-three property for all distinguished
triangles. `IsStableUnderRetracts` is closure under direct summands, i.e. thickness.

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-coefficient-heart-ii,
`sk-cor-coefficient-heart-ii-triangulated.md`
(blueprint: det-cor-coefficient-heart-ii-triangulated).

Proof plan:
1. Work with the actual pulled-back ring `Λ_X` and its abelian module category, using
   def-weil-size-convention, def-weil-sheaf-of-modules-category and
   def-weil-derived-cohomology-sheaves. By det-def-sfb-constructible-tor-amplitude,
   membership means finite cohomological support and constructible cohomology. Zero has
   the zero finite constant model (det-def-sfb-constructible-local-model), with the empty
   stratification on an empty scheme. Cohomology preserves isomorphisms, so constructibility
   and finite support are invariant under isomorphism.
2. By lem-sp-derived-cohomology-shift, H^q(K[n]) is H^{q+n}(K). Translate the finite
   cohomological support by -n and transport the local models through this isomorphism.
   This gives all shifts, including +1 and -1.
3. For a distinguished triangle K → K' → K'' → K[1], apply
   lem-sf-derived-homology-long-exact in the category of def-weil-abstract-derived-category.
   If K and K' have finite supports S and S', the support of K'' lies in S' ∪ (S-1).
4. The five consecutive cohomology terms give
   0 → coker(H^q K → H^q K') → H^q K'' → ker(H^{q+1} K → H^{q+1} K') → 0.
   This uses the image/coimage identity in def-sp-abelian and lem-weil-pbc-coimage-mono.
   By det-lem-coefficient-heart-closure, the endpoints and then the middle term are
   constructible, for precisely the stated field coefficients and Noetherian base.
5. Rotate the triangle once or twice (def-weil-triangulated-category) to cover the
   other two choices of vertices; undo shifts by step 2. Zero, shifts and extension
   closure give def-weil-triangulated-subcategory in the ambient triangulated category.
6. If K is a retract of L, applying H^q gives maps a : H^q K → H^q L and b back with
   a ≫ b = 1. The first map identifies H^q K with ker(1 - b ≫ a), an endomorphism of
   the constructible H^q L. Kernel closure in det-lem-coefficient-heart-closure therefore
   gives constructibility. Vanishing for L forces vanishing for K, so its support stays
   finite. Thus retracts, and in particular direct summands, belong to the subcategory. -/
theorem constantModelBoundedConstructible_field_triangulated
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X
        ).IsClosedUnderIsomorphisms ∧
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X
        ).IsTriangulated ∧
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X
        ).IsStableUnderRetracts) ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X
      ).IsClosedUnderIsomorphisms ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X
      ).IsTriangulated ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X
      ).IsStableUnderRetracts := by
  sorry

end AlgebraicGeometry.ProEtale
