/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.AlgebraicGeometry.DerivedCategory
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Lifting quasi-coherent derived objects from a quasi-compact open

Source: Stacks Project, Tag 08EE, proof invoking Tag 08ED, lemma-lift-quasi-coherent
(blueprint: lem-sc-qc-open-derived-lift).
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Every quasi-coherent derived object on a quasi-compact open of an affine scheme
lifts to a quasi-coherent derived object on the scheme. Restriction is first to the
localized site and then transported by the canonical equivalence with the open's site.
Source: Stacks Project, Tag 08EE, proof invoking Tag 08ED, lemma-lift-quasi-coherent
(blueprint: lem-sc-qc-open-derived-lift).

Proof:
1. Write j : U → X for the open inclusion. A finite affine cover of U shows that j
   is quasi-compact: its intersections with affine opens of X are affine, since X
   is separated. Every open immersion is separated, hence j is quasi-separated.
2. Set E' = Rj_* E. By lem-pc-derived-direct-image-preserves-qcoh, its cohomology
   sheaves are quasi-coherent, so E' belongs to D_QCoh(O_X).
3. Apply lem-pc-restrict-derived-direct-image-open with f = j and V = U. The
   inverse image of U is U, and the induced map is the identity of U. This identifies
   the restriction of E' with R(id_U)_* E, which is E. -/
theorem exists_qc_derived_lift_of_isCompact_open
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory U.toScheme) :
    ∃ E' : schemeDerivedQCohCategory X,
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E'.obj ≅ E.obj) :=
  sorry

end AlgebraicGeometry
