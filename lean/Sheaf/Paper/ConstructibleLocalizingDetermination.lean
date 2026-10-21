/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.LocalizingClosureExistence
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus

/-!
# Checking isomorphisms on constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-determination,
statement and proof (blueprint: sk-lem-sf-determination).

The functors are defined on the actual localizing full subcategories, with the
triangulations inherited from the unbounded derived categories of module objects.
No extension to the ambient derived categories is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The localizing full subcategory inherits its triangulation from the ambient
unbounded derived category. This is the triangulated-closure projection of
`localizingClosure_exists`, specialized to the recorded constructible finite-Tor
class; it introduces no new triangulation or assumption.

Source: blueprint main-20261015, sk-lem-sf-determination, proof step 1, using
sk-def-localizing-closure and det-def-localizing-closure-existence, clause 2
(blueprint: sk-lem-sf-determination). -/
instance localizingClosureProEtale_isTriangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (localizingClosureProEtale Λ X).IsTriangulated :=
  (localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X ⊓ fun K ↦
      DerivedCategory.finiteTorAmplitude _ K)).2.2.2.1.1

/-- A shift-compatible transformation between exact, coproduct-preserving functors
on the localizing categories is invertible everywhere if it is invertible on
bounded constructible finite-Tor complexes.

The generator hypothesis is expressed on objects of the source full subcategory:
every ambient generator belongs to that subcategory by the defining intersection.
The ambient derived categories use the recorded canonical Grothendieck-category
localizations in the fixed Hom universe.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-determination,
statement and proof (blueprint: sk-lem-sf-determination).

Proof:
1. Apply det-def-localizing-closure-existence to X and Y. Each ambient derived
category has small sums, and each localizing intersection is replete, triangulated,
and closed under ambient sums. Fullness restricts the coproduct universal property
and the distinguished triangles to these subcategories
(def-weil-triangulated-subcategory). The inherited triangulations are the ones
used here, and the index universe for small sums is `u + 1`.
2. Apply det-sf-determination-localizing to the restricted-domain functors.
Shift compatibility and the two-out-of-three lemma for distinguished triangles
make the isomorphism locus triangulated. Preservation of sums makes it closed
under sums; naturality conjugates components along isomorphisms, so it is replete.
It contains all constructible finite-Tor objects by hypothesis. Viewed in the
ambient source category, its triangles and sums are still those of the localizing
subcategory, hence the locus is one of the subcategories in the defining
intersection of sk-def-localizing-closure. Minimality makes it the whole source.
No extension of the functors to the ambient category is needed. -/
theorem isIso_app_of_constructibleFiniteTor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (X Y : Scheme.{u})
    (F₁ F₂ : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Y).FullSubcategory)
    [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₁.IsTriangulated] [F₂.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F₁]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F₂]
    (η : F₁ ⟶ F₂) [NatTrans.CommShift η ℤ]
    (hη : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      (constantModelBoundedConstructible Λ X K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) → IsIso (η.app K)) :
    ∀ K : (localizingClosureProEtale Λ X).FullSubcategory, IsIso (η.app K) := by
  sorry

end AlgebraicGeometry.ProEtale
