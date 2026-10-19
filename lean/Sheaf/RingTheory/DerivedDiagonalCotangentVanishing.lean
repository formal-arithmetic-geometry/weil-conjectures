/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Homology.Additive
import Sheaf.RingTheory.LocalizationCotangentVanishing
import Sheaf.RingTheory.CotangentFlatBaseChange

/-!
# The derived diagonal criterion for cotangent vanishing

Source: Stacks Project, Cotangent Complex, Tag 08R0, lemma-derived-diagonal
(blueprint: lem-trf-derived-diagonal-cotangent-vanishing).

The canonical multiplication is represented using any projective resolution of the
underlying A-module B. Extension of scalars followed by the ordinary adjunction counit
is the map b ⊗ p ↦ b ε(p), so its derived source is B ⊗ᴸ[A] B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

/-- The canonical derived multiplication B ⊗ᴸ[A] B → B[0], computed using a projective
resolution of B as an A-module. Apply B ⊗[A] - to the augmentation, identify its value
on the single complex with the single complex of its value, and apply the extension/
restriction adjunction counit. Finally extend degree n to cochain degree -n and localize.
Source: Stacks, Tag 08R0 (blueprint: lem-trf-derived-diagonal-cotangent-vanishing). -/
noncomputable def derivedDiagonalMultiplication
    {A B : CommRingCat.{u}}
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} B)] (f : A ⟶ B)
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B))) :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    (((ModuleCat.extendScalars f.hom).mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars f.hom)
        (ComplexShape.down ℕ) 0).hom.app _ ≫
      (ChainComplex.single₀ (ModuleCat.{u} B)).map
        ((ModuleCat.extendRestrictScalarsAdj f.hom).counit.app (ModuleCat.of B B)))
    ComplexShape.embeddingDownNat)

/-- If the canonical derived multiplication is an isomorphism, the standard cotangent
complex is a zero object in D(B). The projective resolution is arbitrary and is only a
representative for the canonical derived tensor product, with no flatness hypothesis
on B over A. Source: Stacks, Tag 08R0
(blueprint: lem-trf-derived-diagonal-cotangent-vanishing).

Proof: Apply lem-trf-cotangent-flat-base-change to the commutative square with both
maps out of A equal to f and both maps into the lower-right B equal to the identity.
Its canonical derived multiplication is precisely the assumed isomorphism. Base change
identifies L[B/A] ⊗ᴸ[B] B with L[B/B]. Extension of scalars along the identity is
naturally the exact identity functor, so this gives L[B/A] ≅ L[B/B]. Apply
lem-trf-localization-cotangent-vanishing with R = B and S = {1}. The localization is
canonically B, hence L[B/B] is zero. Transport zero-object vanishing across the displayed
isomorphism to conclude. Projective modules are flat; the nonpositive projective
resolution computes the derived tensor product in the hypothesis. -/
theorem derived_diagonal_cotangent_vanishing
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (C : Coherence.{u}) {A B : CommRingCat.{u}} (f : A ⟶ B)
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B)))
    (hμ : IsIso (derivedDiagonalMultiplication f P)) :
    IsZero (cotangentComplex C (Arrow.mk f)) := by
  sorry

end Algebra.CotangentResolution
