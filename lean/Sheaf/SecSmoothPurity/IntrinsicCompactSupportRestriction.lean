/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Intrinsic compact-support restriction of scalars

Source: Stacks Project, Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).

The open comparison is the published section-normalized intrinsic comparison.
The proper comparison is the inverse of the published K-injective-normalized ring-sheaf
comparison. Their composite acts on exactly the compact-support functors used by b.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The specified compact-support restriction comparison on intrinsic constant-ring modules.
Source: Stacks Tags 03DI and 0D6E
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
def intrinsicCompactSupportRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (h : Z ⟶ Y) :
    scalarRestriction φ X ⋙ reductionCompactSupport A j h ≅
      reductionCompactSupport B j h ⋙ scalarRestriction φ Y :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ))
      (directImageConstantPush A h) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero j B).mapDerivedCategory
      (proEtaleRingRestrictionDerivedDirectImage h
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
        (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
        (proEtaleConstantInverseImageMap_naturality h
          (CommRingCat.ofHom (RingHom.ulift φ))).symm).symm

/-- Restriction comparisons compose along coefficient maps, with the termwise scalar
restriction associator. Source: Stacks Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: the open comparison preserves the underlying extension-by-zero sections, so
its two composites agree on those sections. For the proper comparison take a
K-injective representative and successive K-injective resolutions of its restrictions.
Both composites are the inverse of the same direct-image resolution roof by the
normalization of proEtaleRingRestrictionDerivedDirectImage. Naturality and localization
extend the equality to every object. Whisker the open equality by proper direct image,
whisker the proper equality by open extension, and compose them. -/
theorem intrinsicCompactSupportRestriction_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : Γ(Y, ⊤)))
    (c : Compactification f) (L : proEtaleDerivedCategory X C) :
    (reductionCompactSupport A c.i c.g).map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app L) ≫
      (intrinsicCompactSupportRestriction (ψ.comp φ) c.i c.g).hom.app L =
    (intrinsicCompactSupportRestriction φ c.i c.g).hom.app
        ((scalarRestriction ψ X).obj L) ≫
      (scalarRestriction φ Y).map
        ((intrinsicCompactSupportRestriction ψ c.i c.g).hom.app L) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((reductionCompactSupport C c.i c.g).obj L) := by
  sorry

end AlgebraicGeometry.ProEtale
