/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # Bounded-below compatibility of the normalized open compositor

Source: finite dualizing proof, paragraph 2, open-locality sentence.
(blueprint: lem-coef-dualizing-open-compositor-plus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Normalize compact support along an open immersion using exactly (j, identity).
Source: the open-candidate clause of lem-coef-finite-dualizing, paragraph 2
(blueprint: lem-coef-dualizing-open-adjoint). -/
def coefDualizingOpenNormalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} R) j ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  (rightDerivedLowerShriekIso R (Compactification.ofIsOpenImmersion j)).symm ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory
      (rightDerivedLowerStarIdIso R Y) ≪≫ Functor.rightUnitor _


/-- The specified comparison F_Y j_! to F_U, obtained from the canonical compositor.
Its inverse is the left-functor identification in the node.
Source: lem-coef-finite-dualizing, paragraph 2, open structural composition
(blueprint: lem-coef-dualizing-open-adjoint). -/
def coefDualizingOpenLeftIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} R) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} R) (j ≫ f) :=
  Functor.isoWhiskerRight (coefDualizingOpenNormalization R j).symm _ ≪≫
    unboundedEtaleLowerShriekCompIso R j f


/-- The ordinary bounded-below left identification, with the open normalization fixed.
Compare the selected compactification with (j, identity), remove the derived identity
image, invert this normalization, and then apply the ordinary compact-support compositor.
Source: lem-coef-finite-dualizing, paragraph 2, bounded-below structural identification
(blueprint: lem-coef-dualizing-open-adjoint). -/
def coefDualizingOpenLeftPlusIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekPlus (ModuleCat.{u + 1} R) f ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} R) (j ≫ f) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationPlusIso R
          (HasCompactification.compactification j) (Compactification.ofIsOpenImmersion j) ≪≫
        Functor.isoWhiskerLeft
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus
          (lowerStarIdDerivedPlus (ModuleCat.{u + 1} R) Y) ≪≫
        Functor.rightUnitor _).symm _ ≪≫
    rightDerivedLowerShriekPlusCompIso R j f


/-- On bounded-below inputs the actual left identification is the ordinary one above.
The square includes the exact open-extension compatibility, so it compares the normalized
identifications themselves, not just the underlying compact-support compositors.
The right identification is their counit-normalized mate, defined by right-adjoint uniqueness.
Source: lem-coef-finite-dualizing, paragraph 2, bounded-below normalization
(blueprint: lem-coef-dualizing-open-adjoint). -/
def CoefDualizingOpenPlusStatement
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] : Prop :=
  ∀ K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)),
    _root_.DerivedCategory.Plus.ι.map
        ((coefDualizingOpenLeftPlusIso R j f).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) (j ≫ f)).hom.app K =
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) f).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus.obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map
        ((Functor.mapDerivedCategoryPlusCompatibility
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) j)).hom.app K) ≫
      (coefDualizingOpenLeftIso R j f).hom.app (_root_.DerivedCategory.Plus.ι.obj K)


/-- The ordinary bounded-below compositor agrees with the actual open-normalized
unbounded compositor. This is only the bounded-below comparison clause; it makes
no assertion about the structural adjoint or its counit.

Source: lem-coef-finite-dualizing.proof.md, paragraph 2, first sentence; step 5 of
lem-coef-dualizing-open-adjoint.
(blueprint: lem-coef-dualizing-open-compositor-plus).

Proof: apply unboundedEtaleCompactSupport_comparison_plus to the chosen
compactification of j and (j,identity). Coherence identifies its unbounded
comparison with the inverse comparison in the opposite direction. Compare the
bounded-below and unbounded identity direct-image normalizations by rightDerived_ext:
after their derived units both maps are localization of lowerStarId, by
lowerStarIdDerivedPlus_hom_app_fac, rightDerivedFunctorIsoMapDerivedCategory_hom_fac
and mapDerivedCategoryNatIso_fach. The unit equation for
rightDerivedFunctorPlusCompatibility identifies the units. Paste this identity
square with the compactification square, then cancel the normalization isomorphism
to invert the resulting square. Apply structural compact support, use naturality
of its Plus compatibility, and paste with
unboundedEtaleCompactSupport_composition_plus. Associativity and functoriality give
the displayed equation. The argument works for empty and identity opens, without
flatness hypotheses or restrictions on the bounded-below complex.
-/
theorem coefDualizingOpenCompositorPlus
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y] [IsNoetherian S]
    (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] :
    CoefDualizingOpenPlusStatement R j f := by sorry

end AlgebraicGeometry.Etale
