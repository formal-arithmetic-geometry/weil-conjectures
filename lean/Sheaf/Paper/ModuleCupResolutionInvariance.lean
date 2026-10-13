/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
import Sheaf.Paper.ModuleCupDerivedTensorConnectivity
import Sheaf.Paper.ModuleCupResolutionRealization
import Sheaf.Paper.ModuleCupRealizationEvaluation
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Independence of resolution pairings on cohomology

Source: Stacks Project, Cohomology of Sheaves, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-resolution-invariance)
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Products of representatives with equal input classes have equal output
classes, even when the representatives belong to different computing pairings.
No bilinear cup product is assumed or constructed in this statement.
Source: Stacks Project, Section 20.31 (0FKU), Lemma 20.31.3 and Tag 0FKV.
(blueprint: lem-sc-module-cup-resolution-invariance)
Proof: a restriction-compatible O-linear pairing with Leibniz is a morphism
from the signed total tensor of the two resolution complexes to the target
complex. Precompose with the canonical morphism from derived tensor to naive
tensor, and identify the three complexes with F, G and F tensor G via their
augmentations. This gives a morphism F tensor-derived G to F tensor G in the
sheaf derived category. F tensor-derived G is in nonpositive degrees; the target
is concentrated in degree zero. The truncation adjunction identifies morphisms
between these objects with morphisms H-zero(F tensor-derived G) to F tensor G.
H-zero is the ordinary tensor F tensor G. The augmentation_pair condition
identifies the latter morphism with the identity, for both D and E. Hence their
derived morphisms coincide. Apply derived global sections and the compatibility
of naive cup with derived cup (Lemma 20.31.3 for the map to the one-point ringed
space). The input and output comparison maps are precisely those extending the
augmentations in CupAcyclicResolution, so taking cohomology uses its class maps.
The equalities of input classes therefore imply equality of the output classes.
The argument needs neither flat coefficients nor termwise flat resolutions. -/
theorem moduleCup_resolution_invariance {X : Scheme.{uM}} {F G : X.Modules}
    (D E : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.left.K).sc p).moduleCatLeftHomologyData.K)
    (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.right.K).sc q).moduleCatLeftHomologyData.K)
    (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (ha : D.left.class p a = E.left.class p a')
    (hb : D.right.class q b = E.right.class q b')
    (hc : c.val = D.pair p q ⊤ a.val b.val)
    (hc' : c'.val = E.pair p q ⊤ a'.val b'.val) :
    D.target.class (p + q) c = E.target.class (p + q) c' := by
  let : MonoidalCategory (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.monoidalCategory X.sheaf
  let : SymmetricCategory (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.symmetricCategory X.sheaf
  let : HasColimitsOfSize.{0, 0} (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, uM} _
  let : MonoidalPreadditive (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  let : IsGrothendieckAbelian.{uM}
      (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  let : HasDerivedCategory.{uM} (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    schemeModule_hasFunctorialFlatResolution X
  obtain ⟨evaluation, hevaluation⟩ := moduleCup_realization_evaluation F G p q
  obtain ⟨tD, hD, hD₀⟩ := moduleCup_resolution_realization D
  obtain ⟨tE, hE, hE₀⟩ := moduleCup_resolution_realization E
  have hLE := DerivedCategory.moduleCup_derived_tensor_connectivity
    (C := SheafOfModules.{uM} (moduleRings X.toRingedSpace)) F G
  change (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) 0).obj G)).IsLE 0 at hLE
  let := hLE
  have hmaps : D.derivedMap tD = E.derivedMap tE :=
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).1
      (hD₀.trans hE₀.symm)
  calc
    D.target.class (p + q) c =
        evaluation (D.derivedMap tD) (D.left.class p a) (D.right.class q b) :=
      (hevaluation D tD hD a b c hc).symm
    _ = evaluation (E.derivedMap tE) (E.left.class p a') (E.right.class q b') := by
      rw [hmaps, ha, hb]
    _ = E.target.class (p + q) c' := hevaluation E tE hE a' b' c' hc'


end
end AlgebraicGeometry.Scheme.Modules
