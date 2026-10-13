/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.ModuleCupResolutionRealization
import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility
import Sheaf.Paper.ModuleCupSinglePairingHomology

/-! # Equality of realized derived pairings on cocycle classes

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-equal-derived-maps-class)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance cupClassCongruenceMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
local instance cupClassCongruenceSymmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance cupClassCongruenceHasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance cupClassCongruenceMonoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
local instance cupClassCongruenceMonoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance cupClassCongruenceHasFunctorialFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
local instance cupClassCongruenceIsGrothendieckAbelian : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)

attribute [local irreducible] Functor.rightDerivedFunctor

set_option maxHeartbeats 1000000 in
-- Comparing the two transported cohomology formulas requires this elaboration budget.
/-- Equal realized derived pairings induce equal output classes on equal input classes.
Source: Stacks Project, Section 20.31, Lemma 20.31.3 (0FKU), global specialization.
(blueprint: lem-sc-module-cup-equal-derived-maps-class)
Proof: apply the naive/derived global cup diagram to the integer extensions of both
pairs of resolution complexes. Postcompose each diagram with the localization of
the realized cochain map and the inverse target augmentation. Naturality of the
derived cup moves the input augmentations across the diagram, so the resulting
bottom arrows agree by hmaps. The section formula for the naive map and the two
Realizes hypotheses identify the upper values with the two specified paired
cocycles. Each comparison to an injective resolution extends the augmentation by
D.over or E.over and induces an isomorphism on global cohomology by computes.
Hence the induced input and output identifications are precisely the class maps.
Extension by zero identifies integer homology with nonnegative homology. Taking
cohomology, then using ha and hb, gives the asserted equality. No bilinear
cohomology map is constructed or assumed here, and no degree-zero normalization
is used. This works also in degree zero, for zero sheaves, and for zero cycles. -/
theorem moduleCup_equal_derived_maps_class {F G : X.Modules}
    (D E : CupResolutionPairing F G)
    (tD : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (tE : E.left.integerComplex ⊗ E.right.integerComplex ⟶ E.target.integerComplex)
    (hD : D.Realizes tD) (hE : E.Realizes tE)
    (hmaps : D.derivedMap tD = E.derivedMap tE) (p q : ℕ)
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
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨V⟩ := exists_cupDerivedHomologyTensor (k := Γ(X, ⊤))
    obtain ⟨J⟩ := exists_cupDerivedClassComparison X
    obtain ⟨μ, hμ, hdiagram⟩ := moduleCup_naive_derived_compatibility X
    have hD' := moduleCup_single_pairing_homology V J μ hμ hdiagram D tD hD p q a b c hc
    have hE' := moduleCup_single_pairing_homology V J μ hμ hdiagram E tE hE p q a' b' c' hc'
    rw [hmaps, ha, hb] at hD'
    exact (J.equiv (F ⊗ G) (p + q)).injective (hD'.trans hE'.symm)

end
end AlgebraicGeometry.Scheme.Modules
