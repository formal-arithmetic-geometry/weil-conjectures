/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Paper.ModuleCupNaiveMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import Sheaf.Paper.ModuleCupGlobalTensorPullback
import Sheaf.Paper.ModuleCupGlobalCounitComparison
import Sheaf.Paper.ModuleCupGlobalTensorComparison

/-! # Derived cup evaluated in a K-injective target

Source: Stacks, Tag 0FP3, specialized to the map to (pt, Γ(X,O_X)).
This is the adjunction calculation for a chain pairing with K-injective
codomain. The argument passing to an arbitrary codomain is in the importing
compatibility module, by naturality and cancellation of a resolution.
-/

@[expose] public section

universe u wC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

local instance : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance : SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf

local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

/-- The canonical lax tensor comparison of localization, specialized to module sheaves.
This names the existing instance so the compatibility calculation and its use share
one transparent interface. -/
@[instance_reducible]
def moduleCup_sourceLax :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  inferInstance

local instance cupSourceLax :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  moduleCup_sourceLax X

/-- The natural right-derived comparison unit on cochain complexes.
Source: Stacks, Tag 0FP3 (blueprint: lem-sc-module-cup-kinjective-target). -/
def moduleCup_comparisonNatTrans :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor :=
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  (Functor.isoWhiskerLeft (S.mapHomologicalComplex (ComplexShape.up ℤ))
    (DerivedCategory.quotientCompQhIso
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      S.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))) S.rightDerivedFunctor).hom

/-- Construct the natural derived cup and calculate it with a K-injective target.
Source: Stacks, Tag 0FP3, Lemma 20.31.3, and Tag 0B68 (relative cup by adjunction).
(blueprint: lem-sc-module-cup-kinjective-target)
Proof: for the map to (pt, Γ(X,O_X)), take the derived tensor pullback left
adjoint to RΓ. Use lem-sc-module-cup-global-tensor-pullback for its canonical
tensor isomorphism, normalized on K-flat representatives and compatible with
ordinary tensor-section evaluation. Define μ by adjunction from this
comparison followed by the tensor of the two counits. Naturality of the comparison
and of the counits gives the displayed naturality equation.
For a chain pairing φ:Tot(K tensor L)→I with I K-injective, compute RΓ(QI) by
QΓ(I), using rightDerivedFunctorObjQIso. Resolve the two complexes of sections
by K-flat complexes and compute the left-adjoint transpose of the composite.
The comparison from derived to ordinary pullback, followed by the counit, is the
ordinary pullback/sections evaluation, by
lem-sc-module-cup-global-counit-comparison. Use the induced adjunction, whose
counit this theorem identifies; the absolute K-flat comparison and K-injective
right derivation supply its postcomposition hypotheses. The full tensor polygon
commutes by lem-sc-module-cup-global-tensor-comparison, applied with the K-flat
normalization furnished by lem-sc-module-cup-global-tensor-pullback.
Hence on each tensor summand the
transpose is evaluation on tmulSection, followed by φ. The coproduct formula
for moduleCup_naiveMap gives exactly that chain pairing. Equality of these
transposes proves the identity after identifying RΓ(QI) with QΓ(I). This is the polygon proof
of 20.31.3 with its last vertex replaced by the K-injective target I. Neither
K nor L is required to be flat, bounded, or K-injective. -/
theorem moduleCup_exists_kinjective_target_pairing :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
    let R := S.rightDerivedFunctor
    ∃ μ : ∀ A B : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
        R.obj A ⊗ R.obj B ⟶ R.obj (A ⊗ B),
      (∀ (A A' B B' : DerivedCategory
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
        (f : A ⟶ A') (g : B ⟶ B'),
        (R.map f ⊗ₘ R.map g) ≫ μ A' B' = μ A B ≫ R.map (f ⊗ₘ g)) ∧
      ∀ (K L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        [I.IsKInjective] (φ : K ⊗ L ⟶ I),
        ((moduleCup_comparisonNatTrans X).app K ⊗ₘ
          (moduleCup_comparisonNatTrans X).app L) ≫
          μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
            R.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫
              DerivedCategory.Q.map φ) =
          Functor.LaxMonoidal.μ DerivedCategory.Q (T.obj K) (T.obj L) ≫
            DerivedCategory.Q.map (moduleCup_naiveMap X K L ≫ T.map φ) ≫
              (moduleCup_comparisonNatTrans X).app I := by sorry

end
end AlgebraicGeometry.Scheme.Modules
