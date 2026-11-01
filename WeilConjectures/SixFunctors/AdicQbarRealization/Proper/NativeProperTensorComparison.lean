/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.DirectImage.RationalDirectImageRealization
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # Proper adjunction comparison for native continuous coefficients

Source: Bhatt--Scholze, Proposition 6.8.14, Remark 6.8.15 and Lemma 6.7.2;
agent assembly of the normalized common-stage comparison
(blueprint: def-sf-native-proper-tensor-comparison).

All functors below take values in ordinary module derived categories. The comparison
is fixed before rationalization by balanced tensor multiplication, and its direct-image
comparison is fixed by the actual adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AdicQbarRealization
attribute [local irreducible] ContinuousRational.modulePull ContinuousRational.derivedPull
  ordinaryIntegralModulePull ordinaryIntegralDerivedPull
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
/-- The explicit ordinary-pullback normalization equation for this comparison.
Source: BS 6.8.14--6.8.15; Stacks 07A4
(blueprint: def-sf-native-proper-tensor-comparison). -/
def tensorPure (O : Operations l p R S) (A : At l X R) (C : At l Y S)
    (cochain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
      (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).prod
      ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    : Prop :=
  ∀ (P Q : CochainComplex (modules l Y S) ℤ) (i j : ℤ) (V : Y.ProEt)
      (x : (P.X i).val.obj (op V)) (y : (Q.X j).val.obj (op V)),
    ((cochain.hom.app (P, Q)).f (i + j)).val.app (op ((proEtaleBaseChange p).obj V))
      (((O.moduleAdjunction.unit.app
        (((coefficientTotalTensor.{u + 1, u + 1, u}
          (ProEt.topology Y) (ring l Y S)).obj (P, Q)).X (i + j))).val.app (op V))
        (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
          P Q i j (i + j) rfl (op V) x y)) =
    coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
      (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj P)
      (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj Q)
      i j (i + j) rfl (op ((proEtaleBaseChange p).obj V))
      (((O.moduleAdjunction.unit.app (P.X i)).val.app (op V)) x)
      (((O.moduleAdjunction.unit.app (Q.X j)).val.app (op V)) y)

/-- The explicit ordinary-pullback normalization equation for this comparison.
Source: BS 6.8.14--6.8.15; Stacks 07A4
(blueprint: def-sf-native-proper-tensor-comparison). -/
def tensorRepresentative (O : Operations l p R S) (A : At l X R) (C : At l Y S)
    (cochain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
      (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).prod
      ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (kflat : ∀ P : CochainComplex (modules l Y S) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := ring l Y S) P →
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj P))
    (tensor : C.closed.tensor ⋙ ContinuousRational.derivedPull p O.coefficient ≅
    ((ContinuousRational.derivedPull p O.coefficient).prod
      (ContinuousRational.derivedPull p O.coefficient)) ⋙ A.closed.tensor)
    : Prop :=
  ∀ (P Q : CochainComplex (modules l Y S) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := ring l Y S) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := ring l Y S) Q),
    (ContinuousRational.derivedPull p O.coefficient).map
        (C.models.iso _ _ _ _ _ hP hQ).hom ≫
      tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      A.closed.tensor.map (Prod.mkHom (O.pullCounit.app P) (O.pullCounit.app Q)) =
    O.pullCounit.app
        ((coefficientTotalTensor.{u + 1, u + 1, u}
          (ProEt.topology Y) (ring l Y S)).obj (P, Q)) ≫
      DerivedCategory.Q.map (cochain.hom.app (P, Q)) ≫
      (A.models.iso _ _ _ _ _ (kflat P hP) (kflat Q hQ)).hom

/-- The explicit ordinary-pullback normalization equation for this comparison.
Source: BS 6.8.14--6.8.15; Stacks 07A4
(blueprint: def-sf-native-proper-tensor-comparison). -/
def unitSections (O : Operations l p R S) (A : At l X R) (C : At l Y S)
    (unitCochain : ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex
      (.up ℤ)).obj (ringedTensorUnitComplex.{u + 1, u, u + 1}
        (ProEt.topology Y) (ring l Y S)) ≅
    ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R))
    : Prop :=
  ∀ (V : Y.ProEt) (s : (ring l Y S).obj.obj (op V)),
    (unitCochain.hom.f 0).val.app (op ((proEtaleBaseChange p).obj V))
      ((O.moduleAdjunction.unit.app
        ((ringedTensorUnitComplex.{u + 1, u, u + 1}
          (ProEt.topology Y) (ring l Y S)).X 0)).val.app (op V)
        (ringedTensorUnitSection.{u + 1, u, u + 1}
          (ProEt.topology Y) (ring l Y S) (op V) s)) =
    ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
      (op ((proEtaleBaseChange p).obj V))
      (((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
        O.coefficient).hom.app (op V) s)

/-- The explicit ordinary-pullback normalization equation for this comparison.
Source: BS 6.8.14--6.8.15; Stacks 07A4
(blueprint: def-sf-native-proper-tensor-comparison). -/
def unitRepresentative (O : Operations l p R S) (A : At l X R) (C : At l Y S)
    (unitCochain : ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex
      (.up ℤ)).obj (ringedTensorUnitComplex.{u + 1, u, u + 1}
        (ProEt.topology Y) (ring l Y S)) ≅
    ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R))
    (unit : (ContinuousRational.derivedPull p O.coefficient).obj C.closed.monoidal.tensorUnit ≅
    A.closed.monoidal.tensorUnit)
    : Prop :=
  (ContinuousRational.derivedPull p O.coefficient).map C.coherence.unitIso.hom ≫
      O.pullCounit.app _ ≫ DerivedCategory.Q.map unitCochain.hom =
    unit.hom ≫ A.coherence.unitIso.hom

/-- The canonical derived tensor and unit comparison with all local normalizations.
Source: BS 6.8.14--6.8.15
(blueprint: def-sf-native-proper-tensor-comparison). -/
structure TensorComparison (O : Operations l p R S) (A : At l X R) (C : At l Y S) where
  cochain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
      (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).prod
      ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  pure : tensorPure l p R S O A C cochain
  kflat : ∀ P : CochainComplex (modules l Y S) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := ring l Y S) P →
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj P)
  tensor : C.closed.tensor ⋙ ContinuousRational.derivedPull p O.coefficient ≅
    ((ContinuousRational.derivedPull p O.coefficient).prod
      (ContinuousRational.derivedPull p O.coefficient)) ⋙ A.closed.tensor
  representative : tensorRepresentative l p R S O A C cochain kflat tensor
  unitCochain : ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex
      (.up ℤ)).obj (ringedTensorUnitComplex.{u + 1, u, u + 1}
        (ProEt.topology Y) (ring l Y S)) ≅
    ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
  unit_sections : unitSections l p R S O A C unitCochain
  unit : (ContinuousRational.derivedPull p O.coefficient).obj C.closed.monoidal.tensorUnit ≅
    A.closed.monoidal.tensorUnit
  unit_representative : unitRepresentative l p R S O A C unitCochain unit

end WeilConjectures.AdicQbarRealization.Proper
