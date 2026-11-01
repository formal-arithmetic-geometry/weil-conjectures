/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicReindexingData

/-! # Canonical comparison data
Source: BS 6.8.14--6.8.15; HRS 7.9 (blueprint: def-sf-native-adic-tensor-reindexing). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The tensor reindexing representative equation on the actual K-flat models.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-tensor-reindexing). -/
def reindexTensorRepresentative {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (C : At l Y S) (B : RingReindex l X g R S)
    (cochain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
      (modulePull l X g B).mapHomologicalComplex (.up ℤ) ≅
    (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).prod
      ((modulePull l X g B).mapHomologicalComplex (.up ℤ))) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (kflat : ∀ P : CochainComplex (modules l Y S) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := ring l Y S) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj P))
    (tensor : C.closed.tensor ⋙ derivedPull l X g B ≅
    ((derivedPull l X g B).prod (derivedPull l X g B)) ⋙ A.closed.tensor) : Prop :=
  ∀ (P Q : CochainComplex (modules l Y S) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := ring l Y S) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := ring l Y S) Q),
    (derivedPull l X g B).map ((C.models.iso _ _ _ _ _ hP hQ).hom) ≫
      tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      A.closed.tensor.map (Prod.mkHom
        ((modulePull l X g B).mapDerivedCategoryFactors.hom.app P)
        ((modulePull l X g B).mapDerivedCategoryFactors.hom.app Q)) =
    (modulePull l X g B).mapDerivedCategoryFactors.hom.app
        ((coefficientTotalTensor.{u + 1, u + 1, u}
          (ProEt.topology Y) (ring l Y S)).obj (P, Q)) ≫
      DerivedCategory.Q.map (cochain.hom.app (P, Q)) ≫
      (A.models.iso _ _ _ _ _ (kflat P hP) (kflat Q hQ)).hom

/-- The homogeneous pure-section equation for tensor reindexing.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-tensor-reindexing). -/
def reindexTensorPure {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S)
    (cochain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
      (modulePull l X g B).mapHomologicalComplex (.up ℤ) ≅
    (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).prod
      ((modulePull l X g B).mapHomologicalComplex (.up ℤ))) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) : Prop :=
  ∀ (P Q : CochainComplex (modules l Y S) ℤ) (p q : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X p).val.obj ((proEtaleIsoPostcompose g).op.obj U))
      (y : (Q.X q).val.obj ((proEtaleIsoPostcompose g).op.obj U)),
    ((cochain.hom.app (P, Q)).f (p + q)).val.app U
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
        P Q p q (p + q) rfl ((proEtaleIsoPostcompose g).op.obj U) x y) =
    coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
      (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj P)
      (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj Q)
      p q (p + q) rfl U x y

/-- The coefficient section equation for the reindexing unit in degree zero.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-tensor-reindexing). -/
def reindexUnitSections {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S)
    (unitCochain : ((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)) ≅
    ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)) : Prop :=
  ∀ (U : X.ProEtᵒᵖ)
      (a : (ring l Y S).obj.obj ((proEtaleIsoPostcompose g).op.obj U)),
    (unitCochain.hom.f 0).val.app U
      (ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)
        ((proEtaleIsoPostcompose g).op.obj U) a) =
    ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
      U (B.iso.hom.hom.app U a)

/-- The ordinary tensor comparison for reindexing, fixed on homogeneous pure tensors
and coefficient-unit sections, and descended using the actual K-flat models.
Source: BS 6.8.15; Stacks 07A4
(blueprint: def-sf-native-adic-tensor-reindexing). -/
structure ReindexTensor {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (C : At l Y S) (B : RingReindex l X g R S) where
  cochain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
      (modulePull l X g B).mapHomologicalComplex (.up ℤ) ≅
    (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).prod
      ((modulePull l X g B).mapHomologicalComplex (.up ℤ))) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  pure : reindexTensorPure l X g B cochain
  kflat : ∀ P : CochainComplex (modules l Y S) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := ring l Y S) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj P)
  tensor : C.closed.tensor ⋙ derivedPull l X g B ≅
    ((derivedPull l X g B).prod (derivedPull l X g B)) ⋙ A.closed.tensor
  representative : reindexTensorRepresentative l X g A C B cochain kflat tensor
  unitCochain : ((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)) ≅
    ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
  unit_sections : reindexUnitSections l X g B unitCochain

/-- The unit map of ordinary reindexing is the coefficient map in degree zero.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-tensor-reindexing). -/
def pullUnit {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {A : At l X R} {C : At l Y S} {B : RingReindex l X g R S}
    (V : ReindexTensor l X g A C B) :
    (derivedPull l X g B).obj C.closed.monoidal.tensorUnit ≅ A.closed.monoidal.tensorUnit :=
  (derivedPull l X g B).mapIso C.coherence.unitIso ≪≫
    (modulePull l X g B).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso V.unitCochain ≪≫ A.coherence.unitIso.symm

/-- The ordinary Hom inverse-image map is the transpose of pulled-back evaluation.
Source: BS 6.8.15; Stacks 0GMX
(blueprint: def-sf-native-adic-tensor-reindexing). -/
def pullHom {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {A : At l X R} {C : At l Y S} {B : RingReindex l X g R S}
    (V : ReindexTensor l X g A C B) (M N : DerivedCategory (modules l Y S)) :
    (derivedPull l X g B).obj ((ambientHom l Y S).obj (op M, N)) ⟶
      (ambientHom l X R).obj
        (op ((derivedPull l X g B).obj M), (derivedPull l X g B).obj N) :=
  A.closed.transpose _ _ _
    (V.tensor.inv.app ((ambientHom l Y S).obj (op M, N), M) ≫
      (derivedPull l X g B).map (C.closed.evaluation M N))

end WeilConjectures.AdicQbarRealization
