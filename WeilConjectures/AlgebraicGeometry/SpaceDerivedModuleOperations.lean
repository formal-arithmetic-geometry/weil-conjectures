/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceAffineHomComparison

/-! # Tensor and original-complex comparisons on the recorded small models

Source: Stacks Project, Tags 06YS and 07A4
(blueprint: def-sfb-space-base-change-comparisons).

This generalizes the recorded interface's ambient all-spaces localization instance.
The ordinary scalar and signed total comparisons are reused from that interface;
the derived comparison uses the same Q115 tensor models and O3 derived pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

attribute [local irreducible] derivedDualityModel derivedTensorPullback
  smallModuleTensorPullback WeilConjectures.coefficientTotalTensor
  WeilConjectures.CoefficientTensorModels.iso CochainComplex.IsKFlatIndependentCoefficients

/-- Total comparison on the actual total complexes used by the recorded tensor model.
The local sections are the existing ordinary comparison's section construction.
Source: Stacks, Tag 07A4 (blueprint: def-sfb-space-base-change-comparisons). -/
def SmallModulePullbackTensorTotalNormalized (f : X ⟶ Y)
    (c : WeilConjectures.coefficientTotalTensor.{u, u, u}
          Y.smallEtaleModelTopology Y.smallStructureSheaf ⋙
          (smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ) ≅
        ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).prod
            ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)) ⋙
          WeilConjectures.coefficientTotalTensor.{u, u, u}
            X.smallEtaleModelTopology X.smallStructureSheaf) : Prop :=
  ∀ (P Q : CochainComplex Y.SmallModules ℤ) (i j : ℤ)
    (G : Over S) (x : yoneda.obj G ⟶ X.obj.obj)
    (U : SingleComplex.Neighbourhood G x)
    (V : SingleComplex.Neighbourhood G (x ≫ f.hom.hom))
    (a : ((SingleComplex.neighbourhoodChart (x := x)).obj U).obj.left ⟶
      ((SingleComplex.neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.left)
    (ha : SingleComplex.Compatible f U V a)
    (b : (SingleComplex.ringDiagram x).obj (op U))
    (m : (P.X i).val.obj (op V.right)) (n : (Q.X j).val.obj (op V.right)),
    ((c.hom.app (P, Q)).f (i + j)).val.app (op U.right)
        (SingleComplex.localSection f
          (((WeilConjectures.coefficientTotalTensor.{u, u, u}
            Y.smallEtaleModelTopology Y.smallStructureSheaf).obj (P, Q)).X (i + j))
          U V a ha b (WeilConjectures.coefficientTensorGenerator.{u, u, u}
            Y.smallEtaleModelTopology Y.smallStructureSheaf P Q i j (i + j) rfl
            (op V.right) m n)) =
      WeilConjectures.coefficientTensorGenerator.{u, u, u}
        X.smallEtaleModelTopology X.smallStructureSheaf
        (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj P)
        (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj Q)
        i j (i + j) rfl (op U.right)
        (SingleComplex.localSection f (P.X i) U V a ha b m)
        (SingleComplex.localSection f (Q.X j) U V a ha 1 n)

/-- Transport of the recorded ordinary total comparison to the tensor model's totalization.
Source: Stacks, Tag 07A4 (blueprint: def-sfb-space-base-change-comparisons).
Proof: the two totalizations are coproducts of the same ordinary tensor summands.
The canonical coproduct comparison preserves each summand inclusion. Conjugate
ordinaryTotal by those comparisons. Its scalar formula is ordinaryTensor's recorded
formula on each summand, exactly the displayed equation. Conversely local pure
sections generate each sheaf tensor and the total summand inclusions detect equality,
so this equation determines the transported natural isomorphism uniquely. -/
theorem smallModulePullbackTensorTotal_existsUnique (f : X ⟶ Y) :
    ∃! c : WeilConjectures.coefficientTotalTensor.{u, u, u}
          Y.smallEtaleModelTopology Y.smallStructureSheaf ⋙
          (smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ) ≅
        ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).prod
            ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)) ⋙
          WeilConjectures.coefficientTotalTensor.{u, u, u}
            X.smallEtaleModelTopology X.smallStructureSheaf,
      SmallModulePullbackTensorTotalNormalized f c := by
  sorry

/-- The canonical transport of the existing total comparison, fixed on every summand.
Source: Stacks, Tag 07A4 (blueprint: def-sfb-space-base-change-comparisons). -/
def smallModulePullbackTensorTotal (f : X ⟶ Y) :
    WeilConjectures.coefficientTotalTensor.{u, u, u}
      Y.smallEtaleModelTopology Y.smallStructureSheaf ⋙
        (smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ) ≅
      ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).prod
          ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)) ⋙
        WeilConjectures.coefficientTotalTensor.{u, u, u}
            X.smallEtaleModelTopology X.smallStructureSheaf :=
  (smallModulePullbackTensorTotal_existsUnique f).choose

/-- The explicit normalization predicate used to select this canonical comparison.
Source: Stacks, Tags 07A4 (blueprint: def-sfb-space-base-change-comparisons). -/
def ModuleDerivedPullbackTensorNormalized
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y)
    (c : (derivedDualityModel.{u, w} Y).closed.tensor ⋙ derivedTensorPullback.{u, w, w} f ≅
        (derivedTensorPullback.{u, w, w} f).prod (derivedTensorPullback.{u, w, w} f) ⋙
          (derivedDualityModel.{u, w} X).closed.tensor) : Prop :=
  ∀ (P Q : CochainComplex Y.SmallModules ℤ)
    (hP : SingleComplex.FlatKFlat Y P) (hQ : SingleComplex.FlatKFlat Y Q),
    ∃ (hP' : SingleComplex.FlatKFlat X
        (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj P))
      (hQ' : SingleComplex.FlatKFlat X
        (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj Q)),
      (derivedTensorPullback.{u, w, w} f).map
          ((WeilConjectures.CoefficientTensorModels.iso.{u, u, u, w}
            Y.smallEtaleModelTopology Y.smallStructureSheaf
            (derivedDualityModel.{u, w} Y).closed (derivedDualityModel.{u, w} Y).models
            P Q hP.1 hQ.1).hom) ≫
          c.hom.app ((DerivedCategory.Q.{w} (C := Y.SmallModules)).obj P,
            (DerivedCategory.Q.{w} (C := Y.SmallModules)).obj Q) ≫
          (derivedDualityModel.{u, w} X).closed.tensor.map
            (Prod.mkHom ((spaceDerivedPullbackCounit f).app P)
              ((spaceDerivedPullbackCounit f).app Q)) =
        (spaceDerivedPullbackCounit f).app
            ((WeilConjectures.coefficientTotalTensor.{u, u, u}
              Y.smallEtaleModelTopology Y.smallStructureSheaf).obj (P, Q)) ≫
          (DerivedCategory.Q.{w} (C := X.SmallModules)).map
            ((smallModulePullbackTensorTotal f).hom.app (P, Q)) ≫
          (WeilConjectures.CoefficientTensorModels.iso.{u, u, u, w}
            X.smallEtaleModelTopology X.smallStructureSheaf
            (derivedDualityModel.{u, w} X).closed (derivedDualityModel.{u, w} X).models
            (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj P)
            (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj Q)
            hP'.1 hQ'.1).hom

/-- The normalized derived comparison uses Q115's actual K-flat tensor models.
Source: Stacks, Tag 07A4 (blueprint: def-sfb-space-base-change-comparisons).
Proof: this is the representative construction of
ringedTopoiCanonicalDerivedTensorPullback. Resolve both inputs by K-flat flat-term
complexes, apply the recorded scalar-normalized ordinary total comparison and the two recorded
models.iso maps. Pullback preserves K-flats with flat terms, so these maps are
invertible. Two-variable resolving-class localization gives the unique comparison
with the displayed representative square. No second tensor functor is constructed. -/
theorem moduleDerivedPullbackTensor_existsUnique
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y) :
    ∃! c : (derivedDualityModel.{u, w} Y).closed.tensor ⋙ derivedTensorPullback.{u, w, w} f ≅
        (derivedTensorPullback.{u, w, w} f).prod (derivedTensorPullback.{u, w, w} f) ⋙
          (derivedDualityModel.{u, w} X).closed.tensor,
      ModuleDerivedPullbackTensorNormalized f c := by
  sorry

/-- Canonical derived tensor comparison on the recorded tensor objects.
Source: Stacks, Tag 07A4 (blueprint: def-sfb-space-base-change-comparisons). -/
def moduleDerivedPullbackTensor
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y) :
    (derivedDualityModel.{u, w} Y).closed.tensor ⋙ derivedTensorPullback.{u, w, w} f ≅
      (derivedTensorPullback.{u, w, w} f).prod (derivedTensorPullback.{u, w, w} f) ⋙
        (derivedDualityModel.{u, w} X).closed.tensor :=
  (moduleDerivedPullbackTensor_existsUnique f).choose

attribute [local semireducible] smallModuleTensorPullback

/-- Restriction is additive, being the recorded sectionwise equivalence.
Source: Stacks, Tag 039Z (blueprint: def-sfb-space-base-change-comparisons).
Proof: restriction retains the section maps and their sums, so it preserves addition. -/
@[instance] theorem smallModuleRestriction_additive (X : AlgebraicSpace S) :
    X.smallModuleRestriction.Additive := by
  sorry

/-- Actual restriction of a complex of original-site modules to the small model.
Source: Stacks, Tag 039Z (blueprint: def-sfb-space-base-change-comparisons). -/
def smallModuleComplex (X : AlgebraicSpace S) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.SmallModules ℤ :=
  X.smallModuleRestriction.mapHomologicalComplex (.up ℤ)

/-- Pullback commutes with restriction via the fixed equivalence unit.
Source: Stacks, Tag 039Z (blueprint: def-sfb-space-base-change-comparisons). -/
def smallRestrictionPullback (f : X ⟶ Y) :
    Y.smallModuleRestriction ⋙ smallModuleTensorPullback f ≅
      moduleTensorPullback f ⋙ X.smallModuleRestriction :=
  Y.smallModuleEquivalence.funInvIdAssoc (moduleTensorPullback f ⋙ X.smallModuleRestriction)

/-- The original tensor-pullback functor is additive.
Source: Stacks, Tag 03D7 (blueprint: def-sfb-space-base-change-comparisons).
Proof: the tensor-section construction distributes over sums of section maps,
and the chart projections detect equality of maps. -/
@[instance] theorem moduleTensorPullback_additive (f : X ⟶ Y) :
    (moduleTensorPullback f).Additive := by
  sorry

/-- Ordinary termwise pullback followed by actual small-model restriction.
Source: Stacks, Tag 0A1K (blueprint: def-sfb-space-base-change-comparisons). -/
def smallOrdinaryPullbackComplex (f : X ⟶ Y) :
    CochainComplex Y.Modules ℤ ⥤ CochainComplex X.SmallModules ℤ :=
  (moduleTensorPullback f).mapHomologicalComplex (.up ℤ) ⋙ smallModuleComplex X

section Derived

variable [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]

/-- Counit of Lf^* to ordinary pullback of the given original-site complex, restricted.
Source: Stacks, Tag 0A1K (blueprint: def-sfb-space-base-change-comparisons). -/
def moduleOriginalPullbackCounit (f : X ⟶ Y) (G : CochainComplex Y.Modules ℤ) :
    (derivedTensorPullback f).obj (DerivedCategory.Q.obj ((smallModuleComplex Y).obj G)) ⟶
      DerivedCategory.Q.obj ((smallOrdinaryPullbackComplex f).obj G) :=
  (spaceDerivedPullbackCounit f).app ((smallModuleComplex Y).obj G) ≫
    DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (smallRestrictionPullback f) (.up ℤ)).hom.app G)

end Derived

end AlgebraicGeometry.AlgebraicSpace
