/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOperationDescentSpecification
public import WeilConjectures.AlgebraicGeometry.PurFrameworkPbcCoefficientCategoryComparison
public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonIdentification
public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Whiskering

/-! # Identification of smooth operations on common coefficient stages

Source: smooth-purity transport, Step 2, common-stage morphisms and inverse equations
(blueprint: def-pur-smooth-operation-identification-specification).

The finite PBC operations are the specified localized integral operations transported
through the identity coefficient-presentation equivalences. The conclusion fixes
all comparison components, representative actions, shifts and transformation equations.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w z
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CommonStageSmoothOperationIdentification
set_option allowUnsafeReducibility true
attribute [local irreducible] HasDerivedCategory.standard stageEquivalence
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [smooth : SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System.{u, v} l Ω D hl (f := f))
  [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (JX : FdCoefficientComparison l Ω X) (JY : FdCoefficientComparison l Ω Y)

attribute [local irreducible] finiteOperation commonOperation
  conjugate conjugateIso pbcOperation finiteComparison strictComparison objectComparison

/-- Finite conjugation and its descended equation for arbitrary compatible maps,
including the specified finite representatives of inverses.
Source: smooth-purity transport Step 2, transformation and inverse equations
(blueprint: def-pur-smooth-operation-identification-specification). -/
@[irreducible] def TransportSpec
    (H G : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out))
    (RH : commonOperation.{u, v} l Ω D hl f d S false ⋙ JX.equivalence.functor ≅
      JY.equivalence.functor ⋙ H.base.functor)
    (RG : commonOperation.{u, v} l Ω D hl f d S true ⋙ JX.equivalence.functor ≅
      JY.equivalence.functor ⋙ G.base.functor) : Prop :=
  ∀ θ : StageSystem.Morphism.Hom H.base G.base,
    ∃ (θs : commonOperation.{u, v} l Ω D hl f d S false ⟶
        commonOperation.{u, v} l Ω D hl f d S true)
      (θE : ∀ E, finiteOperation.{u, v} l Ω D hl f d S false E ⟶
        finiteOperation.{u, v} l Ω D hl f d S true E),
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E),
        ∃ t : (pbcOperation.{u, v} l Ω D hl f d S JX JY false E).obj
              ((stageEquivalence.{u, v} l Ω Y JY E).functor.obj K) ⟶
            (pbcOperation.{u, v} l Ω D hl f d S JX JY true E).obj
              ((stageEquivalence.{u, v} l Ω Y JY E).functor.obj K),
          HEq t ((θ.τ E).app ((stageEquivalence.{u, v} l Ω Y JY E).functor.obj K)) ∧
          (stageEquivalence.{u, v} l Ω X JX E).functor.map ((θE E).app K) =
            (finiteComparisonAt.{u, v} l Ω D hl f d S JX JY false E K).hom ≫ t ≫
              (finiteComparisonAt.{u, v} l Ω D hl f d S JX JY true E K).inv) ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
        θs.app K ≫ (objectComparison.{u, v} l Ω D hl f d S true K).hom =
          (objectComparison.{u, v} l Ω D hl f d S false K).hom ≫
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι K.stage).map
              ((θE K.stage).app K.obj)) ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
        JX.equivalence.functor.map (θs.app K) = RH.hom.app K ≫
          (StageSystem.Morphism.descNatTrans θ).app (JY.equivalence.functor.obj K) ≫
            RG.inv.app K) ∧
      (∀ ψ : StageSystem.Morphism.Hom G.base H.base,
        (∀ E, θ.τ E ≫ ψ.τ E = 𝟙 (H.base.Φ E)) →
        (∀ E, ψ.τ E ≫ θ.τ E = 𝟙 (G.base.Φ E)) →
        ∃ ψs : commonOperation.{u, v} l Ω D hl f d S true ⟶
            commonOperation.{u, v} l Ω D hl f d S false,
          (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
            JX.equivalence.functor.map (ψs.app K) = RG.hom.app K ≫
              (StageSystem.Morphism.descNatTrans ψ).app (JY.equivalence.functor.obj K) ≫
                RH.inv.app K) ∧
          θs ≫ ψs = 𝟙 _ ∧ ψs ≫ θs = 𝟙 _)

/-- The full common-stage identification, with both exact operations simultaneously.
Source: smooth-purity transport Step 2, repaired common-stage calculation
(blueprint: def-pur-smooth-operation-identification-specification). -/
@[irreducible] def Result : Prop :=
  ∃ (H G : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out))
    (RH : commonOperation.{u, v} l Ω D hl f d S false ⋙ JX.equivalence.functor ≅
      JY.equivalence.functor ⋙ H.base.functor)
    (RG : commonOperation.{u, v} l Ω D hl f d S true ⋙ JX.equivalence.functor ≅
      JY.equivalence.functor ⋙ G.base.functor),
    OperationSpec l Ω D hl f d S JX JY false H.base RH ∧
    OperationSpec l Ω D hl f d S JX JY true G.base RG ∧
    FrameworkRepresentativeSpec l Ω X JX ∧ FrameworkRepresentativeSpec l Ω Y JY ∧
    TransformationSpec H.base G.base ∧
    TransportSpec l Ω D hl f d S JX JY H G RH RG ∧
    ∃ (hS : (commonOperation.{u, v} l Ω D hl f d S false).CommShift ℤ)
      (gS : (commonOperation.{u, v} l Ω D hl f d S true).CommShift ℤ)
      (hP : H.base.functor.CommShift ℤ) (gP : G.base.functor.CommShift ℤ),
      (fun [_hs : (commonOperation.{u, v} l Ω D hl f d S false).CommShift ℤ]
        [_gs : (commonOperation.{u, v} l Ω D hl f d S true).CommShift ℤ]
        [_hp : H.base.functor.CommShift ℤ] [_gp : G.base.functor.CommShift ℤ] ↦
        (commonOperation.{u, v} l Ω D hl f d S false).Additive ∧
        (commonOperation.{u, v} l Ω D hl f d S true).Additive ∧
        (commonOperation.{u, v} l Ω D hl f d S false).IsTriangulated ∧
        (commonOperation.{u, v} l Ω D hl f d S true).IsTriangulated ∧
        H.base.functor.IsTriangulated ∧ G.base.functor.IsTriangulated ∧
        RH.hom.CommShift ℤ ∧ RG.hom.CommShift ℤ ∧
        (∀ θ : StageSystem.Morphism.Hom H.base G.base,
          (∀ E, @NatTrans.CommShift _ _ _ _ (H.base.Φ E) (G.base.Φ E)
            (θ.τ E) ℤ _ _ _ (H.commShift E) (G.commShift E)) →
          (StageSystem.Morphism.descNatTrans θ).CommShift ℤ ∧
          ∃ θs : commonOperation.{u, v} l Ω D hl f d S false ⟶
              commonOperation.{u, v} l Ω D hl f d S true,
            θs.CommShift ℤ ∧
            (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
              JX.equivalence.functor.map (θs.app K) = RH.hom.app K ≫
                (StageSystem.Morphism.descNatTrans θ).app (JY.equivalence.functor.obj K) ≫
                  RG.inv.app K)) ∧
        (∀ E (K : pbcStageCategory l Ω Y E) (n : ℤ),
          HEq (H.base.functor.map
              ((((pbcScalarSystem l Ω Y dY.out iY.out).ι E).commShiftIso n).hom.app K) ≫
            (H.base.functor.commShiftIso n).hom.app
              (((pbcScalarSystem l Ω Y dY.out iY.out).ι E).obj K))
            (((pbcScalarSystem l Ω X dX.out iX.out).ι E).map
              ((Functor.commShiftIso (H.base.Φ E) (self := H.commShift E) n).hom.app K) ≫
              (((pbcScalarSystem l Ω X dX.out iX.out).ι E).commShiftIso n).hom.app
                ((H.base.Φ E).obj K))) ∧
        (∀ E (K : pbcStageCategory l Ω Y E) (n : ℤ),
          HEq (G.base.functor.map
              ((((pbcScalarSystem l Ω Y dY.out iY.out).ι E).commShiftIso n).hom.app K) ≫
            (G.base.functor.commShiftIso n).hom.app
              (((pbcScalarSystem l Ω Y dY.out iY.out).ι E).obj K))
            (((pbcScalarSystem l Ω X dX.out iX.out).ι E).map
              ((Functor.commShiftIso (G.base.Φ E) (self := G.commShift E) n).hom.app K) ≫
              (((pbcScalarSystem l Ω X dX.out iX.out).ι E).commShiftIso n).hom.app
                ((G.base.Φ E).obj K))))
        (_hs := hS) (_gs := gS) (_hp := hP) (_gp := gP)


end WeilConjectures.CommonStageSmoothOperationIdentification
