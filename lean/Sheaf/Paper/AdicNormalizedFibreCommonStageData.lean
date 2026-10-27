/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.AdicNormalizedFibreScalar
public import Sheaf.Paper.PerAdicCommonStageTruncations
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Common-stage fibre descent interfaces -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

attribute [local irreducible] stageHeart heartScalar commonHeartPull

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Preservation of finite-stage kernels, cokernels, images and homology,
eventual vanishing, finite-stage exact representatives, and faithful exact field
tensor. The canonical comparison maps are those of Mathlib preservation of
homology; in particular these assertions retain the cone/truncation kernel and
cokernel maps supplied by the recorded heart-triangle theorem.
Source: BS 6.8.14 (blueprint: def-per-common-stage-fibre-descent-interfaces). -/
structure CommonStageHeartExactness where
  [inclusion_additive : ∀ (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω),
    (stageHeart l Ω X A).Additive]
  inclusion_homology : ∀ (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω),
    (stageHeart l Ω X A).PreservesHomology
  inclusion_image : ∀ (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω)
    (F G : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)) (f : F ⟶ G),
    ∃ e : (stageHeart l Ω X A).obj (image f) ≅ image ((stageHeart l Ω X A).map f),
      e.hom ≫ image.ι ((stageHeart l Ω X A).map f) =
        (stageHeart l Ω X A).map (image.ι f) ∧
      (stageHeart l Ω X A).map (factorThruImage f) ≫ e.hom =
        factorThruImage ((stageHeart l Ω X A).map f)
  eventual_zero : ∀ (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω)
    (F : pbcStageCategory l Ω X.scheme A),
    IsZero (((pbcScalarSystem l Ω X.scheme (base l X).dimension
      (base l X).prime_unit).ι A).obj F) ↔
      ∃ (B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
        IsZero (((pbcScalarSystem l Ω X.scheme (base l X).dimension
          (base l X).prime_unit).T h).obj F)
  finite_complex_stage : ∀ (X : FiniteTypeBase k) (ι : Type w) [Finite ι]
    (c : ComplexShape ι)
    (K : HomologicalComplex (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory c),
    ∃ (A : Padic.FiniteCoefficientFields l Ω)
      (K₀ : HomologicalComplex
        (NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)) c),
      Nonempty (K ≅ ((stageHeart l Ω X A).mapHomologicalComplex c).obj K₀)
  short_exact_stage : ∀ (X : FiniteTypeBase k)
    (S : ShortComplex (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
    S.ShortExact → ∃ (A : Padic.FiniteCoefficientFields l Ω)
      (S₀ : ShortComplex (NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X))),
      S₀.ShortExact ∧ Nonempty (S ≅ S₀.map (stageHeart l Ω X A))
  [scalar_additive : ∀ A : Padic.FiniteCoefficientFields l Ω,
    (ModuleCat.extendScalars.{u, v, u + 1} (stageEmbedding l Ω A)).Additive]
  scalar_faithful : ∀ A : Padic.FiniteCoefficientFields l Ω,
    (ModuleCat.extendScalars.{u, v, u + 1} (stageEmbedding l Ω A)).Faithful
  scalar_homology : ∀ A : Padic.FiniteCoefficientFields l Ω,
    (ModuleCat.extendScalars.{u, v, u + 1} (stageEmbedding l Ω A)).PreservesHomology
  scalar_unit_injective : ∀ (A : Padic.FiniteCoefficientFields l Ω)
    (W : ModuleCat.{u + 1} (pbcFiniteField.{u} l Ω A)),
    Function.Injective (fun w : W ↦
      (1 : Ω) ⊗ₜ[pbcFiniteField.{u} l Ω A, stageEmbedding l Ω A] w)

/-- The prescribed scalar descent equation, including the normalized tensor associator.
Source: BS 6.8.14 (blueprint: def-per-common-stage-fibre-descent-interfaces). -/
@[irreducible] def CommonStageScalarCompatibility (ω : Fibres (k := k) l R)
    (α : NormalizedPullback l R ω) (β : NormalizedScalar l R ω α)
    (point : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x) : Prop :=
  ∀ (X : FiniteTypeBase k) (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    ∃ z : ModuleCat.extendScalars (pbcFiniteFieldInclusion l Ω h).toRingHom ⋙
        ModuleCat.extendScalars (stageEmbedding l Ω B) ≅
          ModuleCat.extendScalars (stageEmbedding l Ω A),
    ∃ e : heartScalar l (pbcFiniteField.{u} l Ω A) (pbcFiniteField.{u} l Ω B)
        (pbcFiniteFieldInclusion l Ω h) X ⋙ stageHeart l Ω X B ≅ stageHeart l Ω X A,
      (∀ (M : ModuleCat.{u + 1} (pbcFiniteField.{u} l Ω A)),
        ∀ (a : pbcFiniteField.{u} l Ω B) (b : Ω) (m : M),
          z.hom.app M (b ⊗ₜ[pbcFiniteField.{u} l Ω B, stageEmbedding l Ω B]
            (a ⊗ₜ[pbcFiniteField.{u} l Ω A,
              (pbcFiniteFieldInclusion l Ω h).toRingHom] m)) =
              (b * stageEmbedding l Ω B a) ⊗ₜ[pbcFiniteField.{u} l Ω A, stageEmbedding l Ω A] m) ∧
      (∀ F, HEq (e.hom.app F).hom
        (((pbcScalarSystem l Ω X.scheme (base l X).dimension
          (base l X).prime_unit).transIso h).hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)),
        HEq ((point X κ x).functor.map (e.hom.app F) ≫
          ((point X κ x).finite_stage A).hom.app F)
          (((point X κ x).finite_stage B).hom.app
              ((heartScalar l (pbcFiniteField.{u} l Ω A) (pbcFiniteField.{u} l Ω B)
                (pbcFiniteFieldInclusion l Ω h) X).obj F) ≫
            (ModuleCat.extendScalars (stageEmbedding l Ω B)).map
              ((β.scalar (pbcFiniteField.{u} l Ω A) (pbcFiniteField.{u} l Ω B)
                (pbcFiniteFieldInclusion l Ω h) X κ x).hom.app F) ≫
            z.hom.app
                (((ω (pbcFiniteField.{u} l Ω A) X).point κ x).functor.obj F))

/-- The prescribed finite pullback comparison equation.
Source: BS 6.8.15 (blueprint: def-per-common-stage-fibre-descent-interfaces). -/
@[irreducible] def CommonStagePullCompatibility (ω : Fibres (k := k) l R)
    (α : NormalizedPullback l R ω)
    (point : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x)
    (pull : ∀ {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme),
    commonHeartPull l Ω g ⋙ (point Y κ y).functor ≅ (point X κ (y ≫ g)).functor) : Prop :=
  ∀ (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (A : Padic.FiniteCoefficientFields l Ω),
    ∃ e : stageHeart l Ω X A ⋙ commonHeartPull l Ω g ≅
        heartPull l (pbcFiniteField.{u} l Ω A) R g ⋙ stageHeart l Ω Y A,
      (∀ F, HEq (e.hom.app F).hom (𝟙
        ((pbcQbarCompletedPull l Ω g).obj ((stageHeart l Ω X A).obj F).obj))) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (F : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)),
        (pull g κ y).hom.app ((stageHeart l Ω X A).obj F) ≫
            ((point X κ (y ≫ g)).finite_stage A).hom.app F =
          (point Y κ y).functor.map (e.hom.app F) ≫
            ((point Y κ y).finite_stage A).hom.app
              ((heartPull l (pbcFiniteField.{u} l Ω A) R g).obj F) ≫
            (ModuleCat.extendScalars (stageEmbedding l Ω A)).map
              ((α.pull (pbcFiniteField.{u} l Ω A) g κ y).hom.app F)

/-- Identity coherence of the descended pull comparison.
Source: BS 6.8.15 (blueprint: def-per-common-stage-fibre-descent-interfaces). -/
@[irreducible] def CommonStagePullIdentity (ω : Fibres (k := k) l R)
    (point : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x)
    (pull : ∀ {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme),
    commonHeartPull l Ω g ⋙ (point Y κ y).functor ≅ (point X κ (y ≫ g)).functor) : Prop :=
  ∀ (X : FiniteTypeBase k),
    ∃ e : commonHeartPull l Ω (𝟙 X.scheme) ≅ 𝟭 _,
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
        HEq ((pull (𝟙 X.scheme) κ x).hom.app F)
          ((point X κ x).functor.map (e.hom.app F))

/-- Composite coherence of the descended pull comparison.
Source: BS 6.8.15 (blueprint: def-per-common-stage-fibre-descent-interfaces). -/
@[irreducible] def CommonStagePullComposition (ω : Fibres (k := k) l R)
    (point : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x)
    (pull : ∀ {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme),
    commonHeartPull l Ω g ⋙ (point Y κ y).functor ≅ (point X κ (y ≫ g)).functor) : Prop :=
  ∀ (X Y Z : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (h : Z.scheme ⟶ Y.scheme),
    ∃ e : commonHeartPull l Ω (h ≫ g) ≅ commonHeartPull l Ω g ⋙ commonHeartPull l Ω h,
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (z : Spec (.of κ) ⟶ Z.scheme)
        (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
        HEq ((pull (h ≫ g) κ z).hom.app F)
          ((point Z κ z).functor.map (e.hom.app F) ≫
            (pull h κ z).hom.app ((commonHeartPull l Ω g).obj F) ≫
              (pull g κ (z ≫ h)).hom.app F)

/-- The normalized functor and comparison data, before joint detection.
Source: BS 6.8.14--6.8.15 (blueprint: def-per-common-stage-fibre-descent-interfaces). -/
structure CommonStageFibreTransport (ω : Fibres (k := k) l R)
    (α : NormalizedPullback l R ω) (β : NormalizedScalar l R ω α) where
  point : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x
  pull : ∀ {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme),
    commonHeartPull l Ω g ⋙ (point Y κ y).functor ≅ (point X κ (y ≫ g)).functor
  scalar : CommonStageScalarCompatibility l R Ω ω α β point
  pull_finite : CommonStagePullCompatibility l R Ω ω α point pull
  identity : CommonStagePullIdentity l R Ω ω point pull
  composition : CommonStagePullComposition l R Ω ω point pull

/-- The common-heart descent assertion for the supplied normalized finite fibres.
Source: BS 6.8.14--6.8.15 (blueprint: def-per-common-stage-fibre-descent-interfaces). -/
structure CommonStageFibreDescent (ω : Fibres (k := k) l R)
    (α : NormalizedPullback l R ω) (β : NormalizedScalar l R ω α)
    extends CommonStageFibreTransport l R Ω ω α β where
  heart_exactness : CommonStageHeartExactness.{u, v, w} l Ω (k := k)
  detects_zero : ∀ (X : FiniteTypeBase k)
    (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsZero ((point X κ x).functor.obj F)) ↔ IsZero F
  detects_iso : ∀ (X : FiniteTypeBase k)
    (F G : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsIso ((point X κ x).functor.map f)) ↔ IsIso f
  detects_zero_map : ∀ (X : FiniteTypeBase k)
    (F G : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      (point X κ x).functor.map f = 0) ↔ f = 0
  detects_short_exact : ∀ (X : FiniteTypeBase k)
    (S : ShortComplex (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
    S.ShortExact ↔ ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ X.scheme), (S.map (point X κ x).functor).ShortExact

end AlgebraicGeometry.Scheme.AdicFibreComparison
