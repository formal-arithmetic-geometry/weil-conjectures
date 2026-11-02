/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives

/-! # Scalar extension of coherent systems is unital and associative

The whole-system scalar tensorator `ScalarExtensionTower.derivedSigma` is compatible with the
associators and unitors of the published coherent system monoidal structures.

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-pur-system-scalar-tensor-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard pullbackTensorCalculus
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

/-- The normalized whole-system scalar tensorator is associative.

Source: Stacks 07A4, total tensor construction; the scalar calculation of
lem-pur-system-scalar-tensor-braiding.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof plan: take simultaneous flat-term K-flat representatives. By `DerivedSigmaModel` the
derived scalar tensorator is the localization of the strict scalar tensorator, conjugated by
the fixed tensor models and scalar counits; the system associators are the localizations of the
total reassociation maps with the same models. On a homogeneous local tensor both strict routes
send `c ⊗ ((x ⊗ y) ⊗ z)` to `(c x) ⊗ (y ⊗ z)` without a sign. These generators span the
sheafified total tensors, so the chain maps agree; localize and extend by naturality. -/
theorem systemScalarTensorAssociativity
    (M N P : coefficientSequenceDerived l E W) :
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    let σ := ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
    H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator M N P).hom ≫
      σ.hom.app (M, (pullbackTensorCalculus l E W).systemClosed.tensor.obj (N, P)) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) (σ.hom.app (N, P))) =
    σ.hom.app ((pullbackTensorCalculus l E W).systemClosed.tensor.obj (M, N), P) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (σ.hom.app (M, N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l L W).systemClosed.monoidal.associator
        (H.obj M) (H.obj N) (H.obj P)).hom := by
  sorry

/-- Scalar extension of coherent systems sends the coefficient-ring unit to the
coefficient-ring unit.

Source: Stacks 03EL; extension of scalars of a free module of rank one.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof plan: the coherent unit is the degree-zero single complex on the structure sheaf; it is
flat-term K-flat, so the scalar model computes its derived extension by the underived one, and
extension of scalars of the structure sheaf is the structure sheaf. -/
theorem systemScalarTensorUnitObject :
    Nonempty ((integralComparisonDerivedSequenceScalar l E L ι W).obj
        (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit) := by
  sorry

universe a b c d in
private theorem scalarAssociativity_from_tensorHom
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (h : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          (𝟙 (F.obj A) ⊗ₘ (μ.app (B, M)).hom) =
        (μ.app (A ⊗ B, M)).hom ≫ ((μ.app (A, B)).hom ⊗ₘ 𝟙 (F.obj M)) ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) (A B M : C) :
    F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
        F.obj A ◁ (μ.app (B, M)).hom =
      (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
        (α_ (F.obj A) (F.obj B) (F.obj M)).hom := by
  have h' := h A B M
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h' ⊢
  simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using h'

/-- Both unit equations for the normalized whole-system scalar tensorator.

Source: Stacks 03EL and 07A4.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: the associativity equation and any identification of the scalar extension of the unit
are combined by the monoidal unit extraction lemma. -/
theorem systemScalarTensorUnit :
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    let σ := ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
    ∃ ε : H.obj (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit,
      ∀ M : coefficientSequenceDerived l E W,
        (σ.hom.app ((pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit, M) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor (H.obj M)).hom =
        H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor M).hom) ∧
        (σ.hom.app (M, (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor (H.obj M)).hom =
        H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor M).hom) := by
  letI : MonoidalCategory (coefficientSequenceDerived l E W) :=
    (pullbackTensorCalculus l E W).systemClosed.monoidal
  letI : MonoidalCategory (coefficientSequenceDerived l L W) :=
    (pullbackTensorCalculus l L W).systemClosed.monoidal
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let σ := ScalarExtensionTower.derivedSigma l E L ι W
    (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
  obtain ⟨e⟩ := systemScalarTensorUnitObject l E L ι W
  have hAssoc := scalarAssociativity_from_tensorHom H σ
    (systemScalarTensorAssociativity l E L ι W)
  obtain ⟨ε, hL, hR⟩ := unit_from_tensor H σ e hAssoc
  exact ⟨ε, fun M ↦ ⟨hL M, hR M⟩⟩

end WeilConjectures
