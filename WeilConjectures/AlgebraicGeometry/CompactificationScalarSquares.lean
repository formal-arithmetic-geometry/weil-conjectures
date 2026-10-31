/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimitSupport
import WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteQuotientHomExt
import all WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData

/-! # Completed coefficient projection squares
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-scalar-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private noncomputable local instance fixedCommRingSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T

private def ellQuotientFactor (n k : ℕ)
    (hk : Padic.coefficientExtensionIdeal l E (k + 1) ≤ spEllIdeal l E ^ (n + 1)) :
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (k + 1))) ⟶
      rings.{u} l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factor hk).comp ULift.ringEquiv.toRingHom))

private theorem ellProjection_factor (T : Scheme.{u}) (n k : ℕ)
    (hk : Padic.coefficientExtensionIdeal l E (k + 1) ≤ spEllIdeal l E ^ (n + 1)) :
    spCompletedEllCommProjection.{u} l E T n =
      completedIntegralCommRingProjectionUnrestricted.{u, u} l E T k ≫
        (constantSheaf.{u, u + 1, u + 1, u + 2}
          (ProEt.topology T) CommRingCat.{u + 1}).map
          (ellQuotientFactor.{u} l E n k hk) := by
  let F := sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  apply completedIntegralFiniteQuotientHom_ext.{u, u} l E T
    (spEllIdeal l E ^ (n + 1)) ⟨k, hk⟩
  · simp only [F, spCompletedEllCommProjection, CategoryTheory.Functor.map_preimage]
    exact (sp_completed_coefficient_limit.{u, u} l E T).exists.choose_spec n
  · rw [Functor.map_comp, ← Category.assoc]
    change (integralConstantToCompletionOfUniverses.{u, u} l E T ≫
        limit.π (integralCoefficientSheafSystem.{u, u} l E T) (op k)) ≫ _ = _
    dsimp only [integralConstantToCompletionOfUniverses]
    erw [limit.lift_π]
    change integralConstantQuotientOfUniverses.{u, u} l E T k ≫ _ = _
    unfold integralConstantQuotientOfUniverses
    rw [← F.map_comp, ← Functor.map_comp]
    congr 2

private theorem ellProjection_square {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((PurCompactSupport.completed.{u} l E).pull f).hom ≫ spCompletedEllCommProjection.{u} l E X n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (spCompletedEllCommProjection.{u} l E Y n) ≫
        ((finiteCoefficients.{u} l E n).pull f).hom := by
  obtain ⟨k, hk⟩ := (sp_coefficient_ideals_cofinal l E).2 (n + 1)
  have hk' : Padic.coefficientExtensionIdeal l E (k + 1) ≤
      spEllIdeal l E ^ (n + 1) := (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  rw [ellProjection_factor l E X n k hk', ellProjection_factor l E Y n k hk']
  rw [← Category.assoc]
  change (PurCompactSupport.completedPullMap l E f ≫
    completedIntegralCommRingProjectionUnrestricted.{u, u} l E X k) ≫ _ = _
  erw [PurCompactSupport.completedPull_projection]
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (proEtaleConstantInverseImageMap_naturality f
    (a := ellQuotientFactor.{u} l E n k hk')).symm

/-- The actual completed-to-ell-quotient maps commute with geometric inverse image.
Source: blueprint direct-image proof, paragraph (2), coefficient compatibility;
Stacks Project, Tags 03DI and 03D7.
(blueprint: lem-sp-compactification-scalar-squares).

Proof: factor the ell-power quotient through a sufficiently deep uniformizer quotient.
The resulting map from completed coefficients agrees on constant integer sections with
the canonical ell-power projection, so finite-quotient uniqueness identifies them.
The completed coefficient pullback is compatible with every uniformizer projection.
Naturality of constant-sheaf pullback for the quotient factor then proves the required
ell-power square. -/
theorem compactificationScalarSquares : ScalarSquares l E := by
  intro n
  exact ⟨{ map := fun T ↦ spCompletedEllCommProjection.{u} l E T n
           square := fun f ↦ ellProjection_square l E f n }, fun T ↦ rfl⟩

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
