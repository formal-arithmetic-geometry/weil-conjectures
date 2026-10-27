/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.IntegralHeartLocalModelData
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.Paper.SmallIntegralRoosCompletenessTransport
import Sheaf.AlgebraicGeometry.IntegralConstantModelConstructibility
import all Sheaf.Paper.IntegralConstantModelHeartClosure
import all Sheaf.Paper.IntegralCohomologicalAdicCriterion
import Mathlib.Algebra.Field.ULift

/-! # Completeness of constructible integral module sheaves

Source: the current blueprint, integral-heart-local-model, clause (2), Completeness.
(blueprint: lem-sfb-integral-heart-constructible-module-complete)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralConstantModel.modulesFunctor

private instance liftFinite (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] :
    FiniteDimensional (Padic ℓ) (ULift.{u} F) :=
  (ULift.moduleEquiv (R := Padic ℓ) (M := F)).symm.finiteDimensional

private theorem liftAbsoluteValue (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] (x : ULift.{u} F) :
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} F) x =
      Padic.coefficientExtensionAbsoluteValue ℓ F x.down := by
  let a := Padic.coefficientExtensionAbsoluteValue ℓ F
  let b : AbsoluteValue (ULift.{u} F) ℝ :=
    { toFun := fun y ↦ a y.down
      map_mul' := fun y z ↦ a.map_mul y.down z.down
      nonneg' := fun y ↦ a.nonneg y.down
      eq_zero' := fun y ↦ by
        constructor
        · intro hy
          apply ULift.ext
          exact a.eq_zero.mp hy
        · rintro rfl
          exact map_zero a
      add_le' := fun y z ↦ a.add_le y.down z.down }
  have hb : ∀ y : Padic ℓ, b (algebraMap (Padic ℓ) (ULift.{u} F) y) = ‖y‖ := by
    intro y
    exact spectralNorm_extends (K := Padic ℓ) (L := F) y
  exact (spectralNorm_unique_field_norm_ext hb x).symm

private theorem liftMemIntegers (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] (x : ULift.{u} F) :
    x ∈ Padic.coefficientExtensionIntegers ℓ (ULift.{u} F) ↔
      x.down ∈ Padic.coefficientExtensionIntegers ℓ F := by
  have h₁ := (Padic.extension_integers_dvr ℓ (ULift.{u} F)
    (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} F))
    (spectralNorm_extends (K := Padic ℓ) (L := ULift.{u} F))).choose_spec.choose_spec.1 x
  have h₂ := (Padic.extension_integers_dvr ℓ F
    (Padic.coefficientExtensionAbsoluteValue ℓ F)
    (spectralNorm_extends (K := Padic ℓ) (L := F))).choose_spec.choose_spec.1 x.down
  rw [liftAbsoluteValue] at h₁
  exact h₁.trans h₂.symm

attribute [local irreducible] Padic.coefficientExtensionIntegers

private def liftIntegers (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] :
    Padic.coefficientExtensionIntegers ℓ F ≃+*
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} F) where
  toFun x := ⟨ULift.up x.val, (liftMemIntegers ℓ F _).2 x.property⟩
  invFun x := ⟨x.val.down, (liftMemIntegers ℓ F _).1 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def liftIntegerHomeo (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] :
    letI := spectralNorm.normedField (Padic ℓ) F
    letI nf := spectralNorm.normedField (Padic ℓ) (ULift.{u} F)
    letI : TopologicalSpace (ULift.{u} F) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Padic.coefficientExtensionIntegers ℓ F ≃ₜ
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} F) := by
  letI src := spectralNorm.normedField (Padic ℓ) F
  letI tgt := spectralNorm.normedField (Padic ℓ) (ULift.{u} F)
  letI : TopologicalSpace (ULift.{u} F) :=
    tgt.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := liftIntegers.{u} ℓ F
  let sm : MetricSpace (Padic.coefficientExtensionIntegers ℓ F) :=
    @Subtype.metricSpace F _ src.toMetricSpace
  let tm : MetricSpace (Padic.coefficientExtensionIntegers ℓ (ULift.{u} F)) :=
    @Subtype.metricSpace (ULift.{u} F) _ tgt.toMetricSpace
  letI : PseudoEMetricSpace (Padic.coefficientExtensionIntegers ℓ F) :=
    sm.toPseudoMetricSpace.toPseudoEMetricSpace
  letI : PseudoEMetricSpace (Padic.coefficientExtensionIntegers ℓ (ULift.{u} F)) :=
    tm.toPseudoMetricSpace.toPseudoEMetricSpace
  have hi : @Isometry _ _ sm.toPseudoMetricSpace.toPseudoEMetricSpace
      tm.toPseudoMetricSpace.toPseudoEMetricSpace e := by
    apply @Isometry.of_dist_eq _ _ sm.toPseudoMetricSpace tm.toPseudoMetricSpace
    intro x y
    change spectralNorm (Padic ℓ) (ULift.{u} F) (ULift.up x.val - ULift.up y.val) =
      spectralNorm (Padic ℓ) F (x.val - y.val)
    exact liftAbsoluteValue ℓ F _
  exact { e.toEquiv with
    continuous_toFun := hi.continuous
    continuous_invFun := (hi.right_inv e.right_inv).continuous }

private def liftPointIso (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F] :
    letI := spectralNorm.normedField (Padic ℓ) F
    Mon.mk (Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ F)) ≅
      sfbCondensedIntegers ℓ (ULift.{u} F) := by
  letI := spectralNorm.normedField (Padic ℓ) F
  letI tgt := spectralNorm.normedField (Padic ℓ) (ULift.{u} F)
  letI : TopologicalSpace (ULift.{u} F) :=
    tgt.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ (ULift.{u} F))) :=
    Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheafOfUniverse
        (Padic.coefficientExtensionIntegers ℓ (ULift.{u} F)))
  let e := liftIntegers.{u} ℓ F
  let h := liftIntegerHomeo.{u} ℓ F
  let forward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ F) →+*
        ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ (ULift.{u} F)) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous _ h.continuous_toFun).comp ULift.ringEquiv.toRingHom)
  let backward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ (ULift.{u} F)) →+*
        ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ℓ F) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous _ h.continuous_invFun).comp
        ULift.ringEquiv.toRingHom)
  let i : Profinite.continuousMapRingSheaf.{u} (Padic.coefficientExtensionIntegers ℓ F) ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ (ULift.{u} F)) :=
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := by ext S x; apply ULift.ext; ext t; rfl
      inv_hom_id := by ext S x; apply ULift.ext; ext t; rfl }
  let G := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : IsMonHom (G.mapIso i).hom := Sheaf.isMonHom_sheafCompose_map _ i.hom
  exact Mon.mkIso' (G.mapIso i)

/-- A constructible integral module sheaf in degree zero is complete for the
explicit K-flat positive-reduction Roos augmentation used by the integral heart.

Source: Stacks Tags 099I, 099L, 099Q(5); Bhatt--Scholze, Proposition 6.8.11(3);
the current blueprint integral-heart-local-model, clause (2), Completeness.
(blueprint: lem-sfb-integral-heart-constructible-module-complete)

Proof: lift the canonical small presentation of E to the scheme universe.
Uniqueness of the extended absolute value identifies the integer subrings and
makes their ring equivalence an isometry. Postcomposition on continuous functions
therefore gives an isomorphism of condensed coefficient rings. Restriction along
this isomorphism preserves the finite constant local models of C. The normalized
section-action equivalence identifies them with completed finitely presented scalar
models. Such a module in degree zero is stratified perfect by the two-term free
resolution over the coefficient DVR. The adic stratified-perfect criterion then
makes this object locally derived complete. The exact-functor/single-complex
comparison identifies it with the derived realization of C in degree zero.
Apply smallIntegralRoosCompletenessTransport to this local-completeness assertion.
That comparison identifies the canonical quotient-tower completion unit with the
specified small-coefficient augmentation on a K-flat representative: its first
coordinate is the product of quotient units, and its second coordinate is zero.
The resulting invertibility is exactly SmallAdicCompletion.IsDerivedComplete.
This also treats zero modules, torsion modules and the empty scheme. -/
theorem integralHeart_constructible_module_complete
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (C : SmallAdicCompletion.Modules ℓ E X)
    (hC : IsConstantModelConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C) :
    SmallAdicCompletion.IsDerivedComplete ℓ E X
      ((DerivedCategory.singleFunctor _ 0).obj C) := by
  let F := ULift.{u} (SmallAdicCompletion.Coefficients.field ℓ E)
  let e : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) ≅
      sfbCondensedIntegers ℓ F :=
    liftPointIso.{u} ℓ (SmallAdicCompletion.Coefficients.field ℓ E)
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.inv.hom X)
  let H := IntegralConstantModel.modulesFunctor ℓ F X
  have hG : IsConstantModelConstructible (sfbCondensedIntegers ℓ F).X X (G.obj C) :=
    (constantModel_comap_iff e.inv.hom X C).mpr hC
  have hM := (IntegralConstantModel.constructible_iff ℓ F X (G.obj C)).mp hG
  let R := IntegralConstantCompletion.integers ℓ F
  let I := IntegralConstantCompletion.ideal ℓ F
  obtain ⟨hR, hc, hI⟩ := Scheme.integralCoefficients ℓ F
  have : IsDiscreteValuationRing R := hR
  have : IsAdicComplete I R := hc
  obtain ⟨hequiv, _, _, hiso, _, _⟩ := Scheme.adic_stratified_perfect X R I hI
  have hs := (hequiv _).mpr (Scheme.perfect_of_completedStratified X I (H.obj (G.obj C)) hM)
  have hK := hiso _ _ ⟨((G ⋙ H).mapDerivedCategorySingleFunctor 0).symm.app C⟩ hs
  exact smallIntegralRoosCompletenessTransport ℓ E F e X _ hK.1

end AlgebraicGeometry.ProEtale
