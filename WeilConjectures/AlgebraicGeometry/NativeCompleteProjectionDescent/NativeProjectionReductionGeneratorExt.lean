/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionReductionPresentation
public import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

/-! # Quotient augmentation generators of the native ordinary reduction

Source: current blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, (3)
(blueprint: def-sp-projection-reduction-presentation).

## Main statements

* `ordinaryReduction_map_apply_reductionGenerator`: ordinary reduction of a map sends the quotient
  augmentation `1 ⊗ x` to `1 ⊗ f x`.
* `ordinaryReduction_tensor_hom_ext`: maps out of the reduction of a total tensor term are
  determined by their values on the reductions of total-summand pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

section OrdinaryTensorHomExt

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]

/-- Maps out of the ordinary sheaf tensor agree if they agree on local pure tensors.
Source: Stacks 03EK (blueprint: def-sp-projection-reduction-presentation).
Proof: the tensor is the sheafification of the presheaf tensor; use the sheafification
adjunction and sectionwise tensor induction. -/
theorem ordinaryTensor_hom_ext
    (R : Sheaf J CommRingCat.{max c v r})
    (M N P : Mod.{c, v, max c v r} J R)
    {f g : ordinaryTensor.{c, v, r} J R M N ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (tensorSection.{c, v, r} J R M N U x y) =
        g.val.app U (tensorSection.{c, v, r} J R M N U x y)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (R := ring.{c, v, max c v r} J R) (𝟙 _)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N).inv).mp
  apply (adj.homEquiv _ P).injective
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  change f.val.app U ((SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      M N).inv.val.app U ((adj.unit.app _).app U z)) =
    g.val.app U ((SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      M N).inv.val.app U ((adj.unit.app _).app U z))
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h U x y
  | add z w hz hw => simp only [map_add, hz, hw]

end WeilConjectures.SemilinearSections

end OrdinaryTensorHomExt

section SequenceHomExt

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The level-`n` slice of a map out of the sequence sheaf of a strict system.
It has the same section maps as the original map.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def strictSystemSequenceLevelHom {M : StrictRingSystem B} {N : systemSequenceModules B}
    (α : (strictSystemToSequenceFunctor B).obj M ⟶ N) (n : ℕ) :
    M.level n ⟶ (systemSequenceEvaluation B n).obj N :=
  (strictSystemSequenceUnitLevel B M n).hom ≫ (systemSequenceEvaluation B n).map α

theorem strictSystemSequenceLevelHom_apply {M : StrictRingSystem B}
    {N : systemSequenceModules B} (α : (strictSystemToSequenceFunctor B).obj M ⟶ N) (n : ℕ)
    (U : Cᵒᵖ) (x : (M.level n).val.obj U) :
    (strictSystemSequenceLevelHom B α n).val.app U x = α.val.app (op (n, U.unop)) x :=
  rfl

/-- Maps out of the sequence sheaf of a strict system are determined by their slices.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
theorem strictSystemSequence_hom_ext {M : StrictRingSystem B} {N : systemSequenceModules B}
    (α β : (strictSystemToSequenceFunctor B).obj M ⟶ N)
    (h : ∀ n, strictSystemSequenceLevelHom B α n = strictSystemSequenceLevelHom B β n) :
    α = β := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨n, U⟩
  ext x
  exact congrArg (fun g ↦ g.val.app (op U) x) (h n)

end SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- The transpose of a map out of a scalar extension evaluates sections through the
normalized unit tensor `1 ⊗ x`.
Source: Stacks 03D7 (blueprint: lem-pur-system-scalar-coherence). -/
theorem SheafOfModules.systemScalarModel_homEquiv_apply {R S : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ S} (A : SheafOfModules.SystemScalarModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (M : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))
    (f : A.model.E.obj P ⟶ M) (U : Cᵒᵖ) (x : P.val.obj U) :
    (A.ordinaryAdj.homEquiv P M f).val.app U x =
      f.val.app U (SheafOfModules.systemModelTmul A.model P U 1 x) := by
  rw [Adjunction.homEquiv_unit, ← A.unit_normalized]
  rfl

end SequenceHomExt

attribute [local instance] AlgebraicGeometry.ProEtale.SpReductionTower.additive

universe u

open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Maps out of the section presentation of a total tensor term are determined by
total-summand pure tensors.
Source: Stacks 03EL, 06YN (blueprint: def-sp-projection-reduction-presentation).
Proof: the term is a coproduct of summand tensors; each summand is the ordinary section
tensor through the normalized comparison, generated by local pure tensors. -/
theorem sectionTensor_hom_ext (T : Scheme.{u}) (P Q : CochainComplex (Modules l E T) ℤ)
    (k : ℤ) {Y : spIntegralSectionModules l E T}
    (ψ ψ' : (spIntegralModuleEquivalence l E T).functor.obj ((P ⊗ Q).X k) ⟶ Y)
    (h : ∀ (a b : ℤ) (hab : a + b = k) (U : T.ProEtᵒᵖ)
      (x : ((spIntegralModuleEquivalence l E T).functor.obj (P.X a)).val.obj U)
      (y : ((spIntegralModuleEquivalence l E T).functor.obj (Q.X b)).val.obj U),
      ψ.val.app U (tensorGenerator l E T P Q a b k hab U x y) =
        ψ'.val.app U (tensorGenerator l E T P Q a b k hab U x y)) :
    ψ = ψ' := by
  let e := spIntegralModuleEquivalence l E T
  apply (e.toAdjunction.homEquiv _ _).injective
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  refine (e.toAdjunction.homEquiv_naturality_left
    (HomologicalComplex.ιTensorObj P Q a b k hab) ψ).symm.trans
      (Eq.trans ?_ (e.toAdjunction.homEquiv_naturality_left
        (HomologicalComplex.ιTensorObj P Q a b k hab) ψ'))
  congr 1
  apply (cancel_epi (ModuleRingedComparison.ordinaryTensorComparison
    (spIntegralCondensed l E) T (P.X a) (Q.X b)).inv).mp
  apply ordinaryTensor_hom_ext.{u + 1, u, u + 1}
  intro U x y
  exact h a b hab U x y

/-- Ordinary reduction of a map sends the quotient augmentation `1 ⊗ x` to `1 ⊗ f x`.
Source: Stacks 03EK (blueprint: def-sp-projection-reduction-presentation).
Proof: naturality of the level identification and the scalar-extension formula on
pure tensors. -/
theorem ordinaryReduction_map_apply_reductionGenerator (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    {M M' : Modules l E T} (f : M ⟶ M') (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    ((ordinaryReduction l E T D R).map f).val.app (op (n, U.unop))
        (reductionGenerator l E T D R M n U x) =
      reductionGenerator l E T D R M' n U
        (((spIntegralModuleEquivalence l E T).functor.map f).val.app U x) := by
  have hn := congrArg (fun g ↦ g.val.app U (SheafOfModules.systemModelTmul
      (D.scalar (spIntegralReductionScalar l E T R.coefficient n)).model
      ((spIntegralModuleEquivalence l E T).functor.obj M) U 1 x))
    ((R.level n).inv.naturality ((spIntegralModuleEquivalence l E T).functor.map f))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.systemScalarModel_map_tmul] at hn
  exact hn.symm

/-- The scalar transpose of the level-`n` slice of a map out of an ordinary reduction
evaluates a section `x` as the map on the quotient augmentation `1 ⊗ x`.
Source: Stacks 03D7 (blueprint: def-sp-projection-reduction-presentation). -/
theorem reductionSequenceLevelTranspose_apply (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (X : Modules l E T) {N : VaryingRing.Modules (rings l E) (transitions l E) T}
    (α : (ordinaryReduction l E T D R).obj X ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj X).val.obj U) :
    (((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).ordinaryAdj.homEquiv _ _)
      ((R.level n).inv.app ((spIntegralModuleEquivalence l E T).functor.obj X) ≫
        SheafOfModules.strictSystemSequenceLevelHom (spCoefficientCommRings l E T)
          (M := D.equivalence.functor.obj
            (R.ordinary.obj ((spIntegralModuleEquivalence l E T).functor.obj X))) α n)).val.app
        U x =
      α.val.app (op (n, U.unop)) (reductionGenerator l E T D R X n U x) := by
  have key := SheafOfModules.systemScalarModel_homEquiv_apply
    (D.scalar (spIntegralReductionScalar l E T R.coefficient n))
    ((spIntegralModuleEquivalence l E T).functor.obj X) _
    ((R.level n).inv.app ((spIntegralModuleEquivalence l E T).functor.obj X) ≫
      SheafOfModules.strictSystemSequenceLevelHom (spCoefficientCommRings l E T)
        (M := D.equivalence.functor.obj
          (R.ordinary.obj ((spIntegralModuleEquivalence l E T).functor.obj X))) α n) U x
  refine key.trans ?_
  exact SheafOfModules.strictSystemSequenceLevelHom_apply (spCoefficientCommRings l E T) α n U _

/-- Maps out of the ordinary reduction of a total tensor term are determined by their
values on the quotient augmentations of total-summand pure tensors.
Source: Stacks 03EK, 03EL, 06YN (blueprint: def-sp-projection-reduction-presentation).
Proof: test level by level; at each level transpose along the scalar-extension
adjunction, whose transpose evaluates on `1 ⊗ x`, and use `sectionTensor_hom_ext`. -/
theorem ordinaryReduction_tensor_hom_ext (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (P Q : CochainComplex (Modules l E T) ℤ) (k : ℤ)
    {N : VaryingRing.Modules (rings l E) (transitions l E) T}
    (α β : (ordinaryReduction l E T D R).obj ((P ⊗ Q).X k) ⟶ N)
    (h : ∀ (a b : ℤ) (hab : a + b = k) (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : ((spIntegralModuleEquivalence l E T).functor.obj (P.X a)).val.obj U)
      (y : ((spIntegralModuleEquivalence l E T).functor.obj (Q.X b)).val.obj U),
      α.val.app (op (n, U.unop))
          (reductionGenerator l E T D R _ n U (tensorGenerator l E T P Q a b k hab U x y)) =
        β.val.app (op (n, U.unop))
          (reductionGenerator l E T D R _ n U (tensorGenerator l E T P Q a b k hab U x y))) :
    α = β := by
  refine SheafOfModules.strictSystemSequence_hom_ext (spCoefficientCommRings l E T)
    (M := D.equivalence.functor.obj
      (R.ordinary.obj ((spIntegralModuleEquivalence l E T).functor.obj ((P ⊗ Q).X k))))
    α β fun n ↦ ?_
  apply (cancel_epi ((R.level n).inv.app
    ((spIntegralModuleEquivalence l E T).functor.obj ((P ⊗ Q).X k)))).mp
  apply ((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).ordinaryAdj.homEquiv
    _ _).injective
  apply sectionTensor_hom_ext
  intro a b hab U x y
  refine (reductionSequenceLevelTranspose_apply l E T D R _ α n U _).trans
    (Eq.trans ?_ (reductionSequenceLevelTranspose_apply l E T D R _ β n U _).symm)
  exact h a b hab n U x y

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
