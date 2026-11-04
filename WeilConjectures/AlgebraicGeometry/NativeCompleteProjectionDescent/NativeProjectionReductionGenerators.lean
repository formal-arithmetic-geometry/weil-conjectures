/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionDescentMaps

/-! # Quotient augmentation generators of ordinary reductions

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

Maps out of the ordinary simultaneous reduction `ordinaryReduction (f^* M)` of an inverse image
are determined by their values on the quotient augmentation generators
`reductionGenerator (unit x)` of unit sections: at every level the reduction is the scalar
extension of the recorded scalar model (whose unit is the augmentation `x ↦ 1 ⊗ x`), and maps
out of an inverse image are determined by the adjunction unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance] AlgebraicGeometry.ProEtale.SpReductionTower.additive
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The level `n` component of a map out of an ordinary reduction, precomposed with the
recorded level identification. -/
def reductionLevelMap (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (N : Modules l E T)
    {W : VaryingRing.Modules (rings l E) (transitions l E) T}
    (α : (ordinaryReduction l E T D R).obj N ⟶ W) (n : ℕ) :=
  (R.level n).inv.app ((spIntegralModuleEquivalence l E T).functor.obj N) ≫
    (SheafOfModules.strictSystemSequenceUnitLevel (spCoefficientCommRings l E T)
      (D.equivalence.functor.obj
        (R.ordinary.obj ((spIntegralModuleEquivalence l E T).functor.obj N))) n).hom ≫
    (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map α

/-- The scalar transpose of `reductionLevelMap`. -/
def reductionLevelTranspose (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (N : Modules l E T)
    {W : VaryingRing.Modules (rings l E) (transitions l E) T}
    (α : (ordinaryReduction l E T D R).obj N ⟶ W) (n : ℕ) :=
  ((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).ordinaryAdj.homEquiv _ _)
    (reductionLevelMap T D R N α n)

theorem reductionLevelTranspose_apply (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (N : Modules l E T)
    {W : VaryingRing.Modules (rings l E) (transitions l E) T}
    (α : (ordinaryReduction l E T D R).obj N ⟶ W) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj N).val.obj U) :
    (reductionLevelTranspose T D R N α n).val.app U x =
      α.val.app (op (n, U.unop)) (reductionGenerator l E T D R N n U x) := by
  rw [reductionLevelTranspose, Adjunction.homEquiv_unit]
  exact congrArg (fun y ↦ (reductionLevelMap T D R N α n).val.app U y)
    ((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).unit_normalized _ U x)

/-- Maps out of an ordinary reduction are determined by their level transposes. -/
theorem ordinaryReduction_hom_ext_of_transpose (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D) (N : Modules l E T)
    {W : VaryingRing.Modules (rings l E) (transitions l E) T}
    (α β : (ordinaryReduction l E T D R).obj N ⟶ W)
    (h : ∀ n, reductionLevelTranspose T D R N α n = reductionLevelTranspose T D R N β n) :
    α = β := by
  have hl (n : ℕ) :
      (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map α =
        (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map β := by
    have hn := (Adjunction.homEquiv _ _ _).injective (h n)
    rwa [reductionLevelMap, reductionLevelMap, cancel_epi, cancel_epi] at hn
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun φ ↦ φ.val.app (op U.unop.2) x) (hl U.unop.1)

/-- Maps out of the section module of an inverse image are determined by their values on
unit sections. -/
theorem upperStar_section_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules l E Y)
    {W : spIntegralSectionModules l E X}
    (φ ψ : (spIntegralModuleEquivalence l E X).functor.obj ((ordinaryPull l E f).obj M) ⟶ W)
    (h : ∀ (U : Y.ProEt) (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op U)),
      φ.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op U) x) =
      ψ.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op U) x)) :
    φ = ψ := by
  let e := spIntegralModuleEquivalence l E X
  let c := e.counitIso.inv.app W
  rw [← cancel_mono c, ← e.fullyFaithfulFunctor.map_preimage (φ ≫ c),
    ← e.fullyFaithfulFunctor.map_preimage (ψ ≫ c)]
  congr 1
  apply ((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  have hφ := congrArg (fun g ↦ g.val.app (op ((Scheme.proEtaleBaseChange f).obj U.unop))
    (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
      M).hom.hom.app U x)) (e.fullyFaithfulFunctor.map_preimage (φ ≫ c))
  have hψ := congrArg (fun g ↦ g.val.app (op ((Scheme.proEtaleBaseChange f).obj U.unop))
    (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
      M).hom.hom.app U x)) (e.fullyFaithfulFunctor.map_preimage (ψ ≫ c))
  exact hφ.trans ((congrArg (fun y ↦ c.val.app _ y) (h U.unop x)).trans hψ.symm)

/-- Maps out of the ordinary reduction of an inverse image are determined by their values on
the quotient augmentation generators of unit sections. -/
theorem ordinaryReduction_upperStar_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : SpCoefficientTowersAbelian l E X) (R : SpReductionTower l E X D) (M : Modules l E Y)
    {W : VaryingRing.Modules (rings l E) (transitions l E) X}
    (α β : (ordinaryReduction l E X D R).obj ((ordinaryPull l E f).obj M) ⟶ W)
    (h : ∀ (U : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op U)) (n : ℕ),
      α.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (reductionGenerator l E X D R ((ordinaryPull l E f).obj M) n
          (op ((Scheme.proEtaleBaseChange f).obj U))
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op U) x)) =
      β.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (reductionGenerator l E X D R ((ordinaryPull l E f).obj M) n
          (op ((Scheme.proEtaleBaseChange f).obj U))
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op U) x))) :
    α = β :=
  ordinaryReduction_hom_ext_of_transpose X D R _ α β fun n ↦
    upperStar_section_hom_ext f M _ _ fun U x ↦ by
      rw [reductionLevelTranspose_apply, reductionLevelTranspose_apply]
      exact h U x n

/-- The quotient augmentation generators are natural in the module. -/
theorem ordinaryReduction_map_reductionGenerator (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    {N N' : Modules l E T} (φ : N ⟶ N') (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj N).val.obj U) :
    ((ordinaryReduction l E T D R).map φ).val.app (op (n, U.unop))
        (reductionGenerator l E T D R N n U x) =
      reductionGenerator l E T D R N' n U
        (((spIntegralModuleEquivalence l E T).functor.map φ).val.app U x) := by
  have h1 := congrArg (fun g ↦ g.val.app U
      (((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).ordinaryAdj.unit.app
        ((spIntegralModuleEquivalence l E T).functor.obj N)).val.app U x))
    ((R.level n).inv.naturality ((spIntegralModuleEquivalence l E T).functor.map φ))
  have h2 := congrArg (fun g ↦ g.val.app U x)
    ((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).ordinaryAdj.unit.naturality
      ((spIntegralModuleEquivalence l E T).functor.map φ))
  have hN := (D.scalar (spIntegralReductionScalar l E T R.coefficient n)).unit_normalized
    ((spIntegralModuleEquivalence l E T).functor.obj N) U x
  have hN' := (D.scalar (spIntegralReductionScalar l E T R.coefficient n)).unit_normalized
    ((spIntegralModuleEquivalence l E T).functor.obj N') U
    (((spIntegralModuleEquivalence l E T).functor.map φ).val.app U x)
  dsimp only at h1 h2
  rw [reductionGenerator, reductionGenerator, spReductionGenerator, spReductionGenerator,
    ← hN, ← hN']
  exact h1.symm.trans (congrArg (fun y ↦ ((R.level n).inv.app _).val.app U y) h2.symm)

/-- `ordinaryReduction_map_reductionGenerator` at an object of the site. -/
theorem ordinaryReduction_map_reductionGenerator_op (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    {N N' : Modules l E T} (φ : N ⟶ N') (n : ℕ) (U : T.ProEt)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj N).val.obj (op U)) :
    ((ordinaryReduction l E T D R).map φ).val.app (op (n, U))
        (reductionGenerator l E T D R N n (op U) x) =
      reductionGenerator l E T D R N' n (op U)
        (((spIntegralModuleEquivalence l E T).functor.map φ).val.app (op U) x) :=
  ordinaryReduction_map_reductionGenerator T D R φ n (op U) x

/-- The quotient augmentation generators are compatible with restriction. -/
theorem ordinaryReduction_restrict_reductionGenerator (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (N : Modules l E T) (n : ℕ) {V V' : T.ProEt} (a : V' ⟶ V)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj N).val.obj (op V)) :
    ((ordinaryReduction l E T D R).obj N).val.map (Prod.mkHom (𝟙 n) a).op
        (reductionGenerator l E T D R N n (op V) x) =
      reductionGenerator l E T D R N n (op V')
        (((spIntegralModuleEquivalence l E T).functor.obj N).val.map a.op x) := by
  have h := PresheafOfModules.naturality_apply
    (reductionLevelTranspose T D R N (𝟙 ((ordinaryReduction l E T D R).obj N)) n).val a.op x
  rw [reductionLevelTranspose_apply, reductionLevelTranspose_apply] at h
  exact h.symm

/-- The composition isomorphism of integral direct images restricts along the pullback pasting
isomorphism. -/
theorem lowerStarComp_hom_app_apply {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y)
    (N : Modules l E X) (U : Y.ProEt)
    (y : N.X.obj.obj (op ((Scheme.proEtaleBaseChange i).obj
      ((Scheme.proEtaleBaseChange g).obj U)))) :
    ((CondensedRing.lowerStarComp (spIntegralCondensed l E) i g).hom.app N).hom.hom.app (op U) y =
      N.X.obj.map ((MorphismProperty.Over.pullbackComp i g).hom.app U).op y :=
  rfl

/-- The composition isomorphism of integral inverse images on unit sections. -/
theorem upperStarComp_hom_app_unit {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y)
    (M : Modules l E Y) (U : Y.ProEt) (x : M.X.obj.obj (op U)) :
    ((CondensedRing.upperStarComp (spIntegralCondensed l E) i g).hom.app M).hom.hom.app
        (op ((Scheme.proEtaleBaseChange (i ≫ g)).obj U))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) (i ≫ g)).unit.app
          M).hom.hom.app (op U) x) =
      ((ordinaryPull l E i).obj ((ordinaryPull l E g).obj M)).X.obj.map
        ((MorphismProperty.Over.pullbackComp i g).hom.app U).op
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) i).unit.app
          ((ordinaryPull l E g).obj M)).hom.hom.app (op ((Scheme.proEtaleBaseChange g).obj U))
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
            M).hom.hom.app (op U) x)) := by
  have h := congrArg (fun φ ↦ φ.hom.hom.app (op U) x)
    (unit_conjugateEquiv_symm
      ((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).comp
        (CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) i))
      (CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) (i ≫ g))
      (CondensedRing.lowerStarComp (spIntegralCondensed l E) i g).hom M)
  exact h.symm

/-- `upperStarComp_hom_app_unit` on section modules. -/
theorem upperStarComp_hom_app_unit_section {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y)
    (M : Modules l E Y) (U : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op U)) :
    ((spIntegralModuleEquivalence l E X).functor.map
        ((CondensedRing.upperStarComp (spIntegralCondensed l E) i g).hom.app M)).val.app
        (op ((Scheme.proEtaleBaseChange (i ≫ g)).obj U))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) (i ≫ g)).unit.app
          M).hom.hom.app (op U) x) =
      ((spIntegralModuleEquivalence l E X).functor.obj
          ((ordinaryPull l E i).obj ((ordinaryPull l E g).obj M))).val.map
        ((MorphismProperty.Over.pullbackComp i g).hom.app U).op
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) i).unit.app
          ((ordinaryPull l E g).obj M)).hom.hom.app (op ((Scheme.proEtaleBaseChange g).obj U))
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
            M).hom.hom.app (op U) x)) :=
  upperStarComp_hom_app_unit i g M U x

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
