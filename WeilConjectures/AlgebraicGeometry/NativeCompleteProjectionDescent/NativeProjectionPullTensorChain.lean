/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionReductionGeneratorExt
public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionPullTensorUnit
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence

/-! # The chain-level pullback tensor identity

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

On cochain representatives, the ordinary reduction of the pullback tensorator, the tensor
presentation chain map, the ordinary pullback reduction comparison and the system tensor
pullback chain map compose to the pullback of the tensor presentation chain map: both send
the quotient augmentation of the pulled-back unit section of a tensor generator to the unit
section of the quotient tensor generator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The coefficient sequence site of the whole quotient system. -/
abbrev sysSite (T : Scheme.{u}) := coefficientSequenceTopology (Scheme.ProEt.topology T)

/-- The ring of the whole quotient system on the coefficient sequence site. -/
abbrev sysRing (T : Scheme.{u}) :=
  systemRing (Scheme.ProEt.topology T) (VaryingRing.coefficients (rings l E) T)
    (VaryingRing.coefficientTransition (rings l E) (transitions l E) T)

/-- The total tensor of chain maps sends a tensor generator to the tensor generator of the
images. -/
theorem totalTensor_map_coefficientTensorGenerator (T : Scheme.{u})
    {P P' Q Q' : CochainComplex (VaryingRing.Modules (rings l E) (transitions l E) T) ℤ}
    (φ : P ⟶ P') (ψ : Q ⟶ Q') (p q k : ℤ) (h : p + q = k) (U : (ℕ × T.ProEt)ᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((SemilinearSections.totalTensor.{u + 1, u, u + 1} (sysSite T) (sysRing l E T)).map
        (Prod.mkHom φ ψ)).f k).val.app U
        (coefficientTensorGenerator.{u + 1, u + 1, u} (sysSite T) (sysRing l E T)
          P Q p q k h U x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (sysSite T) (sysRing l E T)
        P' Q' p q k h U ((φ.f p).val.app U x) ((ψ.f q).val.app U y) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (sysRing l E T)
  let := SheafOfModules.monoidalCategory (sysRing l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (sysRing l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (sysRing l E T)
  have e : (SemilinearSections.totalTensor.{u + 1, u, u + 1} (sysSite T) (sysRing l E T)).map
      (Prod.mkHom φ ψ) =
      HomologicalComplex.mapBifunctorMap φ (𝟙 Q) (curriedTensor _) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 P') ψ (curriedTensor _) (.up ℤ) := rfl
  have key : HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q k h ≫
      ((SemilinearSections.totalTensor.{u + 1, u, u + 1} (sysSite T) (sysRing l E T)).map
        (Prod.mkHom φ ψ)).f k =
      (φ.f p ⊗ₘ ψ.f q) ≫
        HomologicalComplex.ιMapBifunctor P' Q' (curriedTensor _) (.up ℤ) p q k h := by
    rw [e, HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, curriedTensor_map_app, curriedTensor_obj_map, Category.assoc,
      MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_id]
    erw [Category.id_comp]
  have hk := congrArg (fun g ↦ g.val.app U
    (tensorSection.{u + 1, u, u + 1} (sysSite T) (sysRing l E T) (P.X p) (Q.X q) U x y)) key
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hk
  refine hk.trans ?_
  exact congrArg _ (SheafOfModules.CochainScalarConstruction.pure_map (sysRing l E T)
    (φ.f p) (ψ.f q) U x y)

/-- The system tensor pullback chain map sends the tensor generator of unit sections to the
unit section of the tensor generator. -/
theorem SystemTensorPull.chain_unit_coefficientTensorGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    {SX : Calculus l E X} {SY : Calculus l E Y} (s : SystemTensorPull l E f SX SY)
    (P Q : CochainComplex (VaryingRing.Modules (rings l E) (transitions l E) Y) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : ℕ × Y.ProEt)
    (x : (P.X p).val.obj (op U)) (y : (Q.X q).val.obj (op U)) :
    ((s.model.chain P Q).f k).val.app (op ((VaryingRing.baseChange f).obj U))
        (coefficientTensorGenerator.{u + 1, u + 1, u} (sysSite X) (sysRing l E X)
          (((VaryingRing.pull (rings l E) (transitions l E) f).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((VaryingRing.pull (rings l E) (transitions l E) f).mapHomologicalComplex
            (.up ℤ)).obj Q) p q k h (op ((VaryingRing.baseChange f).obj U))
          (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (P.X p)).val.app
            (op U) x)
          (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (Q.X q)).val.app
            (op U) y)) =
      ((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app
          (((SemilinearSections.totalTensor.{u + 1, u, u + 1} (sysSite Y)
            (sysRing l E Y)).obj (P, Q)).X k)).val.app (op U)
        (coefficientTensorGenerator.{u + 1, u + 1, u} (sysSite Y) (sysRing l E Y)
          P Q p q k h (op U) x y) := by
  have hgenY : coefficientTensorGenerator.{u + 1, u + 1, u} (sysSite Y) (sysRing l E Y)
      P Q p q k h (op U) x y =
      (tensorSummand.{u + 1, u, u + 1} (sysSite Y) (sysRing l E Y) P Q p q k h).val.app (op U)
        (tensorSection.{u + 1, u, u + 1} (sysSite Y) (sysRing l E Y) (P.X p) (Q.X q) (op U)
          x y) := rfl
  have hgenX : coefficientTensorGenerator.{u + 1, u + 1, u} (sysSite X) (sysRing l E X)
      (((VaryingRing.pull (rings l E) (transitions l E) f).mapHomologicalComplex
        (.up ℤ)).obj P)
      (((VaryingRing.pull (rings l E) (transitions l E) f).mapHomologicalComplex
        (.up ℤ)).obj Q) p q k h (op ((VaryingRing.baseChange f).obj U))
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (P.X p)).val.app
        (op U) x)
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (Q.X q)).val.app
        (op U) y) =
      (tensorSummand.{u + 1, u, u + 1} (sysSite X) (sysRing l E X)
        (((VaryingRing.pull (rings l E) (transitions l E) f).mapHomologicalComplex
          (.up ℤ)).obj P)
        (((VaryingRing.pull (rings l E) (transitions l E) f).mapHomologicalComplex
          (.up ℤ)).obj Q) p q k h).val.app (op ((VaryingRing.baseChange f).obj U))
        (tensorSection.{u + 1, u, u + 1} (sysSite X) (sysRing l E X) _ _
          (op ((VaryingRing.baseChange f).obj U))
          (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (P.X p)).val.app
            (op U) x)
          (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (Q.X q)).val.app
            (op U) y)) := rfl
  rw [hgenX, hgenY]
  have hs := congrArg (fun φ ↦ φ.val.app (op ((VaryingRing.baseChange f).obj U))
      (tensorSection.{u + 1, u, u + 1} (sysSite X) (sysRing l E X) _ _
          (op ((VaryingRing.baseChange f).obj U))
          (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (P.X p)).val.app
            (op U) x)
          (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app (Q.X q)).val.app
            (op U) y))) (s.model.summand P Q p q k h)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hs
  refine hs.trans ?_
  have hp := s.pure (P.X p) (Q.X q) U x y
  have hi := congrArg (fun φ ↦ φ.val.app (op ((VaryingRing.baseChange f).obj U))
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app
        (ordinaryTensor.{u + 1, u, u + 1} _ _ (P.X p) (Q.X q))).val.app (op U)
          (tensorSection.{u + 1, u, u + 1} _ _ (P.X p) (Q.X q) (op U) x y)))
      (s.model.ordinary (P.X p) (Q.X q)).hom_inv_id
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hi
  rw [hp] at hi
  refine (congrArg (fun z ↦ ((VaryingRing.pull (rings l E) (transitions l E) f).map
      (tensorSummand.{u + 1, u, u + 1} (sysSite Y) (sysRing l E Y) P Q p q k h)).val.app
        (op ((VaryingRing.baseChange f).obj U)) z) hi).trans ?_
  have hn := congrArg (fun φ ↦ φ.val.app (op U)
      (tensorSection.{u + 1, u, u + 1} _ _ (P.X p) (Q.X q) (op U) x y))
      ((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.naturality
        (tensorSummand.{u + 1, u, u + 1} (sysSite Y) (sysRing l E Y) P Q p q k h))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Functor.id_map, Functor.comp_map] at hn
  exact hn.symm

/-- The transpose along the system module adjunction evaluates through the unit. -/
theorem moduleAdj_homEquiv_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : VaryingRing.Modules (rings l E) (transitions l E) Y)
    (N : VaryingRing.Modules (rings l E) (transitions l E) X)
    (φ : (VaryingRing.pull (rings l E) (transitions l E) f).obj A ⟶ N) (U : ℕ × Y.ProEt)
    (s : A.val.obj (op U)) :
    (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).homEquiv A N) φ).val.app (op U) s =
      φ.val.app (op ((VaryingRing.baseChange f).obj U))
        (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app A).val.app
          (op U) s) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- Unit naturality of the system module adjunction, evaluated on a section. -/
theorem moduleAdj_unit_naturality_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : VaryingRing.Modules (rings l E) (transitions l E) Y} (φ : A ⟶ B) (U : ℕ × Y.ProEt)
    (s : A.val.obj (op U)) (t : B.val.obj (op U)) (h : φ.val.app (op U) s = t) :
    ((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app B).val.app (op U) t =
      ((VaryingRing.pull (rings l E) (transitions l E) f).map φ).val.app
        (op ((VaryingRing.baseChange f).obj U))
        (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app A).val.app (op U) s) :=
  h ▸ congrArg (fun ψ ↦ ψ.val.app (op U) s)
    ((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.naturality φ)

/-- An isomorphism of system-module valued functors inverts its values on sections. -/
theorem iso_inv_val_apply_of_hom {T : Scheme.{u}}
    {C : Type*} [Category C] {F G : C ⥤ VaryingRing.Modules (rings l E) (transitions l E) T}
    (e : F ≅ G) (M : C) (V : (ℕ × T.ProEt)ᵒᵖ) (a : (F.obj M).val.obj V) (b : (G.obj M).val.obj V)
    (h : (e.hom.app M).val.app V a = b) : (e.inv.app M).val.app V b = a := by
  rw [← h]
  exact congrArg (fun ψ ↦ ψ.val.app V a) (e.hom_inv_id_app M)

set_option maxHeartbeats 1000000 in
-- the composite chain maps on generators are compared by definitional unfolding
/-- The pullback tensor chain identity: on cochain representatives, the reduced pullback
tensorator followed by the tensor presentation, the ordinary pullback reduction comparison and
the system tensor pullback chain map is the pullback of the tensor presentation chain map.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1). -/
theorem pull_tensor_chain_identity (m : DescentModels l E) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (ordinary : ordinaryPull l E g ⋙ ordinaryReduction l E Z (m.abelian Z) (m.red Z) ≅
      ordinaryReduction l E Y (m.abelian Y) (m.red Y) ⋙
        VaryingRing.pull (rings l E) (transitions l E) g)
    (hgen : ∀ (M : Modules l E Y) (U : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op U)) (n : ℕ),
      ((ordinary.hom.app M).val.app (op (n, (Scheme.proEtaleBaseChange g).obj U)))
        (reductionGenerator l E Z (m.abelian Z) (m.red Z) ((ordinaryPull l E g).obj M) n
          (op ((Scheme.proEtaleBaseChange g).obj U))
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
            M).hom.hom.app (op U) x)) =
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) g).unit.app
        ((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).obj M)).val.app (op (n, U)))
        (reductionGenerator l E Y (m.abelian Y) (m.red Y) M n (op U) x))
    (P Q : CochainComplex (Modules l E Y) ℤ) :
    ((ordinaryReduction l E Z (m.abelian Z) (m.red Z)).mapHomologicalComplex (.up ℤ)).map
        (pullTensorChain l E g P Q) ≫
      (m.tensor Z).chain.hom.app
        (((ordinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj P,
          ((ordinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (SemilinearSections.totalTensor.{u + 1, u, u + 1} (sysSite Z) (sysRing l E Z)).map
        (Prod.mkHom ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app Q)) ≫
      (m.systemPull g).model.chain
        (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex (.up ℤ)).obj P)
        (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex (.up ℤ)).obj
          Q) =
    (NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app (P ⊗ Q) ≫
      ((VaryingRing.pull (rings l E) (transitions l E) g).mapHomologicalComplex (.up ℤ)).map
        ((m.tensor Y).chain.hom.app (P, Q)) := by
  apply HomologicalComplex.hom_ext
  intro k
  refine (cancel_epi (ordinary.inv.app ((P ⊗ Q).X k))).1 ?_
  apply ((VaryingRing.moduleAdj (rings l E) (transitions l E) g).homEquiv _ _).injective
  apply ordinaryReduction_tensor_hom_ext l E Y (m.abelian Y) (m.red Y) P Q k
  intro a b hab n U x y
  rw [moduleAdj_homEquiv_apply, moduleAdj_homEquiv_apply]
  -- the common value
  have hR : ordinary.inv.app ((P ⊗ Q).X k) ≫
      ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app (P ⊗ Q) ≫
        ((VaryingRing.pull (rings l E) (transitions l E) g).mapHomologicalComplex (.up ℤ)).map
          ((m.tensor Y).chain.hom.app (P, Q))).f k =
      (VaryingRing.pull (rings l E) (transitions l E) g).map
        (((m.tensor Y).chain.hom.app (P, Q)).f k) := by
    rw [HomologicalComplex.comp_f]
    exact Iso.inv_hom_id_app_assoc ordinary _ _
  rw [hR]
  have hn := moduleAdj_unit_naturality_apply l E g (((m.tensor Y).chain.hom.app (P, Q)).f k)
    (n, U.unop) (reductionGenerator l E Y (m.abelian Y) (m.red Y) _ n U
      (tensorGenerator l E Y P Q a b k hab U x y)) _ ((m.tensor Y).generators P Q a b k hab n U x y)
  refine Eq.trans ?_ hn
  -- the left hand side
  have h1 : (ordinary.inv.app ((P ⊗ Q).X k)).val.app
      (op ((VaryingRing.baseChange g).obj (n, U.unop)))
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) g).unit.app
        ((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).obj ((P ⊗ Q).X k))).val.app
          (op (n, U.unop))
        (reductionGenerator l E Y (m.abelian Y) (m.red Y) _ n U
          (tensorGenerator l E Y P Q a b k hab U x y))) =
      reductionGenerator l E Z (m.abelian Z) (m.red Z) ((ordinaryPull l E g).obj ((P ⊗ Q).X k)) n
        (op ((Scheme.proEtaleBaseChange g).obj U.unop))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
          ((P ⊗ Q).X k)).hom.hom.app U (tensorGenerator l E Y P Q a b k hab U x y)) :=
    iso_inv_val_apply_of_hom l E ordinary _ _ _ _
      (hgen ((P ⊗ Q).X k) U.unop (tensorGenerator l E Y P Q a b k hab U x y) n)
  have hA := (ordinaryReduction_map_apply_reductionGenerator l E Z (m.abelian Z) (m.red Z)
      ((pullTensorChain l E g P Q).f k) n (op ((Scheme.proEtaleBaseChange g).obj U.unop))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
          ((P ⊗ Q).X k)).hom.hom.app U (tensorGenerator l E Y P Q a b k hab U x y))).trans
    (congrArg (reductionGenerator l E Z (m.abelian Z) (m.red Z) _ n
      (op ((Scheme.proEtaleBaseChange g).obj U.unop)))
      (pullTensorChain_unit_tensorGenerator l E g P Q a b k hab U.unop x y))
  have hB := (m.tensor Z).generators (((ordinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj P)
    (((ordinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj Q) a b k hab n
    (op ((Scheme.proEtaleBaseChange g).obj U.unop))
    (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
      (P.X a)).hom.hom.app U x)
    (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
      (Q.X b)).hom.hom.app U y)
  have hC := (totalTensor_map_coefficientTensorGenerator l E Z
    ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
    ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app Q) a b k hab
    (op (n, (Scheme.proEtaleBaseChange g).obj U.unop))
    (reductionGenerator l E Z (m.abelian Z) (m.red Z) ((ordinaryPull l E g).obj (P.X a)) n
      (op ((Scheme.proEtaleBaseChange g).obj U.unop))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
        (P.X a)).hom.hom.app U x))
    (reductionGenerator l E Z (m.abelian Z) (m.red Z) ((ordinaryPull l E g).obj (Q.X b)) n
      (op ((Scheme.proEtaleBaseChange g).obj U.unop))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
        (Q.X b)).hom.hom.app U y))).trans
    (congrArg₂ _ (hgen (P.X a) U.unop x n) (hgen (Q.X b) U.unop y n))
  have hD := SystemTensorPull.chain_unit_coefficientTensorGenerator l E g (m.systemPull g)
    (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex (.up ℤ)).obj P)
    (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex (.up ℤ)).obj Q)
    a b k hab (n, U.unop)
    (reductionGenerator l E Y (m.abelian Y) (m.red Y) (P.X a) n U x)
    (reductionGenerator l E Y (m.abelian Y) (m.red Y) (Q.X b) n U y)
  have e1 := congrArg (fun z ↦ ((((ordinaryReduction l E Z (m.abelian Z)
    (m.red Z)).mapHomologicalComplex (.up ℤ)).map (pullTensorChain l E g P Q)).f k).val.app
      (op ((VaryingRing.baseChange g).obj (n, U.unop))) z) h1
  have e2 := congrArg (fun z ↦ (((m.tensor Z).chain.hom.app
    (((ordinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj P,
      ((ordinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj Q)).f k).val.app
        (op ((VaryingRing.baseChange g).obj (n, U.unop))) z) (e1.trans hA)
  have e3 := congrArg (fun z ↦ (((SemilinearSections.totalTensor.{u + 1, u, u + 1} (sysSite Z)
    (sysRing l E Z)).map
      (Prod.mkHom ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app Q))).f k).val.app
          (op ((VaryingRing.baseChange g).obj (n, U.unop))) z) (e2.trans hB)
  have e4 := congrArg (fun z ↦ (((m.systemPull g).model.chain
    (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex (.up ℤ)).obj P)
    (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex (.up ℤ)).obj
      Q)).f k).val.app (op ((VaryingRing.baseChange g).obj (n, U.unop))) z) (e3.trans hC)
  exact e4.trans hD

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
