/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData

/-! # strictCoefficientEquations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Restriction of the strict reduction comparison `rho` is compatible with pullback.
Source: Stacks 099M, 0D6D (blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
theorem rho_reductionTowerPullbackIso {U V : Scheme.{t}} (u : U ⟶ V) (M : d.derived V) :
    (exchangeTowerRes d U).map ((d.reductionTowerPullbackIso u).hom.app M) ≫
        (rho d U).hom.app ((d.pull u).obj M) ≫
        (reduction d U).map ((alpha d u).hom.app M) =
      (exchangeResPull d u).hom.app ((completedReductionTower V d).obj M) ≫
        (exchangeConstantPull (A := A) u).map ((rho d V).hom.app M) ≫
        (reductionPullIso d u).hom.app ((res d V).obj M) := by
  sorry

/-- Restriction of the strict reduction comparison `rho` is compatible with the strict
projection formula maps. Source: Stacks 099M, 0D6E
(blueprint: def-weil-pbc-ordered-coefficient-comparison-data). -/
theorem rho_towerProjection {U V : Scheme.{t}} (u : U ⟶ V) (K : d.derived U) :
    (exchangeTowerRes d V).map (d.towerProjection u K) ≫
        (exchangeResPush d u).hom.app ((completedReductionTower U d).obj K) ≫
        (exchangeConstantPush (A := A) u).map ((rho d U).hom.app K) =
      (rho d V).hom.app ((d.push u).obj K) ≫
        (reduction d V).map ((chi d u).hom.app K) ≫
        projection d u ((res d U).obj K) := by
  sorry

/-- The second strict coefficient equation: restriction of the strict realization `H`
followed by `beta` is `rhoM` followed by the constant `H`.
Source: Stacks 099M, 0D6D, 0D6E
(blueprint: lem-weil-pbc-ordered-strict-coefficient-equations). -/
theorem exchangeRealizationH_beta (K : d.derived X) :
    (exchangeTowerRes d Y').map (exchangeRealizationH (f := f) (g := g) d K).hom ≫
        (beta (f := f) (g := g) d K).hom =
      (rhoM (f := f) (g := g) d K).hom ≫ (H (f := f) (g := g) d ((res d X).obj K)).hom := by
  let M := (d.push f).obj K
  have hP := rho_reductionTowerPullbackIso d g M
  have hQ := rho_towerProjection d f K
  have hP' : (exchangeResPull d g).hom.app ((completedReductionTower Y d).obj M) ≫
      (exchangeConstantPull (A := A) g).map ((rho d Y).hom.app M) =
    (exchangeTowerRes d Y').map ((d.reductionTowerPullbackIso g).hom.app M) ≫
      (rho d Y').hom.app ((d.pull g).obj M) ≫
      (reduction d Y').map ((alpha d g).hom.app M) ≫
      (reductionPullIso d g).inv.app ((res d Y).obj M) := by
    rw [reassoc_of% hP, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hN := (exchangeResPull d g).hom.naturality (d.towerProjection f K)
  have hR := (reductionPullIso d g).inv.naturality ((chi d f).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hN hR
  simp only [exchangeRealizationH, beta, rhoM, H, exchangeCornerB, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, asIso_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  rw [reassoc_of% hN]
  rw [← Functor.map_comp, ← Functor.map_comp, hQ]
  simp only [Functor.map_comp]
  rw [reassoc_of% hP', ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hR]

/-- The third strict coefficient equation: restriction of the strict exchange `towerV'`
is the constant strict tower mate, conjugated by `beta` and `delta`.
Source: Stacks 099M, 0E48 (blueprint: lem-weil-pbc-ordered-strict-coefficient-equations). -/
theorem towerV'_delta (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (exchangeTowerRes d Y').map (d.towerV' sq K) ≫ (delta (f' := f') (g' := g') d K).hom =
      (beta (f := f) (g := g) d K).hom ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
          ((reduction d X).obj ((res d X).obj K)) := by
  sorry

/-- strictCoefficientEquations: the indicated part of the ordered comparison argument.
Source: blueprint completed-exchange-coherence, second proof paragraph;
Stacks Tags 099M, 099N, 0A07 and 0E48.
(blueprint: lem-weil-pbc-ordered-strict-coefficient-equations).
Proof: the diagonal exact-adjunction comparison identifies the completed strict
exchange with the reduction of the ambient mate. The perfect quotient projection
maps are invertible, so conjugating gives the first formula. For the second,
transpose the projection formula map under the ordinary ringed adjunction.
Restriction identifies its counit with the constant counit, and quotient balancing
sends each pure tensor to the same tensor. Apply the derived pullback and tensor
comparison to this equation on the single strict quotient diagram. Tensor descent
makes it an equality of derived tower morphisms. For the third, transpose the
restricted strict exchange under the constant tower adjunction. Scalar restriction
identifies both units and counits, and coefficient inverse image respects
composition. The transpose is therefore the transpose defining the constant mate.
Bijectivity of the adjunction correspondence gives the equation. Naturality for
rho then gives exactly beta and delta at the reduced complete input. No claim of
faithfulness of derived evaluation functors is used. -/
theorem strictCoefficientEquations (sq : ChosenCartesianSquare g' f' f g) :
    ∀ (K : d.derived X) (hK : d.TowerComplete X K),
      (d.towerV' sq K =
        (exchangeRealizationH (f := f) (g := g) d K).inv ≫
          (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
      ((exchangeTowerRes d Y').map
          (exchangeRealizationH (f := f) (g := g) d K).hom ≫
            (beta (f := f) (g := g) d K).hom =
        (rhoM (f := f) (g := g) d K).hom ≫
          (H (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((exchangeTowerRes d Y').map (d.towerV' sq K) ≫
          (delta (f' := f') (g' := g') d K).hom =
        (beta (f := f) (g := g) d K).hom ≫
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
            ((reduction d X).obj ((res d X).obj K))) := by
  intro K _
  refine ⟨?_, exchangeRealizationH_beta d K, towerV'_delta d sq K⟩
  simp only [AdicCoefficientDatum.towerV', AdicCoefficientDatum.towerV,
    exchangeRealizationH, exchangeRealizationHPrime, AdicCoefficientDatum.towerH,
    AdicCoefficientDatum.towerH', Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.app_hom,
    Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.OrderedExchange
