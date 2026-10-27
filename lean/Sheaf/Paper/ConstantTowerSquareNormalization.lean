/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
import all Sheaf.Paper.StrictTowerRealizationComparisons

/-! # Constant-coefficient normalization of the ringed tower square

The section-normalized ringed compositor agrees with the fixed constant-coefficient
compositor. This exposes the existing proved normalization helper for further proofs.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.rightDerivedFunctor constantSheaf

private theorem inverseComparison {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (c : Z ≅ W) (h : X = Z) :
    (c.symm ≪≫ eqToIso h.symm ≪≫ a).inv = (a.symm ≪≫ eqToIso h ≪≫ c).hom := by
  subst h
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]

/-- The inverse constant ringed square is the specified constant compositor.
Source: Stacks 03D8 and 07A7, and the finite open-exchange factor of blueprint
sec-six-functors-basics/sk-prop-sf-cbc/sk-prop-sf-cbc.proof.md.
(blueprint: lem-cbc-constant-tower-square-normalization).

Proof: the two ordinary module compositors are inverse conjugates of the canonical
section-normalized direct-image compositors. Uniqueness identifies them with
exchangeModuleComposition, including the endpoint coefficient transports. This
identifies the module square with moduleSquareG. Whisker over the entire tower
index and apply exact localization; squareG_lift identifies the result with squareG.
The already proved cbcEvaluationConstantTowerSquare implements these steps. Take
inverses before projecting components; hκ identifies the chosen compositor. -/
theorem exchangeConstantTowerSquare_inv (A : Type (u + 1)) [CommRing A]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (sq : ChosenCartesianSquare k r p i)
    (κ : ProEtale.StrictTower.G A p ⋙ ProEtale.StrictTower.G A k ≅
      ProEtale.StrictTower.G A i ⋙ ProEtale.StrictTower.G A r)
    (hκ : κ = (ProEtale.StrictTower.gComp A k p).symm ≪≫
      eqToIso (congrArg (ProEtale.StrictTower.G A) sq.w) ≪≫
      ProEtale.StrictTower.gComp A r i) :
    (exchangeConstantSquare (A := A) sq).exchangeTowerSquare.inv = κ.hom := by
  have h := AlgebraicGeometry.Scheme.cbcEvaluationConstantTowerSquare A k r p i sq
  have hi := congrArg (fun e ↦ e.inv) h
  have hn : (ProEtale.StrictTower.squareG A k r p i sq.w).inv =
      ((ProEtale.StrictTower.gComp A k p).symm ≪≫
        eqToIso (congrArg (ProEtale.StrictTower.G A) sq.w) ≪≫
        ProEtale.StrictTower.gComp A r i).hom := by
    exact inverseComparison (ProEtale.StrictTower.gComp A k p)
      (ProEtale.StrictTower.gComp A r i) (congrArg (ProEtale.StrictTower.G A) sq.w)
  exact hi.trans (hn.trans (congrArg (fun e ↦ e.hom) hκ.symm))

end AlgebraicGeometry.Scheme
