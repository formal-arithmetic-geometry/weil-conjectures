/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.Adjunction.LiftedCommRingBranch

/-!
# Lifting a product preserving adjunction to group and ring objects

Source: Stacks Project, Sites and Sheaves, Proposition 00YV, proof of (2) and the
paragraph on rings as sextuples (blueprint: lem-weil-pbc-adjunction-lifts-group-ring-objects).
-/

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

/-- Source: Stacks Project, Proposition 00YV, proof of (2) and rings as sextuples
(blueprint: lem-weil-pbc-adjunction-lifts-group-ring-objects).

The Cartesian monoidal structures specify the chosen finite products. `CommGrp` is
written multiplicatively, with its multiplication, unit and inverse representing
addition, zero and negation. The equalities of forgetful functors specify strict
underlying functors; the associated `eqToIso`s only express these equalities in
well-typed equations of structure maps.

Proof: (1) The right adjoint preserves limits. Apply `Adjunction.mapCommGrp` for the
group clauses, using the canonical braided structures on product preserving functors
(lem-weil-pbc-right-adjoint-preserves-limits,
lem-weil-pbc-adjunction-lifts-abelian-group-objects).
(2) The product comparisons commute with projections, pairings and product maps;
the terminal comparison commutes with the unique maps to the terminal object
(def-weil-category-product). These identities also hold for the right adjoint.
(3) Transport the ring operations by the inverse comparisons. Induction on terms
built from coordinates, operations and constants shows that transported terms,
precomposed with the comparison for their product of variables, equal the image
of the original terms. Cancel that isomorphism to obtain every ring axiom.
(4) Naturality of the product comparisons and functoriality imply that images of
ring morphisms preserve every operation, giving functors commuting with forgetting.
(5) Naturality of the unit and counit, checked on the product projections, shows
that they preserve multiplication and one; their additive compatibility is (1).
(6) A morphism and its adjunct preserve the operations simultaneously: one direction
composes its right image with the unit; the other composes its left image with the
counit (lem-weil-pbc-adjunct-counit-identity). Restrict the natural adjunction
bijection to obtain the lifted adjunction (lem-weil-pbc-adjunction-of-natural-bijection).
Its unit and counit are the original components. -/
theorem liftsGroupRingObjects
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [PreservesFiniteProducts L] :
    letI : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
    letI : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
    ∃ (_ : PreservesFiniteProducts R),
      (∃ (LF : CommGrp A ⥤ CommGrp B) (RF : CommGrp B ⥤ CommGrp A)
          (hL : LF ⋙ CommGrp.forget B = CommGrp.forget A ⋙ L)
          (hR : RF ⋙ CommGrp.forget A = CommGrp.forget B ⋙ R),
        let eL := eqToIso hL
        let eR := eqToIso hR
        ∃ (a : LF ⊣ RF),
          (∀ X : CommGrp A,
            MonObj.mul (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X)) ∧
            GrpObj.inv (X := (LF.obj X).X) ≫ eL.hom.app X =
              eL.hom.app X ≫ L.map (GrpObj.inv (X := X.X))) ∧
          (∀ X : CommGrp B,
            MonObj.mul (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X)) ∧
            GrpObj.inv (X := (RF.obj X).X) ≫ eR.hom.app X =
              eR.hom.app X ≫ R.map (GrpObj.inv (X := X.X))) ∧
          (∀ (X : CommGrp A) (Y : CommGrp B) (f : LF.obj X ⟶ Y),
            (CommGrp.forget A).map (a.homEquiv X Y f) ≫ eR.hom.app Y =
              adj.homEquiv X.X Y.X (eL.inv.app X ≫ (CommGrp.forget B).map f)) ∧
          (∀ X : CommGrp A,
            (CommGrp.forget A).map (a.unit.app X) ≫ eR.hom.app (LF.obj X) ≫
                R.map (eL.hom.app X) = adj.unit.app X.X) ∧
          (∀ Y : CommGrp B,
            L.map (eR.inv.app Y) ≫ eL.inv.app (RF.obj Y) ≫
                (CommGrp.forget B).map (a.counit.app Y) = adj.counit.app Y.X) ∧
          (∀ (X : CommGrp A) (Y : CommGrp B) (α : L.obj X.X ⟶ Y.X),
            (∃ f : LF.obj X ⟶ Y, eL.inv.app X ≫ (CommGrp.forget B).map f = α) ↔
              ∃ g : X ⟶ RF.obj Y,
                (CommGrp.forget A).map g ≫ eR.hom.app Y = adj.homEquiv X.X Y.X α)) ∧
      (∃ (LF : CommRingObjCat A ⥤ CommRingObjCat B) (RF : CommRingObjCat B ⥤ CommRingObjCat A)
          (hL : LF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ L)
          (hR : RF ⋙ CommRingObjCat.forget A = CommRingObjCat.forget B ⋙ R),
        let eL := eqToIso hL
        let eR := eqToIso hR
        ∃ (a : LF ⊣ RF),
          (∀ X : CommRingObjCat A,
            AddMonObj.add (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (LF.obj X).X) ≫ eL.hom.app X =
              eL.hom.app X ≫ L.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X))) ∧
          (∀ X : CommRingObjCat B,
            AddMonObj.add (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ eR.hom.app X =
              eR.hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X))) ∧
          (∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (f : LF.obj X ⟶ Y),
            (CommRingObjCat.forget A).map (a.homEquiv X Y f) ≫ eR.hom.app Y =
              adj.homEquiv X.X Y.X (eL.inv.app X ≫ (CommRingObjCat.forget B).map f)) ∧
          (∀ X : CommRingObjCat A,
            (CommRingObjCat.forget A).map (a.unit.app X) ≫ eR.hom.app (LF.obj X) ≫
                R.map (eL.hom.app X) = adj.unit.app X.X) ∧
          (∀ Y : CommRingObjCat B,
            L.map (eR.inv.app Y) ≫ eL.inv.app (RF.obj Y) ≫
                (CommRingObjCat.forget B).map (a.counit.app Y) = adj.counit.app Y.X) ∧
          (∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (α : L.obj X.X ⟶ Y.X),
            (∃ f : LF.obj X ⟶ Y, eL.inv.app X ≫ (CommRingObjCat.forget B).map f = α) ↔
              ∃ g : X ⟶ RF.obj Y,
                (CommRingObjCat.forget A).map g ≫ eR.hom.app Y = adj.homEquiv X.X Y.X α)) := by
  let : PreservesLimitsOfSize.{0, 0} R := adj.rightAdjoint_preservesLimits
  let : PreservesFiniteProducts R := ⟨fun n => inferInstance⟩
  refine ⟨inferInstance, ?_, liftedCommRingBranch adj⟩
  let : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
  let : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let : R.Braided := Functor.Braided.ofChosenFiniteProducts R
  have hforward (X : CommGrp A) (Y : CommGrp B) (f : L.mapCommGrp.obj X ⟶ Y) :
      (adj.mapCommGrp.homEquiv X Y f).hom.hom.hom =
        adj.homEquiv X.X Y.X f.hom.hom.hom := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change (𝟙 _ ≫ adj.unit.app X.X ≫ 𝟙 _) ≫ R.map f.hom.hom.hom = _
    simp only [Category.id_comp, Category.comp_id]
  refine ⟨L.mapCommGrp, R.mapCommGrp, rfl, rfl, adj.mapCommGrp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    change
      ((Functor.LaxMonoidal.μ L X.X X.X ≫ L.map MonObj.mul) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (prodComparisonIso L X.X X.X).inv ≫ L.map MonObj.mul) ∧
      ((Functor.LaxMonoidal.ε L ≫ L.map MonObj.one) ≫ 𝟙 _ =
        (preservesTerminalIso L).inv ≫ L.map MonObj.one) ∧
      (L.map GrpObj.inv ≫ 𝟙 _ = 𝟙 _ ≫ L.map GrpObj.inv)
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp,
      Functor.Monoidal.μ_of_cartesianMonoidalCategory,
      Functor.Monoidal.ε_of_cartesianMonoidalCategory, and_self]
  · intro X
    change
      ((Functor.LaxMonoidal.μ R X.X X.X ≫ R.map MonObj.mul) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (prodComparisonIso R X.X X.X).inv ≫ R.map MonObj.mul) ∧
      ((Functor.LaxMonoidal.ε R ≫ R.map MonObj.one) ≫ 𝟙 _ =
        (preservesTerminalIso R).inv ≫ R.map MonObj.one) ∧
      (R.map GrpObj.inv ≫ 𝟙 _ = 𝟙 _ ≫ R.map GrpObj.inv)
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp,
      Functor.Monoidal.μ_of_cartesianMonoidalCategory,
      Functor.Monoidal.ε_of_cartesianMonoidalCategory, and_self]
  · intro X Y f
    change (adj.mapCommGrp.homEquiv X Y f).hom.hom.hom ≫ 𝟙 _ =
      adj.homEquiv X.X Y.X (𝟙 _ ≫ f.hom.hom.hom)
    simp only [Category.comp_id, Category.id_comp]
    exact hforward X Y f
  · intro X
    change (𝟙 _ ≫ adj.unit.app X.X ≫ 𝟙 _) ≫ 𝟙 _ ≫ R.map (𝟙 _) = _
    simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    exact Category.comp_id _
  · intro Y
    change L.map (𝟙 _) ≫ 𝟙 _ ≫ (𝟙 _ ≫ adj.counit.app Y.X ≫ 𝟙 _) = _
    simp only [Category.comp_id, Category.id_comp, Functor.map_id]
  · intro X Y α
    change (∃ f : L.mapCommGrp.obj X ⟶ Y, 𝟙 _ ≫ f.hom.hom.hom = α) ↔
      ∃ g : X ⟶ R.mapCommGrp.obj Y,
        g.hom.hom.hom ≫ 𝟙 _ = adj.homEquiv X.X Y.X α
    simp only [Category.id_comp, Category.comp_id]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨adj.mapCommGrp.homEquiv X Y f, (hforward X Y f).trans (congrArg _ hf)⟩
    · rintro ⟨g, hg⟩
      refine ⟨(adj.mapCommGrp.homEquiv X Y).symm g, ?_⟩
      apply (adj.homEquiv X.X Y.X).injective
      rw [← hforward X Y, Equiv.apply_symm_apply, hg]

end CategoryTheory.Adjunction
