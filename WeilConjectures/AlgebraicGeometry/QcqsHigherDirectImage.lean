/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Blueprint statements

lem-weil-pbc-qcqs-higher-direct-image.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Blueprint: lem-weil-pbc-qcqs-higher-direct-image. -/
theorem qcqs_higherDirectImage {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    (∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
      Nonempty
        ((presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
              { obj := fun Z ↦
                  ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
                    (evaluation U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj Z).rightDerived q).obj F
                map := fun g ↦
                  (NatTrans.rightDerived
                    (Functor.whiskerLeft
                      (sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
                      ((evaluation U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map g)) q).app F
                map_id := fun Z ↦ by
                  simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
                    NatTrans.rightDerived_id, NatTrans.id_app]
                map_comp := fun g h ↦ by
                  simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
                    NatTrans.rightDerived_comp, NatTrans.comp_app] }) ≅
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))) ∧
    ∀ (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (I : CochainComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      I.IsKInjective → Nonempty (DerivedCategory.Q.obj I ≅ K.obj) →
      ∀ q : ℤ, Nonempty
        ((presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
              (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I).homology q) ≅
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
