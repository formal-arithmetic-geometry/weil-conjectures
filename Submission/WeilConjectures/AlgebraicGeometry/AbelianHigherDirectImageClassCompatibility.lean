/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Submission.WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp
import Submission.WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Pullback compatibility of the canonical derived-Hom class map

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-higher-direct-image-class-compatibility).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

private theorem adjunct_transition
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : D ⥤ E) (θ : L' ⟶ L ⋙ P)
    {X : C} {K : D} {K' : E} (z : L.obj X ⟶ K) (t : P.obj K ⟶ K') :
    adj.homEquiv X K z ≫ adj.transitionThrough adj' P θ K K' t =
      adj'.homEquiv X K' (θ.app X ≫ P.map z ≫ t) := by
  unfold Adjunction.transitionThrough
  rw [adj.homEquiv_unit, adj'.homEquiv_unit]
  rw [Category.assoc, ← adj'.unit_naturality_assoc,
    ← adj'.unit_naturality_assoc, ← R'.map_comp, ← R'.map_comp]
  apply congrArg (fun f ↦ adj'.unit.app X ≫ R'.map f)
  rw [θ.naturality_assoc, θ.naturality_assoc]
  simp only [Functor.comp_map]
  have hc : L.map (adj.unit.app X) ≫ L.map (R.map z) ≫ adj.counit.app K = z := by
    erw [adj.counit_naturality z, ← Category.assoc, adj.left_triangle_components,
      Category.id_comp]
  rw [← P.map_comp_assoc, ← P.map_comp_assoc, Category.assoc, hc]


namespace AlgebraicGeometry.Etale

/-- The free abelian sheaf on an etale representable, constructed by sheafification. -/
noncomputable abbrev abelianComparisonFree (S : Scheme.{v}) :=
  uliftYoneda.{v + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}


end AlgebraicGeometry.Etale
