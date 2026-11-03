/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Invertibility of the specified locally closed internal adjunction

Source: blueprint thm-coef-finite-hom, paragraph 3, internal stratum adjunction
(blueprint: lem-coef-locally-closed-internal-adjunction-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange

attribute [local irreducible] derivedHom derivedTensor upperStar lowerStar

private theorem isIso_evaluationTranspose
    {C D : Type*} [Category C] [Category D]
    {P : C ⥤ D} {R : D ⥤ C} {F : D ⥤ C} {E : C ⥤ D}
    {T H : D ⥤ D} {U V : C ⥤ C}
    (a : P ⊣ R) (t : T ⊣ H) (c : F ⊣ E) (b : U ⊣ V)
    (α : U ⟶ P ⋙ (T ⋙ F)) [IsIso α] (M : C) :
    IsIso ((b.homEquiv _ _)
      (α.app (R.obj (H.obj (E.obj M))) ≫
        F.map (T.map (a.counit.app _) ≫ t.counit.app (E.obj M)) ≫
        c.counit.app M)) := by
  have h : (b.homEquiv _ _)
      (α.app (R.obj (H.obj (E.obj M))) ≫
        F.map (T.map (a.counit.app _) ≫ t.counit.app (E.obj M)) ≫
        c.counit.app M) = (conjugateEquiv (a.comp (t.comp c)) b α).app M := by
    apply (b.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply]
    simpa only [Adjunction.homEquiv_counit, Adjunction.comp_counit_app,
      Functor.comp_map, Functor.map_comp, Functor.comp_obj, Functor.id_obj,
      Category.assoc] using
      (conjugateEquiv_counit (a.comp (t.comp c)) b α M).symm
  rw [h]
  infer_instance

-- Keep the projection factors in their native functor presentations.
-- The reassociation and identity-functor conversions are checked with abstract functors.
private theorem isIso_factoredEvaluationTranspose
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ D} {Q : D ⥤ E} {K : E ⥤ D} {G : D ⥤ C}
    {R : E ⥤ C} {F : C ⥤ E} {T H : E ⥤ E} {U V : C ⥤ C} {W : D ⥤ D}
    (a : P ⋙ Q ⊣ R) (t : T ⊣ H) (c : K ⋙ G ⊣ F) (b : U ⊣ V)
    (β : U ⟶ (P ⋙ W) ⋙ G) (γ : (𝟭 D) ⋙ W ⟶ (Q ⋙ T) ⋙ K)
    [IsIso β] [IsIso γ] (M : C) :
    IsIso ((b.homEquiv _ _)
      ((β.app (R.obj (H.obj (F.obj M))) ≫
          G.map (γ.app (P.obj (R.obj (H.obj (F.obj M)))))) ≫
        (K ⋙ G).map (T.map (a.counit.app _) ≫ t.counit.app (F.obj M)) ≫
        c.counit.app M)) := by
  let α : U ⟶ (P ⋙ Q) ⋙ (T ⋙ (K ⋙ G)) :=
    β ≫ Functor.whiskerLeft P (Functor.whiskerRight γ G)
  have : IsIso α := by dsimp only [α]; infer_instance
  exact isIso_evaluationTranspose a t c b α M

/-- The evaluation-defined internal adjunction is invertible without a Tor bound.
Source: thm-coef-finite-hom, paragraph 3, internal stratum adjunction
(blueprint: lem-coef-locally-closed-internal-adjunction-iso).

Proof: For fixed L the closed proper projection map followed by the inverse open
projection is a natural isomorphism from tensoring with g_*j_!L to the composite
of g-star, j-star, tensoring with L and g_*j_!. The closed factor is invertible by
the finite-ring proper projection theorem; the open factor is the published open
projection isomorphism. Compose the two ordinary pullback/direct-image adjunctions,
the tensor-Hom adjunction and the compact-support exceptional adjunction. Conjugate
the projection isomorphism along this composite and the tensor-Hom adjunction on X.
Conjugation preserves isomorphisms. Its counit equation says that the component at
M is the transpose of projection followed by compact direct image of the ordinary
counit and evaluation, followed by the exceptional counit. Expanding the composite
counits gives precisely internalAdjunction as defined, so its component is an
isomorphism. No constructibility, nonemptiness or boundedness assumption occurs. -/
theorem locallyClosedInternalAdjunction_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    IsIso (internalAdjunction A g j L M) := by
  have : IsIso (rightDerivedLowerStarProjectionMap (ModuleCat A) g) :=
    isIso_rightDerivedLowerStarProjectionMap_of_finite A g
  unfold internalAdjunction
  rw [projection, ordinaryCounit, counit]
  -- Infer the adjunctions from the goal to retain the definition's instance arguments.
  apply isIso_factoredEvaluationTranspose

end AlgebraicGeometry.Etale
