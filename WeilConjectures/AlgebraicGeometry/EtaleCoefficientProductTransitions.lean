/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveSystemData
import WeilConjectures.AlgebraicGeometry.EtaleCoefficientProductCompositionComponent
import WeilConjectures.AlgebraicGeometry.EtaleCoefficientProductIdentityComponent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Canonical transitions for outgoing-arrow products

Source: Stacks Project, Tag 0EXZ, the canonical maps between products of direct images.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The outgoing-arrow product transition, with components obtained by transposing
projections along the inverse-image/direct-image adjunction. No witnesses are chosen.
(Stacks, Tag 0EXZ) -/
noncomputable def etaleCoefficientProductTransition
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j : I} (f : i ⟶ j) :
    (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj
      (etaleCoefficientInjectiveTarget D F i) ⟶ etaleCoefficientInjectiveTarget D F j :=
  Pi.lift fun t : Σ k : I, j ⟶ k ↦
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op)).homEquiv _ _).symm
      (Pi.π _ ⟨t.1, f ≫ t.2⟩ ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (D.map t.2.op) (D.map f.op)
          (D.map (f ≫ t.2).op) (D.map_comp t.2.op f.op)).inv.app
            (Injective.under (F t.1)))

/-- The canonical outgoing-arrow product transitions satisfy the system laws.
(Stacks, Tag 0EXZ) -/
theorem etale_coefficient_product_transition_laws
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∀ i : I, etaleCoefficientProductTransition D F (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (etaleCoefficientInjectiveTarget D F i) ≫
      (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app
        (etaleCoefficientInjectiveTarget D F i)) ∧
    (∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      etaleCoefficientProductTransition D F (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app
            (etaleCoefficientInjectiveTarget D F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map
          (etaleCoefficientProductTransition D F f) ≫ etaleCoefficientProductTransition D F g)
    := by
  constructor
  · intro i
    apply Pi.hom_ext
    intro t
    dsimp only [etaleCoefficientProductTransition]
    refine (Pi.lift_comp_π _ t).trans ?_
    exact etale_coefficient_product_identity_component D F i t
  · intro i j k f g
    apply Pi.hom_ext
    intro t
    dsimp only [etaleCoefficientProductTransition]
    rw [Category.assoc, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]
    exact etale_coefficient_product_composition_component D F f g t

end AlgebraicGeometry.Etale
