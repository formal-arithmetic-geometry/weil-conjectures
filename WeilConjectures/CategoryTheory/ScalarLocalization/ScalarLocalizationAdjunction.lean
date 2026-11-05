/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Adjunctions after localizing the Hom modules

Source: blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md`, final sentence.
Tensoring the linear adjunction bijections gives the adjunction after inverting ell.
(blueprint: lem-sfb-scalar-localization-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe r u v u' v'

open TensorProduct

namespace CategoryTheory.ScalarLocalization

variable (R : Type r) [CommRing R] (p : R)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]

/-- Extend a linear functor by the identity on the localized scalar factor.
Source: blueprint, inversion of ell in the proper adjunction
(blueprint: lem-sfb-scalar-localization-adjunction). -/
def mapFunctor (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨F.obj X.obj⟩
  map {X Y} f := (F.mapLinearMap R).baseChange (Localization.Away p) f
  map_id X := by
    change (F.mapLinearMap R).baseChange (Localization.Away p)
      (1 ⊗ₜ[R] 𝟙 X.obj) = 1 ⊗ₜ[R] 𝟙 (F.obj X.obj)
    change 1 ⊗ₜ[R] F.map (𝟙 X.obj) = _
    rw [F.map_id]
  map_comp {X Y Z} f g := by
    change (F.mapLinearMap R).baseChange (Localization.Away p)
        (composition R C p X.obj Y.obj Z.obj g f) =
      composition R D p (F.obj X.obj) (F.obj Y.obj) (F.obj Z.obj)
        ((F.mapLinearMap R).baseChange (Localization.Away p) g)
        ((F.mapLinearMap R).baseChange (Localization.Away p) f)
    induction g using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul b g =>
      induction f using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a f =>
        simp only [composition_tmul, LinearMap.baseChange_tmul]
        change (b * a) ⊗ₜ[R] F.map (f ≫ g) =
          (b * a) ⊗ₜ[R] (F.map f ≫ F.map g)
        rw [F.map_comp]
      | add f h hf hh => simp only [map_add, hf, hh]
    | add g h hg hh => simp only [map_add, hg, hh, LinearMap.add_apply]

/-- The extended functor acts on pure tensors by its prescribed formula.
Source: the tensor-Hom definition (blueprint: lem-sfb-scalar-localization-adjunction).
Proof: this is the pure-tensor computation for base change of a linear map. -/
theorem mapFunctor_tmul (F : C ⥤ D) [F.Additive] [F.Linear R]
    (X Y : C) (a : Localization.Away p) (f : X ⟶ Y) :
    (mapFunctor R p F).map (X := ⟨X⟩) (Y := ⟨Y⟩) (a ⊗ₜ[R] f) =
      a ⊗ₜ[R] F.map f := LinearMap.baseChange_tmul _ _ _

instance mapFunctor_additive (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (mapFunctor R p F).Additive where
  map_add {_X _Y} f g := (F.mapLinearMap R).baseChange (Localization.Away p) |>.map_add f g

/-- The extended functor commutes with the tensor-with-one localization functors.
Source: inversion of ell in the blueprint proof
(blueprint: lem-sfb-scalar-localization-adjunction).
Proof: object maps agree, and both morphism maps send f to 1 tensor F(f). -/
theorem mapFunctor_localization (F : C ⥤ D) [F.Additive] [F.Linear R] :
    localization R C p ⋙ mapFunctor R p F = F ⋙ localization R D p := by
  exact Functor.ext (fun _ ↦ rfl)

private def homLinearEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.Additive] [F.Linear R] (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) := by
  let := adj.right_adjoint_linear (R := R)
  refine { adj.homAddEquiv X Y with map_smul' := ?_ }
  intro a f
  change adj.homEquiv X Y (a • f) = a • adj.homEquiv X Y f
  simp only [Adjunction.homEquiv_unit,
    Functor.map_smul, Linear.comp_smul]

/-- A linear left adjoint remains a left adjoint after scalar localization.
Source: blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md`, final sentence
(blueprint: lem-sfb-scalar-localization-adjunction).

Proof: the right adjoint is additive and linear. Tensor each linear adjunction bijection
with the localized coefficient ring. Naturality in both variables is checked on two pure
tensors, where it is the original adjunction naturality, and then on sums by bilinearity.
These natural bijections define the localized adjunction. This does not assert any
geometric comparison or existence of an integral adjoint. -/
theorem mapFunctor_isLeftAdjoint (F : C ⥤ D) [F.Additive] [F.Linear R]
    [F.IsLeftAdjoint] : (mapFunctor R p F).IsLeftAdjoint := by
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  let := adj.right_adjoint_additive
  let := adj.right_adjoint_linear (R := R)
  let e (X : ScalarLocalization R C p) (Y : ScalarLocalization R D p) :=
    (homLinearEquiv R adj X.obj Y.obj).baseChange R (Localization.Away p)
  refine (Adjunction.mkOfHomEquiv (F := mapFunctor R p F)
    (G := mapFunctor R p G)
    { homEquiv := fun X Y ↦ (e X Y).toEquiv
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }).isLeftAdjoint
  · intro X X' Y f g
    change (e X Y).symm (composition R C p _ _ _ g f) =
      composition R D p _ _ _ ((e X' Y).symm g)
        ((F.mapLinearMap R).baseChange (Localization.Away p) f)
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | tmul b g =>
        change (e X Y).symm (composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        simp only [composition_tmul, e, LinearEquiv.baseChange_symm_tmul]
        change (b * a) ⊗ₜ[R] (adj.homEquiv _ _).symm (f ≫ g) =
          composition R D p _ _ _ (b ⊗ₜ[R] (adj.homEquiv _ _).symm g)
            (a ⊗ₜ[R] F.map f)
        rw [composition_tmul, adj.homEquiv_naturality_left_symm]
      | add g h hg hh => simp only [map_add, LinearMap.add_apply, hg, hh]
    | add f h hf hh => simp only [map_add, hf, hh]
  · intro X Y Y' g h
    change e X Y' (composition R D p _ _ _ h g) =
      composition R C p _ _ _ ((G.mapLinearMap R).baseChange (Localization.Away p) h) (e X Y g)
    induction g using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a g =>
      induction h using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | tmul b h =>
        change e X Y' (composition R D p _ _ _ (b ⊗ₜ[R] h) (a ⊗ₜ[R] g)) = _
        simp only [composition_tmul, e, LinearEquiv.baseChange_tmul]
        change (b * a) ⊗ₜ[R] adj.homEquiv _ _ (g ≫ h) =
          composition R C p _ _ _ (b ⊗ₜ[R] G.map h)
            (a ⊗ₜ[R] adj.homEquiv _ _ g)
        rw [composition_tmul, adj.homEquiv_naturality_right]
      | add h i hh hi => simp only [map_add, LinearMap.add_apply, hh, hi]
    | add g i hg hi => simp only [map_add, hg, hi]

end CategoryTheory.ScalarLocalization
