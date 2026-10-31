/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Evaluation normalization of the inverse closed comparison

Source: `literature/stacks-project/sites-modules.tex`, Tag 03EO,
lemma-internal-hom-adjoint-tensor, for evaluation/currying; the inverse monoidal
structure is Mathlib `CategoryTheory.Equivalence.inverseMonoidal`
(blueprint: lem-sf-closed-equivalence-inverse-mate-normalization).

The internal-Hom adjunctions, their naturality in the contravariant variable and the
forward evaluation comparison are retained as explicit data.  The inverse comparison
is the specified unit/counit composite; the theorem below records its evaluation
normalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe uC vC uD vD

namespace CategoryTheory

/-- The inverse internal-Hom comparison `k_{U,V} : G H_D(U,V) ≅ H_C(GU,GV)` obtained
from the unit and counit of an adjoint equivalence: the composite
`η⁻¹ ∘ G(h_{GU,GV}⁻¹) ∘ G H_D(ε_U, ε_V⁻¹)` of the node statement.
Source: Tag 03EO (sites-modules.tex) for the internal Hom; composite specified by the
node (blueprint: lem-sf-closed-equivalence-inverse-mate-normalization). -/
noncomputable def closedEquivalenceInverseComparison
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (e : C ≌ D) [e.functor.Monoidal]
    (H_C : Cᵒᵖ ⥤ C ⥤ C) (H_D : Dᵒᵖ ⥤ D ⥤ D)
    (h : ∀ (X : C) (Y : C),
      e.functor.obj ((H_C.obj (Opposite.op X)).obj Y) ≅
        (H_D.obj (Opposite.op (e.functor.obj X))).obj (e.functor.obj Y))
    (U : D) (V : D) :
    e.inverse.obj ((H_D.obj (Opposite.op U)).obj V) ≅
      (H_C.obj (Opposite.op (e.inverse.obj U))).obj (e.inverse.obj V) := by
  exact
    (e.inverse.mapIso
      ((H_D.mapIso (e.counitIso.app U).op).app V ≪≫
        (H_D.obj (Opposite.op (e.functor.obj (e.inverse.obj U)))).mapIso
          (e.counitIso.app V).symm)).trans
      ((e.inverse.mapIso (h (e.inverse.obj U) (e.inverse.obj V)).symm).trans
        (e.unitIso.symm.app
          ((H_C.obj (Opposite.op (e.inverse.obj U))).obj (e.inverse.obj V))))

/-- The specified inverse closed comparison preserves evaluation:
`ev^C_{GU,GV} ∘ (k_{U,V} ⊗ 1) ∘ b_{H_D(U,V),U} = G(ev^D_{U,V})`.
The hypotheses `adj_C_natural`, `adj_D_natural` say that the adjunctions
`(-) ⊗ X ⊣ H(X,-)` are natural in `X` (extranaturality of evaluation).
Source: Tag 03EO (sites-modules.tex), evaluation/counit naturality; Mathlib
`Equivalence.inverseMonoidal` (blueprint:
lem-sf-closed-equivalence-inverse-mate-normalization).

Proof (node steps).
1. Put `t = H_D(ε_U, ε_V⁻¹)` and `M = H_D(U,V)`.  Evaluation is natural in the covariant
   variable and, by naturality of the adjunctions in `U`, extranatural in the
   contravariant one, so `ev_{FGU,FGV} ∘ (t ⊗ 1) = ε_V⁻¹ ∘ ev_{U,V} ∘ (1_M ⊗ ε_U)`.
2. With `b = (μ^G)⁻¹` the claim is `ev_{GU,GV} ∘ (k ⊗ 1) = G(ev_{U,V}) ∘ μ^G_{M,U}`.
   Transposition `f ↦ ε_V ∘ F f` across `F ⊣ G` is bijective, so compare transposes.
   The right side transposes, by naturality of `ε` and the compatibility
   `ε_{M⊗U} ∘ F(μ^G_{M,U}) = (ε_M ⊗ ε_U) ∘ c_{GM,GU}` of the inverse monoidal
   structure, to `ev_{U,V} ∘ (ε_M ⊗ ε_U) ∘ c_{GM,GU}`.
3. Put `A = H_C(GU,GV)`.  Then `h ∘ F k = t ∘ ε_M`, since `F(η_A⁻¹) = ε_{FA}` (triangle
   identity) and `ε` is natural.  The left side transposes, by `h_evaluation` at
   `(GU,GV)`, naturality of `c`, this identity and Step 1, to the same map
   `ev_{U,V} ∘ (ε_M ⊗ ε_U) ∘ c_{GM,GU}`.  Composing with `b_{M,U}` gives the claim. -/
theorem closedEquivalenceInverseMateNormalization
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (e : C ≌ D) [e.functor.Monoidal]
    (H_C : Cᵒᵖ ⥤ C ⥤ C) (H_D : Dᵒᵖ ⥤ D ⥤ D)
    (adj_C : ∀ (X : C),
      tensorRight X ⊣ H_C.obj (Opposite.op X))
    (adj_D : ∀ (U : D),
      tensorRight U ⊣ H_D.obj (Opposite.op U))
    (adj_C_natural : ∀ (X X' : C) (f : X' ⟶ X) (Y : C),
      ((H_C.map (Opposite.op f)).app Y ▷ X') ≫ (adj_C X').counit.app Y =
        ((H_C.obj (Opposite.op X)).obj Y ◁ f) ≫ (adj_C X).counit.app Y)
    (adj_D_natural : ∀ (U U' : D) (f : U' ⟶ U) (V : D),
      ((H_D.map (Opposite.op f)).app V ▷ U') ≫ (adj_D U').counit.app V =
        ((H_D.obj (Opposite.op U)).obj V ◁ f) ≫ (adj_D U).counit.app V)
    (h : ∀ (X : C) (Y : C),
      e.functor.obj ((H_C.obj (Opposite.op X)).obj Y) ≅
        (H_D.obj (Opposite.op (e.functor.obj X))).obj (e.functor.obj Y))
    (h_natural_left : ∀ (X X' : C) (f : X' ⟶ X) (Y : C),
      e.functor.map ((H_C.map (Opposite.op f)).app Y) ≫
          (h X' Y).hom =
        (h X Y).hom ≫
          (H_D.map (Opposite.op (e.functor.map f))).app (e.functor.obj Y))
    (h_natural_right : ∀ (X : C) (Y Y' : C) (g : Y ⟶ Y'),
      e.functor.map ((H_C.obj (Opposite.op X)).map g) ≫
          (h X Y').hom =
        (h X Y).hom ≫
          (H_D.obj (Opposite.op (e.functor.obj X))).map (e.functor.map g))
    (h_evaluation : ∀ (X : C) (Y : C),
      (Functor.Monoidal.μIso e.functor
          ((H_C.obj (Opposite.op X)).obj Y) X).inv ≫
          ((h X Y).hom ⊗ₘ 𝟙 (e.functor.obj X)) ≫
          (adj_D (e.functor.obj X)).counit.app (e.functor.obj Y) =
        e.functor.map ((adj_C X).counit.app Y))
    (U : D) (V : D) :
      (@Functor.Monoidal.μIso _ _ _ _ _ _ e.inverse e.inverseMonoidal
            ((H_D.obj (Opposite.op U)).obj V) U).inv ≫
          ((closedEquivalenceInverseComparison e H_C H_D h U V).hom ⊗ₘ
            𝟙 (e.inverse.obj U)) ≫
          (adj_C (e.inverse.obj U)).counit.app (e.inverse.obj V) =
        e.inverse.map ((adj_D U).counit.app V) := by
  -- Keep the original compatibility hypotheses in the fixed public signature.
  have _ := adj_C_natural
  have _ := h_natural_left
  have _ := h_natural_right
  let _ := e.inverseMonoidal
  let M := (H_D.obj (Opposite.op U)).obj V
  let A := (H_C.obj (Opposite.op (e.inverse.obj U))).obj (e.inverse.obj V)
  let t := (H_D.mapIso (e.counitIso.app U).op).app V ≪≫
    (H_D.obj (Opposite.op (e.functor.obj (e.inverse.obj U)))).mapIso
      (e.counitIso.app V).symm
  let k := closedEquivalenceInverseComparison e H_C H_D h U V
  have ht :
      t.hom ▷ e.functor.obj (e.inverse.obj U) ≫
          (adj_D (e.functor.obj (e.inverse.obj U))).counit.app
            (e.functor.obj (e.inverse.obj V)) ≫ e.counitIso.hom.app V =
        M ◁ e.counitIso.hom.app U ≫ (adj_D U).counit.app V := by
    dsimp [t]
    rw [comp_whiskerRight, Category.assoc]
    have hn := (adj_D (e.functor.obj (e.inverse.obj U))).counit.naturality
      (e.counitIso.inv.app V)
    change _ ▷ _ ≫ _ = _ at hn
    rw [reassoc_of% hn]
    simp only [Iso.inv_hom_id_app]
    simpa [M, Quiver.Hom.op] using adj_D_natural U (e.functor.obj (e.inverse.obj U))
      (e.counitIso.hom.app U) V
  have hk : e.functor.map k.hom ≫ (h (e.inverse.obj U) (e.inverse.obj V)).hom =
      e.counitIso.hom.app M ≫ t.hom := by
    change e.functor.map (e.inverse.map t.hom ≫
      e.inverse.map (h (e.inverse.obj U) (e.inverse.obj V)).inv ≫
        e.unitIso.inv.app A) ≫ _ = _
    rw [Functor.map_comp, Functor.map_comp, ← e.counit_app_functor]
    simp only [Category.assoc]
    rw [e.counit_naturality_assoc, e.counit_naturality_assoc]
    simp [M]
  simp only [tensorHom_id] at h_evaluation ⊢
  change Functor.OplaxMonoidal.δ e.inverse M U ≫
    k.hom ▷ e.inverse.obj U ≫ (adj_C (e.inverse.obj U)).counit.app (e.inverse.obj V) =
      e.inverse.map ((adj_D U).counit.app V)
  rw [← cancel_epi (Functor.LaxMonoidal.μ e.inverse M U)]
  simp only [Functor.Monoidal.μ_δ_assoc]
  apply e.functor.map_injective
  rw [← cancel_mono (e.counitIso.hom.app V)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← h_evaluation (e.inverse.obj U) (e.inverse.obj V)]
  simp only [Category.assoc]
  change e.functor.map (k.hom ▷ e.inverse.obj U) ≫
      Functor.OplaxMonoidal.δ e.functor A (e.inverse.obj U) ≫
        (h (e.inverse.obj U) (e.inverse.obj V)).hom ▷ _ ≫ _ ≫ _ = _
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [← comp_whiskerRight_assoc, hk, comp_whiskerRight_assoc, ht]
  have hn : e.functor.map (e.inverse.map ((adj_D U).counit.app V)) ≫
      e.counitIso.hom.app V =
        e.counitIso.hom.app (M ⊗ U) ≫ (adj_D U).counit.app V := by
    have he := e.counitIso.hom.naturality ((adj_D U).counit.app V)
    dsimp only [M, Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj,
      tensorRight, Functor.flip, curriedTensor] at he ⊢
    exact he
  rw [hn]
  rw [e.functor_map_μ_inverse_comp_counitIso_hom_app_tensor_assoc]
  simp only [tensorHom_def, Category.assoc]
  rfl

end CategoryTheory
