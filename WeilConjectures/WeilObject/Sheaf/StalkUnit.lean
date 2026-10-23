/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# The identification `σ^* ≅ 𝟭` at the unit

Let `Ω` be a separably closed field and `σ` an endomorphism of `Spec Ω`. The isomorphism
`σ^* ≅ 𝟭` of `ProEtale.CondensedRing.upperStarIsoIdOfIsSepClosed` is, at the unit `Λ_{Spec Ω}`,
the inverse of the unit comparison `ε_σ : Λ_{Spec Ω} ≅ σ^* Λ_{Spec Ω}` of the strong monoidal
functor `σ^*`.

Writing `P = p^*` for the pullback from condensed `Λ`-modules, the isomorphism `σ^* ≅ 𝟭` is,
on objects of the form `P A`, the comparison `P ⋙ σ^* ≅ P`
(`Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj`), so its value at the unit reduces to
the unit coherence of `ProEtale.CondensedRing.upperStarFromPointModComp`.

## Main results

- `CategoryTheory.Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj`,
  `CategoryTheory.Iso.hom_app_eq_inv_of_hom_app_eq`: the abstract reduction.

## Sorried input

- `ProEtale.CondensedRing.upperStarFromPointModComp_hom_app_unit`: the comparison
  `P_Y ⋙ f^* ≅ P_X` is compatible with the unit comparisons.
- `ProEtale.CondensedRing.upperStarIsoIdOfIsSepClosed_hom_app_unit`: `σ^* Λ ≅ Λ` is `ε_σ⁻¹`
  (see its docstring for the kernel timeout of the reduction).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- Let `P : A ⥤ B` be an equivalence and `c : P ⋙ S ≅ P`. The induced isomorphism
`S ≅ P⁻¹ ⋙ P ⋙ S ≅ P⁻¹ ⋙ P ≅ 𝟭` is `c` on objects of the form `P a`. -/
lemma isoWhiskerLeft_counitIso_hom_app_functor_obj {A B : Type*} [Category A] [Category B]
    (P : A ⥤ B) [P.IsEquivalence] {S : B ⥤ B} (c : P ⋙ S ≅ P) (a : A) :
    ((Functor.leftUnitor S).symm ≪≫
      Functor.isoWhiskerRight P.asEquivalence.counitIso.symm S ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ c ≪≫ P.asEquivalence.counitIso).hom.app (P.obj a) =
      c.hom.app a := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp, Functor.comp_obj,
    Functor.id_obj]
  erw [P.asEquivalence.counitInv_app_functor a, P.asEquivalence.counit_app_functor a]
  have h := c.hom.naturality (P.asEquivalence.unit.app a)
  rw [Functor.comp_map] at h
  erw [reassoc_of% h, ← P.map_comp, P.asEquivalence.unitIso.hom_inv_id_app a, P.map_id,
    Category.comp_id]

/-- Let `τ : S ≅ 𝟭` and `e : b ≅ b'`. If `τ` at `b'` is `S e⁻¹ ≫ ε⁻¹ ≫ e` for an isomorphism
`ε : b ≅ S b`, then `τ` at `b` is `ε⁻¹`. -/
lemma _root_.CategoryTheory.Iso.hom_app_eq_inv_of_hom_app_eq {B : Type*} [Category B] {S : B ⥤ B} (τ : S ≅ 𝟭 B)
    {b b' : B} (e : b ≅ b') (ε : b ≅ S.obj b)
    (h : τ.hom.app b' = S.map e.inv ≫ ε.inv ≫ e.hom) : τ.hom.app b = ε.inv := by
  have hn := τ.hom.naturality e.hom
  rw [h, Iso.map_hom_inv_id_assoc, Functor.id_map] at hn
  exact ((cancel_mono e.hom).1 hn).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- The inverse image `p_X^*` preserves coequalizers, being a left adjoint. -/
noncomputable instance preservesColimitsOfShape_walkingParallelPair_upperStarFromPoint
    (X : Scheme.{u}) : PreservesColimitsOfShape WalkingParallelPair (upperStarFromPoint X) :=
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits
  inferInstance

/-- The inverse image `p_X^*` is braided strong monoidal. The low priority keeps instance search
for its lax monoidal structure on the existing instances. -/
noncomputable instance (priority := low) braided_upperStarFromPoint (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where

/-- The pullback `p_X^*` from condensed `Λ`-modules is strong monoidal, being the transport of
module objects along the braided functor `p_X^*` preserving coequalizers. -/
noncomputable instance monoidal_upperStarFromPointMod (X : Scheme.{u}) :
    (upperStarFromPointMod Λ X).Monoidal :=
  inferInstanceAs ((upperStarFromPoint X).mapMod Λ).Monoidal

/-- The comparison `p_Y^* ⋙ f^* ≅ p_X^*` on module objects is compatible with the unit
comparisons: at the unit it is `f^*(ε_{p_Y^*}⁻¹) ≫ ε_f⁻¹ ≫ ε_{p_X^*}`.

On underlying sheaves both sides are `α_f⁻¹ ≫ α_f = 𝟙`; a direct proof by unfolding hits
expensive definitional unfoldings of the sheaf pullbacks (see the report), so this is left
as sorried input. -/
lemma upperStarFromPointModComp_hom_app_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPointModComp Λ f).hom.app (𝟙_ _) =
      (f)^*⟦Λ⟧.map (Functor.Monoidal.εIso (upperStarFromPointMod Λ Y)).inv ≫
        (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv ≫
          (Functor.Monoidal.εIso (upperStarFromPointMod Λ X)).hom :=
  sorry

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The isomorphism `σ^* ≅ 𝟭` is, at the unit, the inverse of the unit comparison of `σ^*`.

Mathematically this follows from `Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj`,
`Iso.hom_app_eq_inv_of_hom_app_eq` and `upperStarFromPointModComp_hom_app_unit`, but
that term hits a kernel deterministic timeout: the strong monoidal structure
`monoidal_upperStarFromPointMod` lives over the coefficient ring with the algebra structure
transported along the `Braided` instance of `p_X^*`, while `upperStarFromPointMod` uses the
`LaxBraided` one, and unifying the two units unfolds the sheaf pullbacks. -/
lemma upperStarIsoIdOfIsSepClosed_hom_app_unit (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) :
    (upperStarIsoIdOfIsSepClosed Λ σ).hom.app (𝟙_ _) =
      (Functor.Monoidal.εIso (σ)^*⟦Λ⟧).inv :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
