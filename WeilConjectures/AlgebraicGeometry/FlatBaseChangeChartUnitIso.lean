/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeRestrictionUnitNormalization

/-! # Unit-compatible coefficient isomorphism on a fixed base-change chart

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] pushforward pushforwardComp pushforwardCongr pushforwardId

-- Keep the existing unused let A in the statement without changing its signature.
set_option linter.unusedVariables false in
-- The statement elaborates several successive module pushforwards and pullbacks.
/-- The adjoint of the restricted tensor unit is invertible on a fixed chart.
(Stacks, Tags 0096, 0097 and 02KH.) -/
theorem isIso_flatBaseChange_chart_unit_adjoint
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (V : S.Opens) (W : S'.Opens)
    (eVW : W ≤ g ⁻¹ᵁ V) (D : FlatBaseChangeOpenChoices f g F I J V)
    [Algebra Γ(S, V) Γ(S', W)] :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (pullback (f ⁻¹ᵁ V).ι).obj F
    let T := baseChangedScheme (S := Γ(S', W)) h
    let A := baseChangedModule (S := Γ(S', W)) h N
    let G := (tensorPullback (pullback.snd g f)).obj F
    let U := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
    let L := (pullback.fst g f) ⁻¹ᵁ W
    let e : L ≤ U := by
      change (pullback.fst g f) ⁻¹ᵁ W ≤ (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
      rw [flatBaseChangeOpenEquality f g V]
      exact (pullback.fst g f).preimage_mono eVW
    let M := (restrictFunctor L.ι).obj G
    let j := (Limits.pullback g f).homOfLE e
    let c := (restrictFunctorComp j U.ι).symm.app G ≪≫
      (restrictFunctorCongr ((Limits.pullback g f).homOfLE_ι e)).app G
    let r := (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj G) ≫
      (pushforward j).map c.hom
    let q := (pullback.snd g f).resLE (f ⁻¹ᵁ V) U le_rfl
    ∀ (σ : L.toScheme ≅ T)
      (ef : σ.hom ≫ baseChangeFst (S := Γ(S', W)) h = j ≫ q),
      let b := ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).inv ≫
        D.psi ≫ (pushforward q).map r ≫
        (pushforwardComp j q).hom.app M ≫ (pushforwardCongr ef).inv.app M ≫
        (pushforwardComp σ.hom (baseChangeFst (S := Γ(S', W)) h)).inv.app M
      IsIso ((pullbackPushforwardAdjunction
        (baseChangeFst (S := Γ(S', W)) h)).homEquiv _ _ |>.symm b) := by
  intro h N T A G U L e M j c r q σ ef
  let p := pullback.snd g f
  let a := (f ⁻¹ᵁ V).ι
  let t := baseChangeFst (S := Γ(S', W)) h
  let l := L.ι
  have E : (σ.hom ≫ t) ≫ a = l ≫ p := by
    rw [ef, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc]
    rw [Scheme.homOfLE_ι]
  let rightIso : pushforward σ.hom ⋙ pushforward t ⋙ pushforward a ≅
      pushforward l ⋙ pushforward p :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComp σ.hom t) (pushforward a) ≪≫
      pushforwardComp (σ.hom ≫ t) a ≪≫ pushforwardCongr E ≪≫
      (pushforwardComp l p).symm
  let adj₁ := (restrictAdjunction a).comp
    ((pullbackPushforwardAdjunction t).comp (pullbackPushforwardAdjunction σ.hom))
  let adj₂ := (Classical.choose (exists_tensorPullbackAdjunction p)).comp
    (restrictAdjunction l)
  let k : (pullback σ.hom).obj A ≅ M :=
    (pullback σ.hom).mapIso ((pullback t).mapIso
      ((restrictFunctorIsoPullback a).symm.app F)) ≪≫
      (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)).app F
  have hp : (pushforward σ.hom).IsEquivalence :=
    Functor.IsEquivalence.mk' (pushforward σ.inv)
      ((pushforwardComp σ.hom σ.inv) ≪≫ pushforwardCongr σ.hom_inv_id ≪≫
        pushforwardId _).symm
      ((pushforwardComp σ.inv σ.hom) ≪≫ pushforwardCongr σ.inv_hom_id ≪≫
        pushforwardId _)
  have hb : IsIso ((pullbackPushforwardAdjunction σ.hom).homEquiv A M k.hom) := by
    rw [Adjunction.homEquiv_unit]
    infer_instance
  have hn := restriction_chart_unit_normalization p a U.ι l j q t σ
    (Scheme.homOfLE_ι (Limits.pullback g f) e) (Scheme.Hom.resLE_comp_ι p le_rfl)
    ef F D.psi D.unit_square
  dsimp only at hn ⊢
  exact hn ▸ hb

end AlgebraicGeometry.Scheme.Modules
