/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMate
public import WeilConjectures.TraceFormula.SupportedRestriction

/-!

# The supported restriction under a change of coefficients

The supported restriction `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` of a fixed square
(`ProEtale.CondensedRing.Correspondence.FixedLocus.supportedRestriction`, blueprint
`det-tf-supported-restriction`) is a formal consequence of the adjunctions `c_! ⊣ c^!`,
`d_! ⊣ d^!` and of compact-support base change `σ : c_! ⋙ Δ^* ≅ ι^* ⋙ d_!`: it is the mate
`c^! ⋙ ι^* ⟶ Δ^* ⋙ d^!` of `σ⁻¹` (`FixedLocus.supportedRestriction_eq_mateEquiv`). This file
proves that such a mate commutes with any change of coefficients `T` which commutes with `c_!`,
`d_!`, `ι^*` and `Δ^*` compatibly with base change
(`CategoryTheory.Adjunction.map_mateEquiv_app_comp`): the image under `T` of the supported
restriction, followed by the exchange `T ⋙ Rd^! ⟶ Rd'^! ⋙ T` (the mate of the lower-shriek
comparison), is the exchange for `c^!` followed by the supported restriction for the new
coefficients. This is the coefficient compatibility of `ρ` used to transport the vanishing of the
supported restriction between coefficient rings (blueprint `sk-lem-tf-curve-restriction-zero`,
last step); the inputs are the coefficient comparisons of blueprint `sk-prop-scalar-six` and the
compatibility of base change with them (blueprint `sk-thm-sf-package`, (2)).

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory

variable {C₂ : Type u₁} {CC : Type u₂} {CF : Type u₃} {CX : Type u₄}
  [Category.{v₁} C₂] [Category.{v₂} CC] [Category.{v₃} CF] [Category.{v₄} CX]
  {C₂' : Type u₅} {CC' : Type u₆} {CF' : Type u₇} {CX' : Type u₈}
  [Category.{v₅} C₂'] [Category.{v₆} CC'] [Category.{v₇} CF'] [Category.{v₈} CX']

/-- The component at `P` of the mate `c^! ⋙ ι^* ⟶ Δ^* ⋙ d^!` of `σ⁻¹ : ι^* ⋙ d_! ⟶ c_! ⋙ Δ^*`
is the `d_! ⊣ d^!` adjoint of `σ⁻¹` followed by `Δ^*` of the counit of `c_! ⊣ c^!`. -/
lemma Adjunction.mateEquiv_app_eq_homEquiv {cL : CC ⥤ C₂} {cR : C₂ ⥤ CC} (a : cL ⊣ cR)
    {dL : CF ⥤ CX} {dR : CX ⥤ CF} (g : dL ⊣ dR) (ι : CC ⥤ CF) (Δ : C₂ ⥤ CX)
    (σ : cL ⋙ Δ ≅ ι ⋙ dL) (P : C₂) :
    (mateEquiv a g (TwoSquare.mk _ _ _ _ σ.inv)).natTrans.app P =
      g.homEquiv (ι.obj (cR.obj P)) (Δ.obj P) (σ.inv.app (cR.obj P) ≫ Δ.map (a.counit.app P)) := by
  rw [Adjunction.homEquiv_unit]
  simp [mateEquiv_apply]

variable {cL : CC ⥤ C₂} {cR : C₂ ⥤ CC} (a : cL ⊣ cR) {dL : CF ⥤ CX} {dR : CX ⥤ CF}
    (g : dL ⊣ dR) (ι : CC ⥤ CF) (Δ : C₂ ⥤ CX) (σ : cL ⋙ Δ ≅ ι ⋙ dL)
  {cL' : CC' ⥤ C₂'} {cR' : C₂' ⥤ CC'} (a' : cL' ⊣ cR') {dL' : CF' ⥤ CX'} {dR' : CX' ⥤ CF'}
    (g' : dL' ⊣ dR') (ι' : CC' ⥤ CF') (Δ' : C₂' ⥤ CX') (σ' : cL' ⋙ Δ' ≅ ι' ⋙ dL')
  (T₂ : C₂ ⥤ C₂') (TC : CC ⥤ CC') (TF : CF ⥤ CF') (TX : CX ⥤ CX')
  (τc : cL ⋙ T₂ ≅ TC ⋙ cL') (τd : dL ⋙ TX ≅ TF ⋙ dL')
  (τι : ι ⋙ TF ≅ TC ⋙ ι') (τΔ : Δ ⋙ TX ≅ T₂ ⋙ Δ')

/-- **The mate of a base-change isomorphism commutes with a change of coefficients**: let `T` be a
change of coefficients commuting with `c_!`, `d_!`, `ι^*` and `Δ^*` (isomorphisms `τ`), compatibly
with base change `σ`, `σ'` (`hσ`), and write `ρ` and `ρ'` for the mates of `σ⁻¹` and `σ'⁻¹`
(for a fixed square, the supported restrictions). Then the square
```
T ι^* c^! P ---T ρ_P---> T d^! Δ^* P --ex_d--> d'^! T Δ^* P --d'^! τ_Δ--> d'^! Δ'^* T P
    |                                                                         ‖
   τ_ι                                                                        ‖
    v                                                                         ‖
ι'^* T c^! P --ι'^* ex_c--> ι'^* c'^! T P ---------------ρ'_{T P}-----------> d'^! Δ'^* T P
```
commutes, where `ex_c` and `ex_d` are the exchanges `T ⋙ c'^! ⟵ c^! ⋙ T` (the mates of `τ_c⁻¹`
and `τ_d⁻¹`). -/
theorem Adjunction.map_mateEquiv_app_comp
    (hσ : ∀ M : CC, TX.map (σ.hom.app M) ≫ τd.hom.app (ι.obj M) ≫ dL'.map (τι.hom.app M) =
      τΔ.hom.app (cL.obj M) ≫ Δ'.map (τc.hom.app M) ≫ σ'.hom.app (TC.obj M)) (P : C₂) :
    TF.map ((mateEquiv a g (TwoSquare.mk _ _ _ _ σ.inv)).natTrans.app P) ≫
        (mateEquiv g g' (TwoSquare.mk _ _ _ _ τd.inv)).natTrans.app (Δ.obj P) ≫
          dR'.map (τΔ.hom.app P) =
      τι.hom.app (cR.obj P) ≫
        ι'.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ τc.inv)).natTrans.app P) ≫
          (mateEquiv a' g' (TwoSquare.mk _ _ _ _ σ'.inv)).natTrans.app (T₂.obj P) := by
  rw [Adjunction.mateEquiv_app_eq_homEquiv a g ι Δ σ P,
    Adjunction.mateEquiv_app_eq_homEquiv a' g' ι' Δ' σ' (T₂.obj P)]
  apply (g'.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_symm_map_comp_mateEquiv_app]
  erw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_naturality_left_symm]
  have hc := Adjunction.homEquiv_symm_map_comp_mateEquiv_app a a' TC T₂ τc (𝟙 (cR.obj P))
  simp only [Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit] at hc
  have hσ' : τd.inv.app (ι.obj (cR.obj P)) ≫ TX.map (σ.inv.app (cR.obj P)) =
      dL'.map (τι.hom.app (cR.obj P)) ≫ σ'.inv.app (TC.obj (cR.obj P)) ≫
        Δ'.map (τc.inv.app (cR.obj P)) ≫ τΔ.inv.app (cL.obj (cR.obj P)) := by
    have hI : TX.mapIso (σ.app (cR.obj P)) ≪≫ τd.app _ ≪≫ dL'.mapIso (τι.app (cR.obj P)) =
        τΔ.app _ ≪≫ Δ'.mapIso (τc.app (cR.obj P)) ≪≫ σ'.app _ := Iso.ext (by simpa using hσ _)
    have h2 := congrArg Iso.inv hI
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at h2
    rw [← h2]
    simp [← Functor.map_comp_assoc]
  have hn := σ'.inv.naturality ((mateEquiv a a' (TwoSquare.mk _ _ _ _ τc.inv)).natTrans.app P)
  simp only [Functor.comp_map] at hn
  have hΔ := τΔ.inv.naturality (a.counit.app P)
  simp only [Functor.comp_map] at hΔ
  rw [Functor.map_comp, ← Category.assoc, hσ']
  erw [Equiv.symm_apply_apply]
  simp only [Category.assoc]
  congr 1
  rw [reassoc_of% hn, ← Functor.map_comp, hc, Functor.map_comp]
  congr 2
  rw [← cancel_mono (τΔ.inv.app P)]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact hΔ.symm


end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K}

/-- The supported restriction is the mate `Rc^! ⋙ Lι^* ⟶ LΔ^* ⋙ Rd^!` of the inverse of
compact-support base change in the fixed square. -/
lemma Correspondence.FixedLocus.supportedRestriction_eq_mateEquiv (F : c.FixedLocus)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    F.supportedRestriction P =
      (CategoryTheory.mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ c.support)
        (boundedConstructibleUpperShriekAdjunction ℓ F.d)
        (TwoSquare.mk _ _ _ _ F.lowerShriekBaseChangeIso.inv)).natTrans.app P := by
  rw [Adjunction.mateEquiv_app_eq_homEquiv, ← F.homEquiv_symm_supportedRestriction]
  exact (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
