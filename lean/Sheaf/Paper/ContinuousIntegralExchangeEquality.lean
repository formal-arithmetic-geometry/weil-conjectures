/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralComparisons

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction
universe v w
variable {A B A' B' : Type w} [Category.{v} A] [Category.{v} B]
  [Category.{v} A'] [Category.{v} B']
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
  {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
  {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
  {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
  (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)
private theorem coefficientMateCounit (M : A) :
    U₂.map ((pushHomOfComapIso adj₁ adj₂ e).app M) ≫ adjS.counit.app (E₁.obj M) =
      (pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv.app (L₁.obj M) ≫
        E₁.map (adjR.counit.app M) := by
  let α : TwoSquare E₂ U₁ U₂ E₁ :=
    .mk _ _ _ _ (pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv
  have hm := iterated_mateEquiv_conjugateEquiv adjR adjS adj₂ adj₁ α
  have he : (mateEquiv adj₁ adj₂ (mateEquiv adjR adjS α)).natTrans = e.inv := by
    rw [hm]
    exact (conjugateEquiv (adjR.comp adj₁) (adj₂.comp adjS)).apply_symm_apply e.inv
  have hh : mateEquiv adjR adjS α =
      (mateEquiv adj₁ adj₂).symm (TwoSquare.mk Res₁ L₂ L₁ Res₂ e.inv) := by
    apply (mateEquiv adj₁ adj₂).injective
    rw [Equiv.apply_symm_apply]
    exact he
  have hc := mateEquiv_counit adjR adjS α M
  rw [hh] at hc
  exact hc

section CoefficientExchange
variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
  [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
  [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
  {U : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
  {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
  (be : Ve ⊣ Se)
  (εa : ∀ K, U.obj (R.obj K) ⟶ K)
  (εb : ∀ K, V.obj (S.obj K) ⟶ K)
  (εae : ∀ K, Ue.obj (Re.obj K) ⟶ K)
  (εbe : ∀ K, Ve.obj (Se.obj K) ⟶ K)
  (hεbe : ∀ K, be.counit.app K = εbe K)
  (nεbe : ∀ K N (h : K ⟶ N), Ve.map (Se.map h) ≫ εbe N = εbe K ≫ h)
  {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
  {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
  (θ : ∀ K, V.obj (G.obj K) ⟶ H.obj (U.obj K))
  (θe : ∀ K, Ve.obj (Ge.obj K) ⟶ He.obj (Ue.obj K))
  (hθe : ∀ K N (h : K ⟶ N), Ve.map (Ge.map h) ≫ θe N =
    θe K ≫ He.map (Ue.map h))
  (B : ∀ K, G.obj (R.obj K) ⟶ S.obj (H.obj K))
  (Be : ∀ K, Ge.obj (Re.obj K) ⟶ Se.obj (He.obj K))
  (hB : ∀ K, V.map (B K) ≫ εb (H.obj K) =
    θ (R.obj K) ≫ H.map (εa K))
  (hBe : ∀ K, Ve.map (Be K) ≫ εbe (He.obj K) =
    θe (Re.obj K) ≫ He.map (εae K))
  (αU : ∀ K, T₂.obj (U.obj K) ⟶ Ue.obj (T₁.obj K))
  (αUi : ∀ K, Ue.obj (T₁.obj K) ⟶ T₂.obj (U.obj K))
  (αV : ∀ K, T₄.obj (V.obj K) ⟶ Ve.obj (T₃.obj K))
  (αVi : ∀ K, Ve.obj (T₃.obj K) ⟶ T₄.obj (V.obj K))
  (αG : ∀ K, T₃.obj (G.obj K) ⟶ Ge.obj (T₁.obj K))
  (αH : ∀ K, T₄.obj (H.obj K) ⟶ He.obj (T₂.obj K))
  (δ : ∀ K, T₁.obj (R.obj K) ⟶ Re.obj (T₂.obj K))
  (δ' : ∀ K, T₃.obj (S.obj K) ⟶ Se.obj (T₄.obj K))
  (hU : ∀ K, αU K ≫ αUi K = 𝟙 _)
  (hV : ∀ K, αVi K ≫ αV K = 𝟙 _)
  (hαV : ∀ K L (h : K ⟶ L), Ve.map (T₃.map h) ≫ αVi L =
    αVi K ≫ T₄.map (V.map h))
  (hαH : ∀ K L (h : K ⟶ L), T₄.map (H.map h) ≫ αH L =
    αH K ≫ He.map (T₂.map h))
  (hδ : ∀ K, Ue.map (δ K) ≫ εae (T₂.obj K) =
    αUi (R.obj K) ≫ T₂.map (εa K))
  (hδ' : ∀ K, Ve.map (δ' K) ≫ εbe (T₄.obj K) =
    αVi (S.obj K) ≫ T₄.map (εb K))
  (hcube : ∀ K, T₄.map (θ K) ≫ αH (U.obj K) ≫
      He.map (αU K) =
    αV (G.obj K) ≫ Ve.map (αG K) ≫ θe (T₁.obj K))

include hεbe nεbe hθe hU hV hB hBe hαV hαH hδ hδ' hcube in
private theorem coefficientExchange (K : C₂) :
    αG (R.obj K) ≫ Ge.map (δ K) ≫
        Be (T₂.obj K) =
      T₃.map (B K) ≫
        δ' (H.obj K) ≫ Se.map (αH K) := by
  apply (be.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp, Category.assoc, hεbe]
  rw [hBe]
  have hn := hθe _ _ (δ K)
  rw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp, hδ]
  have hn' := nεbe _ _ (αH K)
  rw [hn', reassoc_of% (hδ' (H.obj K))]
  rw [reassoc_of% (hαV _ _ (B K)),
    ← CategoryTheory.Functor.map_comp_assoc, hB]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hnH := hαH _ _ (εa K)
  rw [hnH]
  have hc := congrArg (fun z ↦ αVi (G.obj (R.obj K)) ≫ z ≫
    He.map (αUi (R.obj K))) (hcube (R.obj K))
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    hU,
    CategoryTheory.Functor.map_id, Category.comp_id] at hc
  simp only [← Category.assoc, hV, Category.id_comp] at hc
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ He.map (T₂.map (εa K))) hc.symm
end CoefficientExchange

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Coefficient extension respects the specified unit-square-counit exchange arrow.
Source: Bhatt--Scholze, Remark 6.8.15; ChangeOfCoefficients.lean, derived comparisons;
Mathlib/CategoryTheory/Adjunction/Mates.lean, iterated mate and conjugation identities.
(blueprint: lem-weil-pbc-continuous-integral-exchange-equality).

Proof. Write T for scalar extension, l for pullback, r for pushforward, α for the
pull comparison and δ for the push comparison. Both comparisons come from the same
restriction/pushforward isomorphism. The iterated mate/conjugation identity therefore
identifies l_E(δ) followed by the E-counit with α inverse followed by T of the integral
counit. The bounded constructible adjunction counit maps to the full derived counit,
so this identity restricts to the bounded constructible categories.

For arbitrary adjunctions, the specified unit-square-counit exchange has adjunct equal
to the square comparison followed by the counit. Apply adjunction injectivity to the
two sides of the required equation. Naturality of the E square comparison moves δ_f
past that comparison. The preceding mate/counit identity replaces the resulting
composite. Naturality of the second counit and of α_f′ inverse similarly rewrites the
other side. The remaining equation is the pull-comparison cube, precomposed with α_f′ inverse and
postcomposed with pullback of α_f inverse and of
the integral counit. Cancel the comparison isomorphisms. This proves the abstract
coefficient/exchange identity. Instantiate its functors, adjunctions and comparisons
with the specified scheme functors and their actual components.

For completeness the pull cube is proved underived by tensor balancing: restriction
and pushforward have the identity comparison of underlying sheaves, and its conjugate
pull comparison sends b ⊗ (a ⊗ m) to ba ⊗ m. The two composites along scheme maps agree
by associativity. Exact localization and flat-preserving inverse image derive that
identity on K-flat resolutions. Their composition constraints are precisely
leftDerivedUpperStarComp. Substitution by sq.w and proof irrelevance identify the two
paths; fully faithful bounded constructible restriction preserves the equation.
The private lemmas above establish the abstract mate and exchange algebra. Formal
restriction to the actual bounded adjunction counits, identification with the specified
three-factor exchange, and the derived pull cube remain to be completed here.
Neither δ nor the
exchange arrow is inverted; properness and Cartesianity are unnecessary. -/
theorem integralConstructible_exchange_equality
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    integralConstructibleSourceHom ℓ E k f g K ≫
        (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ k sq).app
          ((integralScalarConstructible ℓ E X).obj K) =
      (integralScalarConstructible ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ k sq).app K) ≫
        integralConstructibleTargetHom ℓ E k f' g' K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
