/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Multifunctor

/-!

# Verdier exchange, trace and Poincaré duality for an abstract pair of adjunctions

This file isolates the formal part of Verdier and Poincaré duality: the definitions of the
canonical morphisms out of the two adjunctions `f^* ⊣ f_*` and `f_! ⊣ f^!` of a six-functor
formalism, and the formal identities between them. Nothing here is specific to sheaves: the
categories `C` (for `D(X)`) and `D` (for `D(Y)`) are monoidal closed, and

* `adj : F ⊣ G` plays the role of `Lf^* ⊣ Rf_*`, with `F` oplax monoidal;
* `adj' : P ⊣ S` plays the role of `Rf_! ⊣ Rf^!`;
* `pf`, a natural transformation of bifunctors `C ⥤ D ⥤ D` from `(K, B) ↦ P K ⊗ B` to
  `(K, B) ↦ P (K ⊗ F B)`, plays the role of the derived exceptional projection morphism `PF^!`
  (`f_! K ⊗ B ⟶ f_!(K ⊗ f^* B)`), which in practice is constructed from a compactification (see
  `WeilConjectures.PoincareDuality.ProjectionFormula`), and is here an arbitrary natural
  transformation.

The internal hom `RHom(K, -)` is `ihom K`, the right adjoint of `K ⊗ -`; with this convention
`K` is always the *left* tensor factor, matching the direction of `PF^!`.

## Main definitions

* `CategoryTheory.Adjunction.projectionMorphism`: for `F ⊣ G` with `F` oplax monoidal, the
  projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)`, the mate of
  `F (G A ⊗ B) ⟶ F G A ⊗ F B ⟶ A ⊗ F B` (the morphism `PF^*` of
  `WeilConjectures/PoincareDuality/Verdier_Poincare_Maps_ProEtale_Condensed_EN.tex`).
* `CategoryTheory.Adjunction.projectionComparison`: for `P ⊣ S` with `S` lax monoidal, the
  comparison `P (M ⊗ S N) ⟶ P M ⊗ N`, adjoint to `M ⊗ S N ⟶ S P M ⊗ S N ⟶ S (P M ⊗ N)` (the
  morphism `q_j` for an open immersion `j`).
* `CategoryTheory.Verdier.exchangePairing` and `CategoryTheory.Verdier.exchange`: the Verdier
  exchange morphism `Φ_{K,L} : G RHom(K, S L) ⟶ RHom(P K, L)`, the transpose of the pairing
  `P K ⊗ G RHom(K, S L) ⟶ P (K ⊗ F G RHom(K, S L)) ⟶ P (K ⊗ RHom(K, S L)) ⟶ P S L ⟶ L`.
* `CategoryTheory.Verdier.trace`, `CategoryTheory.Verdier.poincareMap` and
  `CategoryTheory.Verdier.cupProduct`: for a chosen isomorphism `pur : S 𝟙 ≅ T`, the trace
  `P T ⟶ P S 𝟙 ⟶ 𝟙`, the Poincaré duality morphism `G T ⟶ G S 𝟙 ⟶ G RHom(𝟙, S 𝟙) ⟶ RHom(P 𝟙, 𝟙)`
  and the compact-support cup product `P 𝟙 ⊗ G T ⟶ P (𝟙 ⊗ F G T) ⟶ P (𝟙 ⊗ T) ⟶ P T`.
* `CategoryTheory.Verdier.bidualityMap`: in a braided monoidal closed category with an object
  `ω`, the double-dual morphism `K ⟶ D D K`, `D = RHom(-, ω)`, the transpose of
  `D K ⊗ K ⟶ K ⊗ D K ⟶ ω`.
* `CategoryTheory.Verdier.absoluteExchange` and `CategoryTheory.Verdier.dualExchange`: given
  dualizing objects `ω_X`, `ω_Y` and an isomorphism `γ : S ω_Y ≅ ω_X`, the absolute exchange
  `G D_X K ⟶ D_Y P K` and the opposite exchange `Θ_K : P D_X K ⟶ D_Y G K`.

## Main results

* `CategoryTheory.Verdier.uncurry_poincareMap`: **Poincaré duality is the trace–cup pairing**:
  the transpose `P 𝟙 ⊗ G T ⟶ 𝟙` of the Poincaré duality morphism is the composite of the cup
  product and the trace.
* `CategoryTheory.Verdier.isIso_exchange_of_isIso`: the exchange morphism `Φ_{K,L}` is an
  isomorphism if the component of `pf` at `(K, B)` is an isomorphism for every `B` (the Yoneda
  argument of the specification).

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-! ### The projection morphisms -/

namespace Adjunction

section ProjectionMorphism

/-!
In the application, `adj : F ⊣ G` is the derived adjunction `Lg^* ⊣ Rg_*` along the proper half
`g` of a compactification, and `projectionMorphism` is
`ProEtale.CondensedRing.properProjectionMorphism`.
-/

variable {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)` of an adjunction `F ⊣ G` with `F` oplax
monoidal: the adjoint of `F (G A ⊗ B) ⟶ F G A ⊗ F B ⟶ A ⊗ F B`. -/
noncomputable def projectionMorphism (A : C) (B : D) : G.obj A ⊗ B ⟶ G.obj (A ⊗ F.obj B) :=
  adj.homEquiv _ _ (δ F (G.obj A) B ≫ adj.counit.app A ▷ F.obj B)

/-- The projection morphism is natural in its second variable. -/
@[reassoc]
lemma projectionMorphism_natural_right (A : C) {B B' : D} (h : B ⟶ B') :
    G.obj A ◁ h ≫ adj.projectionMorphism A B' =
      adj.projectionMorphism A B ≫ G.map (A ◁ F.map h) := by
  rw [projectionMorphism, projectionMorphism, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right]
  congr 1
  rw [← δ_natural_right_assoc, whisker_exchange, Category.assoc]
  rfl

end ProjectionMorphism

section ProjectionComparison

/-!
In the application, `adj : P ⊣ S` is the derived adjunction `Dj_! ⊣ Lj^*` along the open
immersion half `j` of a compactification (for which `Lj^* = Rj^!`), and `projectionComparison` is
`ProEtale.CondensedRing.openImmersionProjectionComparison`.
-/

variable {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.LaxMonoidal]

/-- The projection comparison `P (M ⊗ S N) ⟶ P M ⊗ N` of an adjunction `P ⊣ S` with `S` lax
monoidal: the adjoint of `M ⊗ S N ⟶ S P M ⊗ S N ⟶ S (P M ⊗ N)`. -/
noncomputable def projectionComparison (M : C) (N : D) :
    P.obj (M ⊗ S.obj N) ⟶ P.obj M ⊗ N :=
  (adj.homEquiv _ _).symm (adj.unit.app M ▷ S.obj N ≫ μ S (P.obj M) N)

/-- The projection comparison is natural in its second variable. -/
@[reassoc]
lemma projectionComparison_natural_right (M : C) {N N' : D} (h : N ⟶ N') :
    P.map (M ◁ S.map h) ≫ adj.projectionComparison M N' =
      adj.projectionComparison M N ≫ P.obj M ◁ h := by
  rw [projectionComparison, projectionComparison, ← homEquiv_naturality_left_symm,
    ← homEquiv_naturality_right_symm, Category.assoc, ← μ_natural_right]
  congr 1
  rw [whisker_exchange_assoc]
  rfl

/-- The inverse of the projection comparison, when it is an isomorphism, is natural in the
second variable. -/
@[reassoc]
lemma inv_projectionComparison_natural_right (M : C) {N N' : D} (h : N ⟶ N')
    [IsIso (adj.projectionComparison M N)] [IsIso (adj.projectionComparison M N')] :
    P.obj M ◁ h ≫ inv (adj.projectionComparison M N') =
      inv (adj.projectionComparison M N) ≫ P.map (M ◁ S.map h) := by
  rw [IsIso.eq_inv_comp, ← projectionComparison_natural_right_assoc, IsIso.hom_inv_id,
    Category.comp_id]

end ProjectionComparison

end Adjunction

/-! ### Verdier exchange, trace and Poincaré duality -/

namespace Verdier

/-!
In the application to a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, `C` is
`Dᵇc(X)`, `D` is `Dᵇc(Y)`, and the data below are:

* `adj : F ⊣ G` is `Lf^* ⊣ Rf_*`,
  `ProEtale.CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction`;
* `adj' : P ⊣ S` is `Rf_! ⊣ Rf^!`,
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`;
* `pf` is the exceptional projection morphism `PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)`,
  `ProEtale.CondensedRing.boundedConstructibleExceptionalProjection`.

The input `pf` is a natural transformation of bifunctors `C ⥤ D ⥤ D`
```
pf : curriedTensorInsertFunctor₁ P ⟶ curriedTensorPost P ⋙ (whiskeringLeft D C D).obj F,
         (K, B) ↦ P K ⊗ B                       (K, B) ↦ P (K ⊗ F B)
```
whose component `(pf.app K).app B` is `PF^!_{f,K,B}`, natural in both `K` and `B`. Only the
naturality in `B` is used below (`pf_naturality_right`), in the Yoneda argument for `exchange`
and in the trace–cup comparison.

The natural transformation `pf` is an input rather than being built from `adj` and `adj'`:
neither `Adjunction.projectionMorphism` (which concerns `G = Rf_*`, not `P = Rf_!`) nor
`Adjunction.projectionComparison` (which goes the other way and involves `S = Rf^!`, not
`F = Lf^*`) produces it for a general `f`, and the two adjunctions alone give no canonical such
morphism. In the application it depends on a compactification `f = g ∘ j`, with `j` an open
immersion and `g` proper: it is the composite of `projectionMorphism` for `Lg^* ⊣ Rg_*`, the
inverse of `projectionComparison` for `Dj_! ⊣ Lj^*`, and `Lj^* Lg^* ≅ Lf^*`
(`ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification`).
-/

variable [MonoidalClosed C] [MonoidalClosed D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S)
  (pf : curriedTensorInsertFunctor₁ P ⟶
    curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)

omit [MonoidalClosed C] [MonoidalClosed D] in
/-- The naturality of the projection morphism `pf` in its second variable, written out. -/
@[reassoc]
lemma pf_naturality_right (K : C) {B B' : D} (h : B ⟶ B') :
    P.obj K ◁ h ≫ (pf.app K).app B' = (pf.app K).app B ≫ P.map (K ◁ F.map h) :=
  (pf.app K).naturality h

section Exchange

/-- The pairing `P K ⊗ G RHom(K, S L) ⟶ L` whose transpose is the Verdier exchange morphism: the
projection morphism `pf`, followed by the counit `F G ⟶ 𝟭`, the evaluation
`K ⊗ RHom(K, S L) ⟶ S L` and the counit `P S ⟶ 𝟭`. -/
noncomputable def exchangePairing (K : C) (L : D) :
    P.obj K ⊗ G.obj ((ihom K).obj (S.obj L)) ⟶ L :=
  (pf.app K).app _ ≫ P.map (K ◁ adj.counit.app _) ≫ P.map ((ihom.ev K).app _) ≫ adj'.counit.app L

/-- The **Verdier exchange morphism** `Φ_{K,L} : G RHom(K, S L) ⟶ RHom(P K, L)`, i.e.
`Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)`: the transpose of `exchangePairing` under the
tensor-hom adjunction. -/
noncomputable def exchange (K : C) (L : D) :
    G.obj ((ihom K).obj (S.obj L)) ⟶ (ihom (P.obj K)).obj L :=
  curry (exchangePairing adj adj' pf K L)

lemma uncurry_exchange (K : C) (L : D) :
    uncurry (exchange adj adj' pf K L) = exchangePairing adj adj' pf K L :=
  uncurry_curry _

/-- **Verdier exchange is an isomorphism** as soon as the projection morphisms
`(pf.app K).app B` are, for every `B`: for every test object `T`, composing with `Φ_{K,L}` is
the chain of bijections
```
Hom(T, G RHom(K, S L)) ≃ Hom(F T, RHom(K, S L)) ≃ Hom(K ⊗ F T, S L) ≃ Hom(P (K ⊗ F T), L)
  ≃ Hom(P K ⊗ T, L) ≃ Hom(T, RHom(P K, L)),
```
the fourth one being precomposition with the isomorphism `(pf.app K).app T`, so `Φ_{K,L}` is
an isomorphism by the Yoneda lemma. -/
theorem isIso_exchange_of_isIso (K : C) (L : D) [∀ B, IsIso ((pf.app K).app B)] :
    IsIso (exchange adj adj' pf K L) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have e : (fun u : T ⟶ G.obj ((ihom K).obj (S.obj L)) ↦ u ≫ exchange adj adj' pf K L) =
      curry ∘ (fun x ↦ (pf.app K).app T ≫ x) ∘ (adj'.homEquiv _ _).symm ∘ uncurry ∘
        (adj.homEquiv _ _).symm := by
    funext u
    simp only [Function.comp_apply, exchange, ← curry_natural_left, exchangePairing,
      pf_naturality_right_assoc, Adjunction.homEquiv_counit, uncurry_eq,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, Functor.map_comp]
  rw [e]
  refine Function.Bijective.comp ⟨curry_injective, fun g ↦ ⟨uncurry g, curry_uncurry g⟩⟩
    (Function.Bijective.comp ⟨fun a b h ↦ (cancel_epi ((pf.app K).app T)).1 h,
      fun y ↦ ⟨inv ((pf.app K).app T) ≫ y, by simp⟩⟩ (Function.Bijective.comp (Equiv.bijective _)
      (Function.Bijective.comp ⟨uncurry_injective, fun g ↦ ⟨curry g, uncurry_curry g⟩⟩
        (Equiv.bijective _))))

end Exchange

section Poincare

/-!
In the application, `f = p : X ⟶ S` is smooth of pure relative dimension `d`, `T` is the Tate
twist `ℚ̄_ℓ,X(d)[2d]`, and `pur : Rp^! ℚ̄_ℓ,S ≅ ℚ̄_ℓ,X(d)[2d]` is the purity isomorphism
`ProEtale.CondensedRing.boundedConstructibleSmoothPurityIso`.
-/

variable {T : C} (pur : S.obj (𝟙_ D) ≅ T)

/-- The **trace** `Tr : P T ⟶ 𝟙`, i.e. `Rf_! Λ(d)[2d] ⟶ Rf_! Rf^! Λ ⟶ Λ`: the inverse of the
chosen purity isomorphism `pur : S 𝟙 ≅ T`, followed by the counit of `P ⊣ S`. -/
noncomputable def trace : P.obj T ⟶ 𝟙_ D :=
  P.map pur.inv ≫ adj'.counit.app (𝟙_ D)

/-- The identification `X ⟶ RHom(𝟙, X)`, the transpose of the left unitor. -/
noncomputable def toIhomUnit (X : C) : X ⟶ (ihom (𝟙_ C)).obj X :=
  curry (λ_ X).hom

/-- The identification `X ⟶ RHom(𝟙, X)` is an isomorphism, its inverse being the evaluation
`RHom(𝟙, X) ≅ 𝟙 ⊗ RHom(𝟙, X) ⟶ X` (cf. `MonoidalClosed.unitIsoSelf`). -/
instance isIso_toIhomUnit (X : C) : IsIso (toIhomUnit X) := by
  refine ⟨(λ_ _).inv ≫ (ihom.ev (𝟙_ C)).app X, ?_, ?_⟩
  · rw [toIhomUnit, leftUnitor_inv_naturality_assoc, whiskerLeft_curry_ihom_ev_app,
      Iso.inv_hom_id]
  · apply uncurry_injective
    rw [toIhomUnit, uncurry_natural_left, uncurry_curry, leftUnitor_naturality,
      Iso.hom_inv_id_assoc, uncurry_id_eq_ev]

/-- The **Poincaré duality morphism** `PD : G T ⟶ RHom(P 𝟙, 𝟙)`, i.e.
`Rf_* Λ(d)[2d] ⟶ Rf_* Rf^! Λ ⟶ Rf_* RHom(Λ, Rf^! Λ) ⟶ RHom(Rf_! Λ, Λ)`: the inverse of the
purity isomorphism, the identification `X ≅ RHom(𝟙, X)`, and the Verdier exchange morphism
`Φ_{𝟙,𝟙}`. -/
noncomputable def poincareMap : G.obj T ⟶ (ihom (P.obj (𝟙_ C))).obj (𝟙_ D) :=
  G.map (pur.inv ≫ toIhomUnit _) ≫ exchange adj adj' pf (𝟙_ C) (𝟙_ D)

/-- The **compact-support cup product** `P 𝟙 ⊗ G T ⟶ P T`, i.e.
`Rf_! Λ ⊗ Rf_* Λ(d)[2d] ⟶ Rf_!(Λ ⊗ Lf^* Rf_* Λ(d)[2d]) ⟶ Rf_!(Λ ⊗ Λ(d)[2d]) ⟶ Rf_! Λ(d)[2d]`:
the projection morphism, the counit `F G ⟶ 𝟭` and the left unitor. -/
noncomputable def cupProduct : P.obj (𝟙_ C) ⊗ G.obj T ⟶ P.obj T :=
  (pf.app (𝟙_ C)).app (G.obj T) ≫ P.map (𝟙_ C ◁ adj.counit.app T) ≫ P.map (λ_ T).hom

/-- **Poincaré duality is the trace–cup pairing.** The transpose `P 𝟙 ⊗ G T ⟶ 𝟙` of the
Poincaré duality morphism is exactly the cup product followed by the trace. In particular the
Poincaré duality morphism, the trace and the pairing share the normalization of the purity
isomorphism. -/
theorem uncurry_poincareMap :
    uncurry (poincareMap adj adj' pf pur) = cupProduct adj pf ≫ trace adj' pur := by
  rw [poincareMap, uncurry_natural_left, uncurry_exchange, exchangePairing,
    pf_naturality_right_assoc, cupProduct, trace]
  simp only [Category.assoc, ← P.map_comp_assoc, ← P.map_comp]
  congr 3
  have hc := adj.counit_naturality (pur.inv ≫ toIhomUnit (S.obj (𝟙_ D)))
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hc, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, toIhomUnit, whiskerLeft_curry_ihom_ev_app]
  simp

end Poincare

section Biduality

/-!
In the application, `ω` is the dualizing complex `ω_X = Ra^! Λ_S` of the structure morphism
`a : X ⟶ S`, `ProEtale.CondensedRing.relativeDualizingComplex`.
-/

variable [BraidedCategory C] (ω : C)

/-- The **double-dual morphism** `δ_K : K ⟶ D D K`, where `D = RHom(-, ω)`: the transpose of
the evaluation pairing `D K ⊗ K ⟶ K ⊗ D K ⟶ ω`. It exists without any biduality
assumption. -/
noncomputable def bidualityMap (K : C) : K ⟶ (ihom ((ihom K).obj ω)).obj ω :=
  curry ((β_ _ _).hom ≫ (ihom.ev K).app ω)

end Biduality

section AbsoluteExchange

/-!
In the application, `ωX` and `ωY` are the dualizing complexes `ω_X` and `ω_Y`
(`ProEtale.CondensedRing.relativeDualizingComplex`) of the structure morphisms
`a_X = f ≫ a_Y : X ⟶ S` and `a_Y : Y ⟶ S`, and `γ : Rf^! ω_Y ≅ ω_X` is the composition isomorphism
`R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!` at the unit,
`ProEtale.CondensedRing.upperShriekDualizingComplexIso`.
-/

variable (ωX : C) (ωY : D) (γ : S.obj ωY ≅ ωX)

/-- The **absolute Verdier exchange morphism** `G D_X K ⟶ D_Y P K`, i.e.
`Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K`, where `D_X = RHom(-, ω_X)` and `D_Y = RHom(-, ω_Y)`, given an
identification `γ : S ω_Y ≅ ω_X` (`Rf^! ω_Y ≅ ω_X`): the exchange morphism `Φ_{K,ω_Y}`
precomposed with `γ`. -/
noncomputable def absoluteExchange (K : C) :
    G.obj ((ihom K).obj ωX) ⟶ (ihom (P.obj K)).obj ωY :=
  G.map ((ihom K).map γ.inv) ≫ exchange adj adj' pf K ωY

variable [BraidedCategory C] [BraidedCategory D]

/-- The morphism `a_K : G K ⟶ D_Y P D_X K`, i.e. `Rf_* K ⟶ Rf_* 𝔻_X 𝔻_X K ⟶ 𝔻_Y Rf_! 𝔻_X K`:
the double-dual morphism followed by the absolute exchange morphism. -/
noncomputable def dualExchangeAux (K : C) :
    G.obj K ⟶ (ihom (P.obj ((ihom K).obj ωX))).obj ωY :=
  G.map (bidualityMap ωX K) ≫ absoluteExchange adj adj' pf ωX ωY γ ((ihom K).obj ωX)

/-- The **opposite Verdier exchange morphism** `Θ_K : P D_X K ⟶ D_Y G K`, i.e.
`Rf_! 𝔻_X K ⟶ 𝔻_Y 𝔻_Y Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`: the double-dual morphism followed by the dual
of `dualExchangeAux`. It is determined by the exchange and double-dual morphisms rather than
chosen independently; the familiar `𝔻_Y Rf_* K ≅ Rf_! 𝔻_X K` is its inverse when it is
invertible. -/
noncomputable def dualExchange (K : C) :
    P.obj ((ihom K).obj ωX) ⟶ (ihom (G.obj K)).obj ωY :=
  bidualityMap ωY _ ≫ (pre (dualExchangeAux adj adj' pf ωX ωY γ K)).app ωY

end AbsoluteExchange

end Verdier

end CategoryTheory
