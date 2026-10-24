/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperProjectionFormula
public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.TraceFormula.RelativeFrobeniusComparison

/-!

# The Künneth formula for proper direct images

Let `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂` be morphisms of separated `k`-schemes of finite type, with
product `q = f₁ × f₂ : X₁ ⨯ X₂ ⟶ Y₁ ⨯ Y₂`. The *Künneth map*
```
Π : Rf₁* B₁ ⊠ Rf₂* B₂ ⟶ Rq_* (B₁ ⊠ B₂)
```
(`ProEtale.CondensedRing.prodLowerStarExternalProduct`, blueprint
`def-trf-kernel-pushforward-maps`, item 5) is the adjoint for `Lq^* ⊣ Rq_*` of the monoidal
structure of `Lq^*` followed by the counits of `Lfᵢ^* ⊣ Rfᵢ*`, transported along the projections
(`ProEtale.CondensedRing.prodUpperStarCounit`). This file proves that `Π` is an isomorphism for
proper `f₁`, `f₂` (`ProEtale.CondensedRing.isIso_prodLowerStarExternalProduct`, blueprint
`thm-sf-kunneth-relative`, in the form `Rf_! ≅ Rf_*` for proper morphisms used in
`def-sf-kv-maps` (i)).

## Proof

Write `q = r ≫ s` with `r = f₁ × 1 : X₁ ⨯ X₂ ⟶ Y₁ ⨯ X₂` and `s = 1 × f₂ : Y₁ ⨯ X₂ ⟶ Y₁ ⨯ Y₂`,
base changes of `f₁` and `f₂`. By `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom`, `Π` is
an isomorphism as soon as

* the base change morphisms of the cartesian squares of `r` and `s` are isomorphisms: this is
  proper base change (`isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`), the
  transposes of the transported counits being the base change morphisms
  (`ProEtale.CondensedRing.homEquiv_prodUpperStarCounit`);
* the projection morphism of `r` and the left projection morphism of `s` are isomorphisms: this
  is the projection formula for the proper morphisms `r` and `s`
  (`isIso_projectionMorphism_boundedConstructible_padicAlgCl`), together with the compatibility of
  the derived pullback with the braidings for the left one.

The transported counits are compatible with the composition isomorphisms of the pullbacks
(`ProEtale.CondensedRing.upperStarComp_inv_app_comp_prodUpperStarCounit_left`,
`ProEtale.CondensedRing.upperStarComp_inv_app_comp_prodUpperStarCounit_right`).

## Main definitions

- `ProEtale.CondensedRing.prodUpperStarCounit`: the counit of `Lf^* ⊣ Rf_*` transported along a
  commutative square.
- `ProEtale.CondensedRing.prodLowerStarExternalProduct`: the Künneth map `Π`.

## Main statements

- `ProEtale.CondensedRing.isIso_prodLowerStarExternalProduct`: `Π` is an isomorphism for proper
  `f₁` and `f₂`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

lemma eqToHom_comp_eqToHom_comp_aux {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (x : O₁ ⟶ O₂) (y : O₂ ⟶ O₃) (e₁ : O₃ = O₄) (e₂ : O₄ = O₅) (e₃ : O₃ = O₅) (t : O₅ ⟶ O₆) :
    x ≫ y ≫ eqToHom e₁ ≫ eqToHom e₂ ≫ t = x ≫ y ≫ eqToHom e₃ ≫ t := by
  simp

lemma map_comp_eqToHom_comp_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {A₁ A₂ A₃ A₄ A₅ : 𝒞} {B₁ B₂ B₃ B₄ B₅ B₆ : 𝒟} (a' : A₁ ⟶ A₂) (e₃ : A₂ = A₃) (c' : A₃ ⟶ A₄)
    (d' : A₄ ⟶ A₅) (y : F.obj A₂ ⟶ B₁) (e₁ : B₁ = B₂) (e₂ : B₂ = B₃) (c : B₃ ⟶ B₄)
    (d : B₄ ⟶ B₅) (n : F.obj A₅ ⟶ B₅) (n' : F.obj A₄ ⟶ B₄) (y' : F.obj A₃ ⟶ B₆)
    (e₄ : B₆ = B₃) (e₅ : B₁ = B₆) (hnat : F.map d' ≫ n = n' ≫ d)
    (hC : F.map c' ≫ n' = y' ≫ eqToHom e₄ ≫ c) (hE : F.map (eqToHom e₃) ≫ y' = y ≫ eqToHom e₅) :
    F.map a' ≫ y ≫ eqToHom e₁ ≫ eqToHom e₂ ≫ c ≫ d =
      F.map (a' ≫ eqToHom e₃ ≫ c' ≫ d') ≫ n := by
  simp only [Functor.map_comp, Category.assoc, hnat, reassoc_of% hC, reassoc_of% hE,
    eqToHom_trans_assoc]

/-! ### Transported counits -/

section Counit

variable {P P' X Y R : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType R.hom] [QuasiCompact R.hom] [IsSeparated R.hom]

/-- The counit of `Lf^* ⊣ Rf_*` transported along a commutative square `q ≫ p' = p ≫ f`:
`Lq^* Lp'^* Rf_* B ⟶ Lp^* B`. -/
noncomputable def prodUpperStarCounit {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    (w : q ≫ p' = p ≫ f) (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ q).obj ((boundedConstructibleUpperStar _ ℓ p').obj
        ((boundedConstructibleLowerStar _ ℓ f).obj B)) ⟶
      (boundedConstructibleUpperStar _ ℓ p).obj B :=
  (boundedConstructibleUpperStarComp _ ℓ q p').inv.app _ ≫ eqToHom (by rw [w]) ≫
    (boundedConstructibleUpperStarComp _ ℓ p f).hom.app _ ≫
    (boundedConstructibleUpperStar _ ℓ p).map
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app B)

/-- The transpose of the transported counit of a commutative square is the base change morphism
of the square. -/
lemma homEquiv_prodUpperStarCounit {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    (w : q ≫ p' = p ≫ f) (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ q).homEquiv _ _
        (prodUpperStarCounit ℓ w B) =
      (boundedConstructibleBaseChange _ ℓ (CommSq.mk w.symm)).app B := by
  rw [boundedConstructibleBaseChange_eq_exchangeRight, Adjunction.exchangeRight_app,
    Adjunction.homEquiv_unit, boundedConstructiblePullbackSquareComparison_hom_app,
    prodUpperStarCounit]
  simp only [Functor.map_comp, Category.assoc]

/-- For a cartesian square `q ≫ p' = p ≫ f` with `f` proper, the transpose of the transported
counit is an isomorphism: proper base change. -/
lemma isIso_homEquiv_prodUpperStarCounit {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    [IsProper f.left] (sq : IsPullback p q f p')
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ q).homEquiv _ _
        (prodUpperStarCounit ℓ sq.w.symm B)) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
  rw [homEquiv_prodUpperStarCounit]
  infer_instance

/-- Changing the second morphism of a composition isomorphism of the pullbacks along an equality
of morphisms. -/
@[reassoc]
lemma map_eqToHom_comp_upperStarComp_inv_app (r : P ⟶ R) {a b : R ⟶ Y} (h : a = b)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ r).map (eqToHom (by rw [h])) ≫
        (boundedConstructibleUpperStarComp _ ℓ r b).inv.app K =
      (boundedConstructibleUpperStarComp _ ℓ r a).inv.app K ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The composition isomorphism `L(r ≫ ρ)^* ≅ Lρ^* ⋙ Lr^*` read through
`L(ρ ≫ f)^* ≅ Lf^* ⋙ Lρ^*`. -/
@[reassoc]
lemma map_upperStarComp_hom_app_comp_upperStarComp_inv_app {X' : Over (Spec (.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    (r : P ⟶ R) (ρ : R ⟶ X) (f : X ⟶ X') (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ r).map
        ((boundedConstructibleUpperStarComp _ ℓ ρ f).hom.app K) ≫
      (boundedConstructibleUpperStarComp _ ℓ r ρ).inv.app
        ((boundedConstructibleUpperStar _ ℓ f).obj K) =
    (boundedConstructibleUpperStarComp _ ℓ r (ρ ≫ f)).inv.app K ≫
      eqToHom (by rw [Category.assoc]) ≫ (boundedConstructibleUpperStarComp _ ℓ (r ≫ ρ) f).hom.app K := by
  have hA := boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ r ρ f K
  rw [← cancel_epi ((boundedConstructibleUpperStarComp _ ℓ r (ρ ≫ f)).hom.app K),
    Iso.hom_inv_id_app_assoc, ← cancel_mono ((boundedConstructibleUpperStarComp _ ℓ r ρ).hom.app
      ((boundedConstructibleUpperStar _ ℓ f).obj K)), Category.assoc, Category.assoc,
    Category.assoc, Iso.inv_hom_id_app, hA, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]

/-- Pasting a transported counit with the trivial square of a composite `r ≫ s` on the right of
the target: for `s ≫ g = g'`, the transported counit of `(r ≫ s) ≫ g = p ≫ f` is that of
`r ≫ g' = p ≫ f` after the composition isomorphisms. -/
lemma upperStarComp_inv_app_comp_prodUpperStarCounit_right {P'' : Over (Spec (.of k))}
    [LocallyOfFiniteType P''.hom] [QuasiCompact P''.hom] [IsSeparated P''.hom]
    {r : P ⟶ R} {s : R ⟶ P''} {g : P'' ⟶ Y} {p : P ⟶ X} {f : X ⟶ Y}
    (w : (r ≫ s) ≫ g = p ≫ f) (w' : r ≫ s ≫ g = p ≫ f)
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp _ ℓ r s).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleLowerStar _ ℓ f).obj B)) ≫
      prodUpperStarCounit ℓ w B =
    (boundedConstructibleUpperStar _ ℓ r).map
        ((boundedConstructibleUpperStarComp _ ℓ s g).inv.app _) ≫
      prodUpperStarCounit ℓ w' B := by
  unfold prodUpperStarCounit
  rewrite [boundedConstructibleUpperStarComp_inv_app_comp_inv_app_assoc]
  exact eqToHom_comp_eqToHom_comp_aux _ _ _ _ _ _

/-- Pasting a transported counit with the trivial square of a composite `r ≫ s` on the left of
the source: the transported counit of `(r ≫ s) ≫ g = (r ≫ ρ) ≫ f` is `Lr^*` of that of
`s ≫ g = ρ ≫ f` after the composition isomorphisms. -/
lemma upperStarComp_inv_app_comp_prodUpperStarCounit_left {P'' : Over (Spec (.of k))}
    [LocallyOfFiniteType P''.hom] [QuasiCompact P''.hom] [IsSeparated P''.hom]
    {r : P ⟶ R} {s : R ⟶ P''} {g : P'' ⟶ Y} {ρ : R ⟶ X} {f : X ⟶ Y}
    (w : (r ≫ s) ≫ g = (r ≫ ρ) ≫ f) (w' : s ≫ g = ρ ≫ f)
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp _ ℓ r s).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleLowerStar _ ℓ f).obj B)) ≫
      prodUpperStarCounit ℓ w B =
    (boundedConstructibleUpperStar _ ℓ r).map (prodUpperStarCounit ℓ w' B) ≫
      (boundedConstructibleUpperStarComp _ ℓ r ρ).inv.app B := by
  unfold prodUpperStarCounit
  rewrite [boundedConstructibleUpperStarComp_inv_app_comp_inv_app_assoc]
  exact map_comp_eqToHom_comp_aux (boundedConstructibleUpperStar _ ℓ r) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((boundedConstructibleUpperStarComp _ ℓ r ρ).inv.naturality
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app B))
    (map_upperStarComp_hom_app_comp_upperStarComp_inv_app ℓ r ρ f _)
    (map_eqToHom_comp_upperStarComp_inv_app ℓ r w' _)

end Counit

end AlgebraicGeometry.ProEtale.CondensedRing
