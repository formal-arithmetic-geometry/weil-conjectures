/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso

/-!

# The coherence behind the comparison of Galois and model Frobenii

This file proves the formal part of the comparison between the local Frobenius of a Weil sheaf
for the Frobenius `σ` twisted by an automorphism `g` and the local Frobenius of the base change
with the model Frobenius, for abstract families of pullback functors.

Let `𝒞` be a category (of schemes) with two families of pullback functors: `U a : D B ⥤ D A`
(the derived pullbacks) and `V a : E B ⥤ E A` (the pullbacks of sheaves), for `a : A ⟶ B`, with
composition isomorphisms `U (a ≫ b) ≅ U b ⋙ U a` and `V (a ≫ b) ≅ V b ⋙ V a` satisfying the
associativity law, and functors `H A : D A ⥤ E A` (the homology sheaves) with commutation
isomorphisms `h a : H B ⋙ V a ≅ U a ⋙ H A` compatible with the composition isomorphisms.

Consider a geometric point `x̄ = x' ≫ π : P ⟶ X` of `X` (a morphism `xb` with `x' ≫ π = xb`),
where `π : Y ⟶ X` is the base change and `x' : P ⟶ Y` a rational point fixed by the model
Frobenius `Φ : Y ⟶ Y`, which lies over
`g ≫ F` for the Frobenius `F` of `X`: `Φ ≫ π = π ≫ g ≫ F`. Let `κ` be trivializations of the
pullbacks along `F`, compatible with `H`, and `τ : V σ ≅ 𝟭` a trivialization of the pullback along
an endomorphism `σ` of `P` with `x̄ ≫ g = σ ≫ x̄`, compatible with `κ` at `x̄`. For `φ : U g K ⟶ K`,
the homology of the model Frobenius
```
U x' U π K = U (x' ≫ Φ) U π K ≅ U x' U Φ U π K ≅ U x' U (π ≫ g ≫ F) K
  ≅ U x' U π U g U F K --κ--> U x' U π U g K --φ--> U x' U π K
```
is conjugate, through `H (U x' U π K) ≅ H (U x̄ K) ≅ V x̄ H K`, to the Galois Frobenius
```
V x̄ H K --τ⁻¹--> V σ V x̄ H K ≅ V (σ ≫ x̄) H K = V (x̄ ≫ g) H K ≅ V x̄ V g H K
  --V x̄ φ_H--> V x̄ H K
```
of `(H K, φ_H = h g ≫ H φ)` (`ProEtale.CondensedRing.homology_modelFrobenius_comp_eq_aux`).

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type u₁} [∀ A, Category.{v₁} (D A)]
  {E : 𝒞 → Type u₂} [∀ A, Category.{v₂} (E A)]

section Pullback

variable (U : ∀ {A B : 𝒞}, (A ⟶ B) → D B ⥤ D A)
  (cU : ∀ {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C), U (a ≫ b) ≅ U b ⋙ U a)

/-- The pullback functors along equal morphisms agree through `eqToHom`. -/
@[reassoc]
lemma eqToHom_comp_map_aux {A B : 𝒞} {t t' : A ⟶ B} (h : t = t') {M M' : D B} (f : M ⟶ M') :
    eqToHom (congrArg (fun s ↦ (U s).obj M) h) ≫ (U t').map f =
      (U t).map f ≫ eqToHom (congrArg (fun s ↦ (U s).obj M') h) := by
  subst h
  simp

/-- The composition isomorphism is natural in the second morphism, through `eqToHom`. -/
@[reassoc]
lemma comp_hom_app_comp_map_eqToHom_aux {A B C : 𝒞} (a : A ⟶ B) {b b' : B ⟶ C} (h : b = b')
    (M : D C) :
    (cU a b).hom.app M ≫ (U a).map (eqToHom (congrArg (fun s ↦ (U s).obj M) h)) =
      eqToHom (congrArg (fun s ↦ (U (a ≫ s)).obj M) h) ≫ (cU a b').hom.app M := by
  subst h
  simp

/-- The composition isomorphism is natural in the first morphism, through `eqToHom`. -/
@[reassoc]
lemma eqToHom_comp_comp_inv_app_aux {A B C : 𝒞} {a a' : A ⟶ B} (h : a = a') (b : B ⟶ C)
    (M : D C) :
    eqToHom (congrArg (fun s ↦ (U s).obj ((U b).obj M)) h) ≫ (cU a' b).inv.app M =
      (cU a b).inv.app M ≫ eqToHom (congrArg (fun s ↦ (U (s ≫ b)).obj M) h) := by
  subst h
  simp

/-- The composition isomorphism is natural in the first morphism, through `eqToHom`. -/
@[reassoc]
lemma eqToHom_comp_comp_hom_app_aux {A B C : 𝒞} {a a' : A ⟶ B} (h : a = a') (b : B ⟶ C)
    (M : D C) :
    eqToHom (congrArg (fun s ↦ (U (s ≫ b)).obj M) h) ≫ (cU a' b).hom.app M =
      (cU a b).hom.app M ≫ eqToHom (congrArg (fun s ↦ (U s).obj ((U b).obj M)) h) := by
  subst h
  simp

/-- Naturality of the inverse of the composition isomorphism, with the composite functor
unfolded. -/
@[reassoc]
lemma map_map_comp_inv_app_aux {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C) {M M' : D C} (f : M ⟶ M') :
    (U a).map ((U b).map f) ≫ (cU a b).inv.app M' = (cU a b).inv.app M ≫ (U (a ≫ b)).map f :=
  (cU a b).inv.naturality f

/-- Naturality of the composition isomorphism, with the composite functor unfolded. -/
@[reassoc]
lemma map_comp_hom_app_aux {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C) {M M' : D C} (f : M ⟶ M') :
    (U (a ≫ b)).map f ≫ (cU a b).hom.app M' = (cU a b).hom.app M ≫ (U a).map ((U b).map f) :=
  (cU a b).hom.naturality f

/-- The inverse of the composition isomorphism is natural in the second morphism, through
`eqToHom`. -/
@[reassoc]
lemma map_eqToHom_comp_inv_app_aux {A B C : 𝒞} (a : A ⟶ B) {b b' : B ⟶ C} (h : b = b')
    (M : D C) :
    (U a).map (eqToHom (congrArg (fun s ↦ (U s).obj M) h)) ≫ (cU a b').inv.app M =
      (cU a b).inv.app M ≫ eqToHom (congrArg (fun s ↦ (U (a ≫ s)).obj M) h) := by
  subst h
  simp

/-- The associativity law of the composition isomorphisms, in a mixed form. -/
@[reassoc]
lemma map_hom_app_comp_inv_app_aux {A B C C' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C')
    (M : D C')
    (hassoc : (cU (a ≫ b) c).hom.app M ≫ (cU a b).hom.app ((U c).obj M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc a b c)) ≫
        (cU a (b ≫ c)).hom.app M ≫ (U a).map ((cU b c).hom.app M)) :
    (U a).map ((cU b c).hom.app M) ≫ (cU a b).inv.app ((U c).obj M) =
      (cU a (b ≫ c)).inv.app M ≫
        eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc a b c).symm) ≫
          (cU (a ≫ b) c).hom.app M := by
  rw [← cancel_epi (eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc a b c)) ≫
    (cU a (b ≫ c)).hom.app M)]
  conv_lhs => simp only [Category.assoc]
  rw [← reassoc_of% hassoc]
  simp

/-- The associativity law of the composition isomorphisms, in inverse form. -/
@[reassoc]
lemma map_inv_app_comp_inv_app_aux {A B C C' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C')
    (M : D C')
    (hassoc : (cU (a ≫ b) c).hom.app M ≫ (cU a b).hom.app ((U c).obj M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc a b c)) ≫
        (cU a (b ≫ c)).hom.app M ≫ (U a).map ((cU b c).hom.app M)) :
    (U a).map ((cU b c).inv.app M) ≫ (cU a (b ≫ c)).inv.app M =
      (cU a b).inv.app ((U c).obj M) ≫ (cU (a ≫ b) c).inv.app M ≫
        eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc a b c)) := by
  rw [← cancel_epi ((cU (a ≫ b) c).hom.app M ≫ (cU a b).hom.app ((U c).obj M))]
  conv_lhs => simp only [Category.assoc]
  rw [reassoc_of% hassoc]
  simp [← Functor.map_comp_assoc]

/-- The isomorphism `U t ≅ U t'` of the pullback functors along equal morphisms, with components
`eqToHom`. Unlike `eqToIso` of an equality of functors, its components are equalities of
objects, which is cheap for the kernel. -/
def pullbackCongrIso {A B : 𝒞} {t t' : A ⟶ B} (h : t = t') : U t ≅ U t' :=
  NatIso.ofComponents (fun M ↦ eqToIso (congrArg (fun s ↦ (U s).obj M) h))
    (fun f ↦ (eqToHom_comp_map_aux U h f).symm)

@[simp]
lemma pullbackCongrIso_hom_app {A B : 𝒞} {t t' : A ⟶ B} (h : t = t') (M : D B) :
    (pullbackCongrIso U h).hom.app M = eqToHom (congrArg (fun s ↦ (U s).obj M) h) :=
  rfl

end Pullback

section Homology

variable (U : ∀ {A B : 𝒞}, (A ⟶ B) → D B ⥤ D A) (V : ∀ {A B : 𝒞}, (A ⟶ B) → E B ⥤ E A)
  (H : ∀ A, D A ⥤ E A) (h : ∀ {A B : 𝒞} (a : A ⟶ B), H B ⋙ V a ≅ U a ⋙ H A)

/-- Naturality of the commutation isomorphism of homology and pullback, with the composite
functors unfolded. -/
@[reassoc]
lemma map_map_comp_hom_app_aux {A B : 𝒞} (a : A ⟶ B) {M M' : D B} (f : M ⟶ M') :
    (V a).map ((H B).map f) ≫ (h a).hom.app M' = (h a).hom.app M ≫ (H A).map ((U a).map f) :=
  (h a).hom.naturality f

/-- The commutation isomorphism of homology and pullback is natural in the morphism, through
`eqToHom`. -/
@[reassoc]
lemma hom_app_comp_map_eqToHom_aux {A B : 𝒞} {t t' : A ⟶ B} (e : t = t') (M : D B) :
    (h t).hom.app M ≫ (H A).map (eqToHom (congrArg (fun s ↦ (U s).obj M) e)) =
      eqToHom (congrArg (fun s ↦ (V s).obj ((H B).obj M)) e) ≫ (h t').hom.app M := by
  subst e
  simp

end Homology

/-- The components of a composite `F ⋙ 𝟭 ≅ F ⋙ S ≅ G₁ ≅ G₂ ≅ G₃` starting with the
whiskering of the inverse of a trivialization `τ : S ≅ 𝟭`. -/
lemma isoWhiskerLeft_symm_trans_hom_app_aux {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    (F : C₀ ⥤ D₀) {S : D₀ ⥤ D₀} (τ : S ≅ 𝟭 D₀) {G₁ G₂ G₃ : C₀ ⥤ D₀} (c₁ : G₁ ≅ F ⋙ S)
    (E : G₁ ≅ G₂) (c₂ : G₂ ≅ G₃) (M : C₀) :
    (Functor.isoWhiskerLeft F τ.symm ≪≫ c₁.symm ≪≫ E ≪≫ c₂).hom.app M =
      τ.inv.app (F.obj M) ≫ c₁.inv.app M ≫ E.hom.app M ≫ c₂.hom.app M := by
  simp

variable (U : ∀ {A B : 𝒞}, (A ⟶ B) → D B ⥤ D A)
  (cU : ∀ {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C), U (a ≫ b) ≅ U b ⋙ U a)
  (assocU : ∀ {A B C C' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C') (M : D C'),
    (cU (a ≫ b) c).hom.app M ≫ (cU a b).hom.app ((U c).obj M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc a b c)) ≫
        (cU a (b ≫ c)).hom.app M ≫ (U a).map ((cU b c).hom.app M))
  (V : ∀ {A B : 𝒞}, (A ⟶ B) → E B ⥤ E A)
  (cV : ∀ {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C), V (a ≫ b) ≅ V b ⋙ V a)
  (assocV : ∀ {A B C C' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C') (M : E C'),
    (cV (a ≫ b) c).hom.app M ≫ (cV a b).hom.app ((V c).obj M) =
      eqToHom (congrArg (fun s ↦ (V s).obj M) (Category.assoc a b c)) ≫
        (cV a (b ≫ c)).hom.app M ≫ (V a).map ((cV b c).hom.app M))
  (H : ∀ A, D A ⥤ E A) (h : ∀ {A B : 𝒞} (a : A ⟶ B), H B ⋙ V a ≅ U a ⋙ H A)
  (hcomp : ∀ {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (M : D C),
    (h (a ≫ b)).hom.app M ≫ (H A).map ((cU a b).hom.app M) =
      (cV a b).hom.app ((H C).obj M) ≫ (V a).map ((h b).hom.app M) ≫
        (h a).hom.app ((U b).obj M))
  {P Y X : 𝒞} (x' : P ⟶ Y) (Φ : Y ⟶ Y) (π : Y ⟶ X) (g F : X ⟶ X) (σ : P ⟶ P)
  (xb : P ⟶ X) (hxb : x' ≫ π = xb)
  (hfix : x' ≫ Φ = x') (hΦ : Φ ≫ π = π ≫ g ≫ F) (hgal : xb ≫ g = σ ≫ xb)
  (hσF : (σ ≫ xb) ≫ F = xb)
  (κD : U F ≅ 𝟭 (D X)) (κE : V F ≅ 𝟭 (E X))
  (hκ : ∀ M : D X, (h F).hom.app M ≫ (H X).map (κD.hom.app M) = κE.hom.app ((H X).obj M))
  (τ : V σ ≅ 𝟭 (E P))
  (hτ : ∀ M : E X, τ.inv.app ((V xb).obj M) ≫ (cV σ xb).inv.app M =
    eqToHom (congrArg (fun s ↦ (V s).obj M) hσF.symm) ≫ (cV (σ ≫ xb) F).hom.app M ≫
      (V (σ ≫ xb)).map (κE.hom.app M))
  (K : D X) (φ : (U g).obj K ⟶ K)

/-- The model Frobenius on `U x' U π K`:
`U x' U π K = U (x' ≫ Φ) U π K ≅ U x' U Φ U π K ≅ U x' U (Φ ≫ π) K = U x' U (π ≫ g ≫ F) K
≅ U x' U π U (g ≫ F) K ≅ U x' U π U g U F K --κ--> U x' U π U g K --φ--> U x' U π K`. -/
def modelFrobeniusAux : (U x').obj ((U π).obj K) ⟶ (U x').obj ((U π).obj K) :=
  eqToHom (congrArg (fun s ↦ (U s).obj ((U π).obj K)) hfix.symm) ≫
    (cU x' Φ).hom.app ((U π).obj K) ≫
    (U x').map ((cU Φ π).inv.app K ≫ eqToHom (congrArg (fun s ↦ (U s).obj K) hΦ) ≫
      (cU π (g ≫ F)).hom.app K ≫
      (U π).map ((cU g F).hom.app K ≫ (U g).map (κD.hom.app K) ≫ φ))

/-- The Galois Frobenius on `V x̄ H K` for `x̄ = xb`:
`V x̄ H K --τ⁻¹--> V σ V x̄ H K ≅ V (σ ≫ x̄) H K = V (x̄ ≫ g) H K ≅ V x̄ V g H K
--V x̄ φ_H--> V x̄ H K` for `φ_H = h g ≫ H φ`. -/
def galoisFrobeniusAux : (V xb).obj ((H X).obj K) ⟶ (V xb).obj ((H X).obj K) :=
  τ.inv.app ((V xb).obj ((H X).obj K)) ≫ (cV σ xb).inv.app ((H X).obj K) ≫
    eqToHom (congrArg (fun s ↦ (V s).obj ((H X).obj K)) hgal.symm) ≫
    (cV xb g).hom.app ((H X).obj K) ≫
    (V xb).map ((h g).hom.app K ≫ (H X).map φ)

/-- The identification `H (U x' U π K) ≅ H (U x̄ K) ≅ V x̄ H K`. -/
def homologyBaseChangeIsoAux :
    (H P).obj ((U x').obj ((U π).obj K)) ≅ (V xb).obj ((H X).obj K) :=
  (H P).mapIso ((cU x' π).symm.app K ≪≫ eqToIso (congrArg (fun s ↦ (U s).obj K) hxb)) ≪≫
    ((h xb).app K).symm

include assocU assocV hcomp hκ hτ in
/-- **The comparison of the Galois and model Frobenii**, for abstract families of pullback
functors: the homology of the model Frobenius is conjugate to the Galois Frobenius. -/
theorem homology_modelFrobenius_comp_eq_aux :
    (H P).map (modelFrobeniusAux U cU x' Φ π g F hfix hΦ κD K φ) ≫
        (homologyBaseChangeIsoAux U cU V H h x' π xb hxb K).hom =
      (homologyBaseChangeIsoAux U cU V H h x' π xb hxb K).hom ≫
        galoisFrobeniusAux U V cV H h g σ xb hgal τ K φ := by
  subst hxb
  have h₄ : x' ≫ π = (x' ≫ π) ≫ g ≫ F := by
    rw [Category.assoc, ← hΦ, ← Category.assoc, hfix]
  have h₁ : modelFrobeniusAux U cU x' Φ π g F hfix hΦ κD K φ ≫ (cU x' π).inv.app K =
      (cU x' π).inv.app K ≫ eqToHom (congrArg (fun s ↦ (U s).obj K) h₄) ≫
        (cU (x' ≫ π) (g ≫ F)).hom.app K ≫
          (U (x' ≫ π)).map ((cU g F).hom.app K ≫ (U g).map (κD.hom.app K) ≫ φ) := by
    simp only [modelFrobeniusAux, Functor.map_comp, Category.assoc]
    rw [map_map_comp_inv_app_aux U cU, map_map_comp_inv_app_aux_assoc U cU,
      map_map_comp_inv_app_aux_assoc U cU,
      map_hom_app_comp_inv_app_aux_assoc U cU _ _ _ _ (assocU _ _ _ _),
      map_eqToHom_comp_inv_app_aux_assoc U cU x' hΦ,
      map_inv_app_comp_inv_app_aux_assoc U cU _ _ _ _ (assocU _ _ _ _), Iso.hom_inv_id_app_assoc,
      eqToHom_comp_comp_inv_app_aux_assoc U cU hfix.symm]
    simp
  have h₂ : (h (g ≫ F)).hom.app K ≫ (H X).map
      ((cU g F).hom.app K ≫ (U g).map (κD.hom.app K) ≫ φ) =
        (cV g F).hom.app ((H X).obj K) ≫ (V g).map (κE.hom.app ((H X).obj K)) ≫
          (h g).hom.app K ≫ (H X).map φ := by
    rw [Functor.map_comp, reassoc_of% (hcomp g F K), Functor.map_comp,
      ← map_map_comp_hom_app_aux_assoc U V H h, ← Functor.map_comp_assoc, hκ]
    rfl
  have h₃ : (h (x' ≫ π)).hom.app K ≫ (H P).map
      (eqToHom (congrArg (fun s ↦ (U s).obj K) h₄) ≫ (cU (x' ≫ π) (g ≫ F)).hom.app K ≫
        (U (x' ≫ π)).map ((cU g F).hom.app K ≫ (U g).map (κD.hom.app K) ≫ φ)) =
      (eqToHom (congrArg (fun s ↦ (V s).obj ((H X).obj K)) h₄) ≫
        (cV (x' ≫ π) (g ≫ F)).hom.app ((H X).obj K) ≫
          (V (x' ≫ π)).map ((cV g F).hom.app ((H X).obj K) ≫
            (V g).map (κE.hom.app ((H X).obj K)) ≫ (h g).hom.app K ≫ (H X).map φ)) ≫
        (h (x' ≫ π)).hom.app K := by
    rw [Functor.map_comp, Functor.map_comp,
      hom_app_comp_map_eqToHom_aux_assoc U V H h h₄, reassoc_of% (hcomp _ _ K),
      ← map_map_comp_hom_app_aux U V H h, ← h₂]
    simp
  have h₅ : galoisFrobeniusAux U V cV H h g σ (x' ≫ π) hgal τ K φ =
      eqToHom (congrArg (fun s ↦ (V s).obj ((H X).obj K)) h₄) ≫
        (cV (x' ≫ π) (g ≫ F)).hom.app ((H X).obj K) ≫
          (V (x' ≫ π)).map ((cV g F).hom.app ((H X).obj K) ≫
            (V g).map (κE.hom.app ((H X).obj K)) ≫ (h g).hom.app K ≫ (H X).map φ) := by
    rw [galoisFrobeniusAux, reassoc_of% (hτ _), ← eqToHom_comp_map_aux_assoc V hgal.symm,
      ← eqToHom_comp_comp_hom_app_aux_assoc V cV hgal.symm, map_comp_hom_app_aux_assoc V cV,
      reassoc_of% (assocV _ _ _ _)]
    simp
  dsimp only [homologyBaseChangeIsoAux, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, eqToIso_refl, Iso.refl_hom]
  rw [h₅, Category.comp_id, ← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc]
  simp only [Category.assoc]
  congr 1
  rw [← cancel_epi ((h (x' ≫ π)).hom.app K), reassoc_of% h₃]
  simp

end AlgebraicGeometry.ProEtale.CondensedRing
