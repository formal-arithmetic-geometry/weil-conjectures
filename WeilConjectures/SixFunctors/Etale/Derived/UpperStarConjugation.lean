/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Restricting morphisms between pulled-back objects

For `w : W ⟶ X`, a morphism `δ : Lw^* K ⟶ Lw^* M` in `D(W_ét, Λ)` between the pullbacks of two
objects of `D(X_ét, Λ)` restricts along `t : T ⟶ W` to a morphism
`L(t ≫ w)^* K ⟶ L(t ≫ w)^* M` (`AlgebraicGeometry.Etale.restrictPullbackHom`), through the
composition isomorphisms of the derived pullbacks. Restrictions compose
(`AlgebraicGeometry.Etale.restrictPullbackHom_restrictPullbackHom`), by the associativity of the
composition isomorphisms.

Two tools to glue isomorphisms between invertible objects from local ones:

* *rigidity*: for a closed immersion `s : U ⟶ Y` such that every point of `Y` lies in a
  preconnected set meeting `s(U)`, two isomorphisms `K ≅ M` out of an invertible `K` agreeing
  after `Ls^*` are equal (`AlgebraicGeometry.Etale.iso_ext_of_leftDerivedUpperStar_map_eq`);
* *normalization*: for a section `s` of `p : Y ⟶ U` and `K ≅ Lp^* C`, any isomorphism
  `Ls^* K ≅ Ls^* M` is the restriction of an isomorphism `K ≅ M`, as soon as `K ≅ M`
  (`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_map_eq`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

section Restriction

variable {X : Scheme.{u}}
  {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

/-- The restriction along `t : T ⟶ W` of a morphism `δ : Lw^* K ⟶ Lw^* M`, a morphism
`Lx^* K ⟶ Lx^* M` for `x = t ≫ w`. -/
noncomputable def restrictPullbackHom {T W : Scheme.{u}} (t : T ⟶ W) (w : W ⟶ X) (x : T ⟶ X)
    (hx : x = t ≫ w)
    (δ : (L((w)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((w)^*[ModuleCat.{u + 1} Λ])).obj M) :
    (L((x)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((x)^*[ModuleCat.{u + 1} Λ])).obj M :=
  (leftDerivedUpperStarComp _ t w x hx).hom.app K ≫ (L((t)^*[ModuleCat.{u + 1} Λ])).map δ ≫
    (leftDerivedUpperStarComp _ t w x hx).inv.app M

/-- The restriction along `t : T ⟶ W` of an isomorphism `δ : Lw^* K ≅ Lw^* M`. -/
noncomputable def restrictPullbackIso {T W : Scheme.{u}} (t : T ⟶ W) (w : W ⟶ X) (x : T ⟶ X)
    (hx : x = t ≫ w)
    (δ : (L((w)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (L((w)^*[ModuleCat.{u + 1} Λ])).obj M) :
    (L((x)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (L((x)^*[ModuleCat.{u + 1} Λ])).obj M :=
  (leftDerivedUpperStarComp _ t w x hx).app K ≪≫ (L((t)^*[ModuleCat.{u + 1} Λ])).mapIso δ ≪≫
    ((leftDerivedUpperStarComp _ t w x hx).app M).symm

@[simp]
lemma restrictPullbackIso_hom {T W : Scheme.{u}} (t : T ⟶ W) (w : W ⟶ X) (x : T ⟶ X)
    (hx : x = t ≫ w)
    (δ : (L((w)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (L((w)^*[ModuleCat.{u + 1} Λ])).obj M) :
    (restrictPullbackIso t w x hx δ).hom = restrictPullbackHom t w x hx δ.hom :=
  rfl

lemma map_eq_of_restrictPullbackHom_eq {T W : Scheme.{u}} (t : T ⟶ W) (w : W ⟶ X) (x : T ⟶ X)
    (hx : x = t ≫ w)
    {δ δ' : (L((w)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((w)^*[ModuleCat.{u + 1} Λ])).obj M}
    (h : restrictPullbackHom t w x hx δ = restrictPullbackHom t w x hx δ') :
    (L((t)^*[ModuleCat.{u + 1} Λ])).map δ = (L((t)^*[ModuleCat.{u + 1} Λ])).map δ' := by
  simp only [restrictPullbackHom] at h
  rwa [cancel_epi, cancel_mono] at h

lemma restrictPullbackHom_comp {T W : Scheme.{u}} (t : T ⟶ W) (w : W ⟶ X) (x : T ⟶ X)
    (hx : x = t ≫ w) {N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))}
    (δ : (L((w)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((w)^*[ModuleCat.{u + 1} Λ])).obj M)
    (δ' : (L((w)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ (L((w)^*[ModuleCat.{u + 1} Λ])).obj N) :
    restrictPullbackHom t w x hx (δ ≫ δ') =
      restrictPullbackHom t w x hx δ ≫ restrictPullbackHom t w x hx δ' := by
  simp [restrictPullbackHom]

lemma restrictPullbackHom_id {T W : Scheme.{u}} (t : T ⟶ W) (w : W ⟶ X) (x : T ⟶ X)
    (hx : x = t ≫ w) :
    restrictPullbackHom (K := K) (M := K) t w x hx (𝟙 _) = 𝟙 _ := by
  simp [restrictPullbackHom]

/-- Restrictions of morphisms between pullbacks compose. -/
lemma restrictPullbackHom_restrictPullbackHom {T' T W : Scheme.{u}} (t' : T' ⟶ T) (t : T ⟶ W)
    (w : W ⟶ X) (tw : T ⟶ X) (htw : tw = t ≫ w) (t't : T' ⟶ W) (ht't : t't = t' ≫ t)
    (x : T' ⟶ X) (hx : x = t' ≫ tw)
    (δ : (L((w)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((w)^*[ModuleCat.{u + 1} Λ])).obj M) :
    restrictPullbackHom t' tw x hx (restrictPullbackHom t w tw htw δ) =
      restrictPullbackHom t't w x (by rw [hx, htw, ht't, Category.assoc]) δ := by
  have hfgh : x = t't ≫ w := by rw [hx, htw, ht't, Category.assoc]
  have a₁ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} Λ) t' t w t't tw x ht't htw
    hfgh K
  have a₂ := map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} Λ) t' t w t't tw x ht't htw hfgh M
  have n := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) t' t t't ht't).hom.naturality δ
  simp only [Functor.comp_map] at n
  simp only [restrictPullbackHom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% a₁, ← reassoc_of% n, a₂, Iso.hom_inv_id_app_assoc]

end Restriction

section Rigidity

variable {U Y : Scheme.{u}} (s : U ⟶ Y) [IsClosedImmersion s]
  (hs : ∀ y : Y, ∃ S : Set Y, _root_.IsPreconnected S ∧ y ∈ S ∧ (S ∩ Set.range s.base).Nonempty)

include hs in
/-- **Rigidity.** Two isomorphisms `K ≅ M` out of an invertible object `K` which agree after
`Ls^*`, for a closed immersion `s` meeting a preconnected set through every point, are equal. -/
lemma iso_ext_of_leftDerivedUpperStar_map_eq
    {K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.isInvertible Λ Y K) (δ δ' : K ≅ M)
    (h : (L((s)^*[ModuleCat.{u + 1} Λ])).map δ.hom =
      (L((s)^*[ModuleCat.{u + 1} Λ])).map δ'.hom) : δ = δ' := by
  have hγ : (L((s)^*[ModuleCat.{u + 1} Λ])).map (δ.hom ≫ δ'.inv) = 𝟙 _ := by
    rw [Functor.map_comp, h, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible s hs hK _ hγ
  exact Iso.ext (by rw [← Category.comp_id δ.hom, ← δ'.inv_hom_id, ← Category.assoc, this,
    Category.id_comp])

end Rigidity

section Normalization

variable {U Y : Scheme.{u}} (p : Y ⟶ U) (s : U ⟶ Y) (hsp : s ≫ p = 𝟙 U)
include hsp

/-- **Normalization along a section.** Let `s` be a section of `p : Y ⟶ U` and let `K` be a
pullback, `K ≅ Lp^* C`. If `K ≅ M`, then every isomorphism `b : Ls^* K ≅ Ls^* M` is the
restriction of an isomorphism `δ : K ≅ M`: an automorphism of `Ls^* K ≅ C` lifts to the
automorphism of `K ≅ Lp^* C` it induces through `Ls^* Lp^* ≅ 𝟭`. -/
lemma exists_iso_leftDerivedUpperStar_map_eq
    {K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {C : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ≅ (L((p)^*[ModuleCat.{u + 1} Λ])).obj C) (δ₀ : K ≅ M)
    (b : (L((s)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (L((s)^*[ModuleCat.{u + 1} Λ])).obj M) :
    ∃ δ : K ≅ M, (L((s)^*[ModuleCat.{u + 1} Λ])).map δ.hom = b.hom := by
  let σ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) s p hsp
  let ψ : (L((s)^*[ModuleCat.{u + 1} Λ])).obj K ≅ C :=
    (L((s)^*[ModuleCat.{u + 1} Λ])).mapIso φ ≪≫ σ.app C
  let v : (L((s)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (L((s)^*[ModuleCat.{u + 1} Λ])).obj K :=
    b ≪≫ ((L((s)^*[ModuleCat.{u + 1} Λ])).mapIso δ₀).symm
  let c : C ≅ C := ψ.symm ≪≫ v ≪≫ ψ
  let w : K ≅ K := φ ≪≫ (L((p)^*[ModuleCat.{u + 1} Λ])).mapIso c ≪≫ φ.symm
  refine ⟨w ≪≫ δ₀, ?_⟩
  have hn : (L((s)^*[ModuleCat.{u + 1} Λ])).map ((L((p)^*[ModuleCat.{u + 1} Λ])).map c.hom) =
      σ.hom.app C ≫ c.hom ≫ σ.inv.app C := by
    have := σ.hom.naturality c.hom
    simp only [Functor.comp_map, Functor.id_map] at this
    rw [← reassoc_of% this, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hw : (L((s)^*[ModuleCat.{u + 1} Λ])).map w.hom = v.hom := by
    simp only [w, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, hn]
    simp [c, ψ]
  simp only [Iso.trans_hom, Functor.map_comp, hw]
  simp [v]

end Normalization

end Etale

end AlgebraicGeometry
