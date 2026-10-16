/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationCouple
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusTruncationIso

/-!
# Finiteness and abutment of the truncation exact couple

Let `F : D⁺(C) ⥤ D⁺(D)` be a triangulated functor which does not lower the cohomological degree
(e.g. a right derived functor, or the composite of a right derived functor with an exact
functor), and `K ∈ D⁺(C)` with `H^q(K) = 0` for `q < a`. For the truncation exact couple
`DerivedCategory.Plus.truncationCouple F K`:

* `D^{p,q} = 0` and `E^{p,q} = 0` for `q < a`, and `E^{p,q} = 0` for `p < 0`
  (`DerivedCategory.Plus.isZero_truncationCouple_D_of_lt`,
  `DerivedCategory.Plus.isZero_truncationCouple_E_of_lt`,
  `DerivedCategory.Plus.isZero_truncationCouple_E_of_neg`): in total degree `n` only the
  finitely many `E^{p,q}` with `a ≤ q ≤ n` are nonzero;
* the abutment map `D^{p,q} = H^{p+q}(F(τ_{≤ q} K)) ⟶ H^{p+q}(F K)` is an isomorphism for
  `p ≤ 0` (`DerivedCategory.Plus.isIso_truncationCoupleAbutmentMap`), the images of these maps
  form the filtration of the abutment (`DerivedCategory.Plus.truncationCoupleFiltration`);
* a natural transformation `τ : F₁ ⟶ F₂` commuting with the shifts induces on abutments the
  map `H^n(τ_K)` (`DerivedCategory.Plus.truncationCoupleMap_hD_comp_abutmentMap`), which
  respects the filtrations (`DerivedCategory.Plus.imageSubobject_truncationCoupleFiltration_le`).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory.Plus

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]

lemma isZero_truncLE_obj_of_isGE (K : Plus C) (a q : ℤ) [K.IsGE a] (hq : q < a) :
    IsZero ((truncLE C q).obj K) := by
  have : (ι.obj K).IsGE a := inferInstance
  have : ((DerivedCategory.truncLE C q).obj (ι.obj K)).IsGE a :=
    DerivedCategory.isGE_truncLE_obj _ a q
  have h : IsZero (ι.obj ((truncLE C q).obj K)) :=
    DerivedCategory.TStructure.t.isZero ((DerivedCategory.truncLE C q).obj (ι.obj K)) q a hq
  exact (IsZero.iff_id_eq_zero _).2 (ι.map_injective (h.eq_of_src _ _))

section

variable (F : Plus C ⥤ Plus D) [F.CommShift ℤ] [F.IsTriangulated] (K : Plus C)

lemma isZero_truncationCouple_D_of_lt (a : ℤ) [K.IsGE a] (p q : ℤ) (hq : q < a) :
    IsZero ((truncationCouple F K).D p q) :=
  Functor.map_isZero _
    (Functor.map_isZero _ (F.map_isZero (isZero_truncLE_obj_of_isGE K a q hq)))

lemma isZero_truncationCouple_E_of_lt (a : ℤ) [K.IsGE a] (p q : ℤ) (hq : q < a) :
    IsZero ((truncationCouple F K).E p q) :=
  Functor.map_isZero _ (Functor.map_isZero _ (F.map_isZero
    (Functor.map_isZero (singleFunctor C q) (isZero_homology_of_isGE K a q hq))))

/-- If `F` does not lower the cohomological degree, then `E^{p,q} = H^p(F(H^q(K))) = 0` for
`p < 0`. -/
lemma isZero_truncationCouple_E_of_neg
    (hF : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
      IsZero ((homologyFunctor D q).obj (F.obj X)))
    (p q : ℤ) (hp : p < 0) :
    IsZero ((truncationCouple F K).E p q) :=
  (hF ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)) 0 p hp).of_iso
    (truncationCoupleEIso F K p q)

/-- The abutment map `D^{p,q} = H^{p+q}(F(τ_{≤ q} K)) ⟶ H^{p+q}(F K)`, induced by the
inclusion `τ_{≤ q} K ⟶ K`. -/
noncomputable def truncationCoupleAbutmentMap (p q : ℤ) :
    (truncationCouple F K).D p q ⟶ ((homologyFunctor D 0).shift (p + q)).obj (F.obj K) :=
  ((homologyFunctor D 0).shift (p + q)).map (F.map ((truncLEι C q).app K))

/-- If `F` does not lower the cohomological degree, the abutment map
`D^{p,q} = H^{p+q}(F(τ_{≤ q} K)) ⟶ H^{p+q}(F K)` is an isomorphism for `p ≤ 0`: the terms
`D^{n-q,q}` with `q ≥ n` are all identified with the abutment `H^n(F K)`. -/
lemma isIso_truncationCoupleAbutmentMap
    (hF : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
      IsZero ((homologyFunctor D q).obj (F.obj X)))
    (p q : ℤ) (hp : p ≤ 0) :
    IsIso (truncationCoupleAbutmentMap F K p q) :=
  isIso_homologyFunctor_map_map_truncLEι_app F hF K q (p + q) (by lia)

/-- The filtration of the abutment `H^n(F K)` by the images of
`H^n(F(τ_{≤ q} K)) ⟶ H^n(F K)`. -/
noncomputable def truncationCoupleFiltration (n q : ℤ) :
    Subobject (((homologyFunctor D 0).shift n).obj (F.obj K)) :=
  imageSubobject (((homologyFunctor D 0).shift n).map (F.map ((truncLEι C q).app K)))

omit [F.CommShift ℤ] [F.IsTriangulated] in
lemma truncationCoupleFiltration_mono (n q q' : ℤ) (h : q ≤ q') :
    truncationCoupleFiltration F K n q ≤ truncationCoupleFiltration F K n q' := by
  have : (truncLEι C q).app K = (truncLEMapOfLE C q q' h).app K ≫ (truncLEι C q').app K := by
    apply ι.map_injective
    simp only [Functor.map_comp, ι_map_truncLEι_app, ι_map_truncLEMapOfLE_app]
    exact NatTrans.congr_app (DerivedCategory.truncLEMapOfLE_comp_truncLEι C q q' h).symm _
  simp only [truncationCoupleFiltration, this, Functor.map_comp]
  exact imageSubobject_comp_le _ _

end

section

variable {F₁ F₂ : Plus C ⥤ Plus D} [F₁.CommShift ℤ] [F₁.IsTriangulated] [F₂.CommShift ℤ]
  [F₂.IsTriangulated] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (K : Plus C)

/-- The morphism of truncation couples induced by `τ` is compatible with the abutment maps,
the map on abutments being `H^{p+q}(τ_K)`. -/
@[reassoc]
lemma truncationCoupleMap_hD_comp_abutmentMap (p q : ℤ) :
    (truncationCoupleMap τ K).hD p q ≫ truncationCoupleAbutmentMap F₂ K p q =
      truncationCoupleAbutmentMap F₁ K p q ≫
        ((homologyFunctor D 0).shift (p + q)).map (τ.app K) := by
  simp only [truncationCoupleMap_hD, truncationCoupleAbutmentMap, ← Functor.map_comp,
    τ.naturality]
  rfl

omit [F₁.CommShift ℤ] [F₁.IsTriangulated] [F₂.CommShift ℤ] [F₂.IsTriangulated]
  [NatTrans.CommShift τ ℤ] in
/-- The map `H^n(τ_K)` on abutments sends the `q`-th step of the filtration of `H^n(F₁ K)` into
the `q`-th step of the filtration of `H^n(F₂ K)`. -/
lemma imageSubobject_truncationCoupleFiltration_le (n q : ℤ) :
    imageSubobject (((homologyFunctor D 0).shift n).map (F₁.map ((truncLEι C q).app K)) ≫
      ((homologyFunctor D 0).shift n).map (τ.app K)) ≤ truncationCoupleFiltration F₂ K n q := by
  have e : ((homologyFunctor D 0).shift n).map (F₁.map ((truncLEι C q).app K)) ≫
      ((homologyFunctor D 0).shift n).map (τ.app K) =
      ((homologyFunctor D 0).shift n).map (τ.app ((truncLE C q).obj K)) ≫
        ((homologyFunctor D 0).shift n).map (F₂.map ((truncLEι C q).app K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact τ.naturality _
  rw [e]
  exact imageSubobject_comp_le _ _

end

end DerivedCategory.Plus
