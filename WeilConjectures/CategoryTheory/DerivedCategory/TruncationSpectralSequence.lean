/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationCoupleAbutment
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.Convergence
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.DifferentialSubobjects

/-!
# The truncation hypercohomology spectral sequence

Let `F : D⁺(C) ⥤ D⁺(D)` be a triangulated functor which does not lower the cohomological degree
and `K ∈ D⁺(C)` with `H^q(K) = 0` for `q < a`. The truncation couple
`DerivedCategory.Plus.truncationCouple F K` (`D^{p,q} = H^{p+q}(F τ_{≤ q} K)`,
`E^{p,q} = H^{p+q}(F (H^q(K)[-q]))`) is a half-plane exact couple
(`DerivedCategory.Plus.isHalfPlane_truncationCouple`), its abutment `D^{0,n}` is identified
with `H^n(F K)` (`DerivedCategory.Plus.truncationCoupleAbutmentIso`), and under this
identification the filtration of the abutment of `thm-sp-half-plane-convergence` is the image
filtration of the maps `H^n(F τ_{≤ q} K) ⟶ H^n(F K)`
(`DerivedCategory.Plus.imageSubobject_abutmentFiltration_truncationCouple`).

For the right derived functor `F = R⁺v` of an additive functor `v : C ⥤ D` (`C` with enough
injectives), the `E`-terms are `E₂^{p,q} ≅ R^p v (H^q(K))`
(`DerivedCategory.Plus.rightDerivedTruncationCoupleE₂Iso`, the shift identification
`lem-sp-shift-identification`), and the spectral sequence
`E₂^{p,q} = R^p v (H^q(K)) ⇒ H^{p+q}(R⁺v K)` converges (`thm-sp-truncation-e2`,
`DerivedCategory.Plus.rightDerivedTruncationCouple_e₂`).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory.Plus

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]

/-- Blueprint `lem-sp-derived-cohomology-shift`: the cohomology of a shifted object of `D⁺`,
`H^a(M⟦k⟧) ≅ H^{a'}(M)` for `k + a = a'`, natural in `M`; this is the shift sequence of the
cohomology functors (`CategoryTheory.Functor.shiftIso`). -/
noncomputable def homologyFunctorShiftIso (k a a' : ℤ) (h : k + a = a') :
    shiftFunctor (Plus D) k ⋙ (homologyFunctor D 0).shift a ≅ (homologyFunctor D 0).shift a' :=
  (homologyFunctor D 0).shiftIso k a a' h

section General

variable (F : Plus C ⥤ Plus D) [F.CommShift ℤ] [F.IsTriangulated] (K : Plus C)

lemma truncLEι_app_eq (q q' : ℤ) (h : q ≤ q') :
    (truncLEι C q).app K = (truncLEMapOfLE C q q' h).app K ≫ (truncLEι C q').app K := by
  apply ι.map_injective
  simp only [Functor.map_comp, ι_map_truncLEι_app, ι_map_truncLEMapOfLE_app]
  exact NatTrans.congr_app (DerivedCategory.truncLEMapOfLE_comp_truncLEι C q q' h).symm _

/-- The map `α` of the truncation couple is compatible with the abutment maps. -/
@[reassoc]
lemma truncationCouple_α_abutmentMap (p q p' q' : ℤ) (hp : p' + 1 = p) (hq : q + 1 = q') :
    (truncationCouple F K).α p q p' q' hp hq ≫ truncationCoupleAbutmentMap F K p' q' =
      truncationCoupleAbutmentMap F K p q ≫ eqToHom (by rw [show p + q = p' + q' by lia]) := by
  have e : (K.truncLETower.map F).i q q' (by lia) ≫ F.map ((truncLEι C q').app K) =
      F.map ((truncLEι C q).app K) := by
    change F.map ((truncLEMapOfLE C q q' (by lia)).app K) ≫ F.map ((truncLEι C q').app K) = _
    rw [← F.map_comp, ← truncLEι_app_eq]
  dsimp only [truncationCouple, TriangleTower.exactCouple, truncationCoupleAbutmentMap]
  rw [assoc, eqToHom_comp_map_of_eq (homologyFunctor D 0).shift (show p + q = p' + q' by lia)
      (F.map ((truncLEι C q').app K)) _ (by rw [show p + q = p' + q' by lia]),
    ← Functor.map_comp_assoc, e]

/-- The iterates `αᵏ` of the truncation couple are compatible with the abutment maps. -/
@[reassoc]
lemma truncationCouple_αPow_abutmentMap (k : ℕ) (a b p q : ℤ) (ha : p + k = a)
    (hb : b + k = q) :
    (truncationCouple F K).αPow k a b p q ha hb ≫ truncationCoupleAbutmentMap F K p q =
      truncationCoupleAbutmentMap F K a b ≫ eqToHom (by rw [show a + b = p + q by lia]) := by
  induction k generalizing a b with
  | zero =>
    obtain rfl : a = p := by lia
    obtain rfl : b = q := by lia
    simp
  | succ k ih =>
    rw [ExactCouple.αPow_succ, assoc, ih (a - 1) (b + 1) (by lia) (by lia),
      truncationCouple_α_abutmentMap_assoc, eqToHom_trans]

variable (hF : ∀ (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
  IsZero ((homologyFunctor D q).obj (F.obj X)))

include hF in
/-- If `F` does not lower the cohomological degree and `H^q(K) = 0` for `q < a`, the truncation
couple satisfies the hypotheses of `thm-sp-half-plane-convergence`. -/
lemma isHalfPlane_truncationCouple (a : ℤ) [K.IsGE a] :
    (truncationCouple F K).IsHalfPlane a where
  isZero_D p q hq := isZero_truncationCouple_D_of_lt F K a p q hq
  isZero_E p q h := h.elim (isZero_truncationCouple_E_of_neg F K hF p q)
    (isZero_truncationCouple_E_of_lt F K a p q)

/-- The identification of the abutment `D^{0,n} = H^n(F τ_{≤ n} K) ≅ H^n(F K)` of the
truncation couple, induced by `τ_{≤ n} K ⟶ K`. -/
noncomputable def truncationCoupleAbutmentIso (n : ℤ) :
    (truncationCouple F K).D 0 n ≅ ((homologyFunctor D 0).shift n).obj (F.obj K) :=
  have := isIso_truncationCoupleAbutmentMap F K hF 0 n le_rfl
  asIso (truncationCoupleAbutmentMap F K 0 n) ≪≫ eqToIso (by rw [zero_add])

lemma truncationCoupleAbutmentIso_hom (n : ℤ) :
    (truncationCoupleAbutmentIso F K hF n).hom =
      truncationCoupleAbutmentMap F K 0 n ≫ eqToHom (by rw [zero_add]) :=
  rfl

omit [HasDerivedCategory C] [HasDerivedCategory D] in
lemma _root_.CategoryTheory.imageSubobject_imageSubobject_arrow_comp {X Y Z : D} (u : X ⟶ Y)
    (g : Y ⟶ Z) : imageSubobject ((imageSubobject u).arrow ≫ g) = imageSubobject (u ≫ g) := by
  rw [← ExactCouple.imageSubobject_epi_comp (factorThruImageSubobject u)
    ((imageSubobject u).arrow ≫ g), imageSubobject_arrow_comp_assoc]

/-- Under the identification `D^{0,n} ≅ H^n(F K)`, the filtration `Fᵖ` (`p ≥ 0`) of the
abutment of the truncation couple (`CategoryTheory.ExactCouple.abutmentFiltration`) is the
image of `H^n(F τ_{≤ n-p} K) ⟶ H^n(F K)`. -/
lemma imageSubobject_abutmentFiltration_truncationCouple (n p : ℤ) (hp : 0 ≤ p) :
    imageSubobject ((((truncationCouple F K).abutmentFiltration n).F p).arrow ≫
      (truncationCoupleAbutmentIso F K hF n).hom) = truncationCoupleFiltration F K n (n - p) := by
  rw [ExactCouple.abutmentFiltration_F_of_nonneg _ n p hp p.toNat (by lia),
    imageSubobject_imageSubobject_arrow_comp, truncationCoupleAbutmentIso_hom,
    truncationCouple_αPow_abutmentMap_assoc, eqToHom_trans, truncationCoupleAbutmentMap,
    ← eqToHom_comp_map_of_eq (homologyFunctor D 0).shift (show p + (n - p) = n by lia)
      (F.map ((truncLEι C (n - p)).app K)) (by rw [show p + (n - p) = n by lia]),
    imageSubobject_iso_comp]
  rfl

end General

section RightDerived

variable [EnoughInjectives C] (v : C ⥤ D) [v.Additive] (K : Plus C)

/-- `R⁺v` does not lower the cohomological degree. -/
lemma isZero_homologyFunctor_rightDerivedFunctorPlus (X : Plus C) (n : ℤ) [X.IsGE n] (q : ℤ)
    (hq : q < n) : IsZero ((homologyFunctor D q).obj (v.rightDerivedFunctorPlus.obj X)) :=
  v.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE X n hq

/-- Blueprint `lem-sp-truncation-couple-exact`: the truncation couple of `K` for a right derived
functor `R⁺v`, with `D^{p,q} = H^{p+q}(R⁺v τ_{≤ q} K)` and `E^{p,q} = H^{p+q}(R⁺v (H^q(K)[-q]))`,
is an exact couple: the three sequences `E ⟶ D ⟶ D`, `D ⟶ E ⟶ D`, `D ⟶ D ⟶ E` are exact,
being pieces of the long exact cohomology sequences of the images under `R⁺v` of the
truncation triangles. -/
lemma rightDerivedTruncationCouple_exact (p q : ℤ) :
    (ShortComplex.mk _ _ ((truncationCouple v.rightDerivedFunctorPlus K).f_α
      (p - 2) (q + 1) p q (p - 1) (q + 1))).Exact ∧
    (ShortComplex.mk _ _ ((truncationCouple v.rightDerivedFunctorPlus K).g_f
      p q p q (p + 2) (q - 1))).Exact ∧
    (ShortComplex.mk _ _ ((truncationCouple v.rightDerivedFunctorPlus K).α_g
      (p + 1) (q - 1) p q p q)).Exact :=
  ⟨(truncationCouple _ K).exact_f_α _ _ _ _ _ _, (truncationCouple _ K).exact_g_f _ _ _ _ _ _,
    (truncationCouple _ K).exact_α_g _ _ _ _ _ _⟩

/-- Blueprint `lem-sp-shift-identification`: for `M ∈ C`, `p : ℕ` and `q : ℤ`,
`H^{p+q}(R⁺v (M[-q])) ≅ H^p(R⁺v M) ≅ R^p v (M)`: the derived functor commutes with the shift
and the cohomology of a shifted object is the shifted cohomology
(`lem-sp-derived-cohomology-shift`), and on an object placed in degree `0` the derived functor
computes the classical right derived functors (`lem-sp-derived-functor-single-identification`,
`CategoryTheory.Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`). -/
noncomputable def rightDerivedShiftIdentification (M : C) (p : ℕ) (q : ℤ) :
    ((homologyFunctor D 0).shift ((p : ℤ) + q)).obj
        (v.rightDerivedFunctorPlus.obj ((singleFunctor C q).obj M)) ≅
      (v.rightDerived p).obj M :=
  ((homologyFunctor D 0).shift ((p : ℤ) + q)).mapIso
      (v.rightDerivedFunctorPlus.mapIso
        (((singleFunctors C).shiftIso (-q) q 0 (by lia)).symm.app M)) ≪≫
    ((homologyFunctor D 0).shift ((p : ℤ) + q)).mapIso
      ((v.rightDerivedFunctorPlus.commShiftIso (-q)).app _) ≪≫
    ((homologyFunctor D 0).shiftIso (-q) ((p : ℤ) + q) p (by lia)).app _ ≪≫
    v.homologyRightDerivedFunctorPlusObjSingleFunctorIso M p

/-- The `E₂`-term of the truncation spectral sequence of `R⁺v`:
`E₂^{p,q} = H^{p+q}(R⁺v (H^q(K)[-q])) ≅ R^p v (H^q(K))` (`thm-sp-truncation-e2`, via the shift
identification `lem-sp-shift-identification`). -/
noncomputable def rightDerivedTruncationCoupleE₂Iso (p : ℕ) (q : ℤ) :
    (truncationCouple v.rightDerivedFunctorPlus K).E p q ≅
      (v.rightDerived p).obj ((homologyFunctor C q).obj K) :=
  truncationCoupleEIso _ K p q ≪≫ v.homologyRightDerivedFunctorPlusObjSingleFunctorIso _ p

/-- Blueprint `thm-sp-truncation-e2`: let `v : C ⥤ D` be additive, `C` with enough injectives,
and `K ∈ D⁺(C)` with `H^q(K) = 0` for `q < a`. The spectral sequence of the truncation couple
`X = DerivedCategory.Plus.truncationCouple (R⁺v) K` (an exact couple,
`lem-sp-truncation-couple-exact`) has `E₂^{p,q} ≅ R^p v (H^q(K))`
(`DerivedCategory.Plus.rightDerivedTruncationCoupleE₂Iso`) and converges to
`H^{p+q}(R⁺v K)`:
* `X` satisfies the hypotheses of `thm-sp-half-plane-convergence` for `a`: only `p ≥ 0`,
  `a ≤ q` occur, so in total degree `n` only `a ≤ q ≤ n`;
* the abutment `D^{0,n}` is `H^n(R⁺v K)` (`DerivedCategory.Plus.truncationCoupleAbutmentIso`),
  and the finite filtration of `thm-sp-half-plane-convergence` corresponds to the image
  filtration of the maps `H^n(R⁺v τ_{≤ q} K) ⟶ H^n(R⁺v K)`;
* hence `E_∞^{p,q} ≅ grᵖ H^{p+q}(R⁺v K)` (`CategoryTheory.ExactCouple.IsHalfPlane.grIsoEInfty`),
  the pages being stable at `(p, q)` from `r > max (q - a + 1) p` on
  (`CategoryTheory.ExactCouple.IsHalfPlane.iterEIsoEInfty`). -/
theorem rightDerivedTruncationCouple_e₂ (a : ℤ) [K.IsGE a] :
    (truncationCouple v.rightDerivedFunctorPlus K).IsHalfPlane a ∧
    (∀ n, ((truncationCouple v.rightDerivedFunctorPlus K).abutmentFiltration n).IsFinite) ∧
    (∀ n p, 0 ≤ p → imageSubobject
      ((((truncationCouple v.rightDerivedFunctorPlus K).abutmentFiltration n).F p).arrow ≫
        (truncationCoupleAbutmentIso _ K (isZero_homologyFunctor_rightDerivedFunctorPlus v)
          n).hom) = truncationCoupleFiltration _ K n (n - p)) ∧
    (∀ p q n, p + q = n → 0 ≤ p →
      Nonempty (((truncationCouple v.rightDerivedFunctorPlus K).abutmentFiltration n).gr p ≅
        (truncationCouple v.rightDerivedFunctorPlus K).EInfty a p q)) := by
  have h := isHalfPlane_truncationCouple _ K (isZero_homologyFunctor_rightDerivedFunctorPlus v) a
  exact ⟨h, h.abutmentFiltration_isFinite,
    fun n p hp ↦ imageSubobject_abutmentFiltration_truncationCouple _ K _ n p hp,
    fun p q n hn hp ↦ ⟨h.grIsoEInfty p q n hn hp⟩⟩

end RightDerived

end DerivedCategory.Plus
