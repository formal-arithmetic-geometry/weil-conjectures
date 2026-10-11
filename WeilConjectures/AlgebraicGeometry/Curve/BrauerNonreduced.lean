/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AffineAcyclic
public import WeilConjectures.AlgebraicGeometry.Curve.BrauerReduced
public import WeilConjectures.AlgebraicGeometry.Sites.SquareZero
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The Brauer group of an arbitrary curve

The Brauer group `H²(C_ét, 𝔾ₘ)` of every curve `C` over an algebraically closed field vanishes;
`C` may be non-reduced. Let `𝒩` be the nilradical of `C`, with `𝒩ᵐ = 0`, and `Cⱼ ⊆ C` the closed
subscheme cut out by `𝒩ʲ`. Then `C₁ = C_red` has trivial Brauer group
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_isReduced`), and `Cⱼ ⊆ Cⱼ₊₁`
is a square-zero thickening, whose ideal sheaf `K` has no `H²` since it is acyclic on affine
étale schemes (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_forall_isAffine`). The
exact sequence `0 → K → 𝔾ₘ → (Cⱼ → Cⱼ₊₁)_* 𝔾ₘ → 0`, with `K → 𝔾ₘ` given by `a ↦ 1 + a`
(`AlgebraicGeometry.Scheme.subsingleton_H_two_gmSheaf_of_squareZero`), then shows that
`Br(Cⱼ₊₁) = 0` if `Br(Cⱼ) = 0`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_nilradical_pow_eq_bot`: the nilradical of a quasi-compact
  locally noetherian scheme is nilpotent.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup`: the Brauer group of a curve
  over an algebraically closed field vanishes.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two`:
  `H²(C, μₙ) ≅ Pic(C)/n·Pic(C)` for every curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **The nilradical of a quasi-compact locally noetherian scheme is nilpotent**: every local
ring is a localization of a noetherian ring of sections over one of finitely many affine opens,
whose nilradical is nilpotent. -/
theorem Scheme.exists_nilradical_pow_eq_bot (X : Scheme.{u}) [CompactSpace X]
    [IsLocallyNoetherian X] : ∃ m : ℕ, X.nilradical ^ m = ⊥ := by
  have key (x : X) : ∃ (V : X.Opens) (N : ℕ), x ∈ V ∧
      ∀ y ∈ V, _root_.nilradical (X.presheaf.stalk y) ^ N = ⊥ := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨N, hN⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(X, V)
    refine ⟨V, N, hxV, fun y hy ↦ ?_⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)
    have := hV.isLocalization_stalk ⟨y, hy⟩
    exact nilradical_pow_eq_bot_of_isLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl hN
  choose V N hxV hN using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  refine ⟨t.sup N, Scheme.IdealSheafData.ext (funext fun U ↦ le_antisymm (fun a ha ↦ ?_) bot_le)⟩
  change a ∈ (_root_.nilradical Γ(X, U)) ^ t.sup N at ha
  change a ∈ (⊥ : Ideal Γ(X, U))
  refine Ideal.mem_bot.2 (TopCat.Presheaf.section_ext X.sheaf U _ _ fun y hy ↦ ?_)
  rw [map_zero]
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ V x := by simpa using ht (Set.mem_univ y)
  have hle : (_root_.nilradical Γ(X, U) ^ t.sup N).map (X.presheaf.germ U y hy).hom ≤ ⊥ := by
    rw [Ideal.map_pow]
    refine (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun b hb ↦ ?_) _).trans ?_
    · exact mem_nilradical.2 ((mem_nilradical.1 hb).map _)
    · exact (Ideal.pow_le_pow_right (Finset.le_sup hxt)).trans (hN x y hyx).le
  exact Ideal.mem_bot.1 (hle (Ideal.mem_map_of_mem _ ha))

/-- **Square-zero thickenings inside a scheme.** Let `ιY : Y ⟶ X` be a closed immersion whose
ideal contains `J`, and `I` an ideal sheaf on `X` with `I * I ≤ J` and `I.subscheme ⊆ Y`, via
`h : I.subscheme ⟶ Y`. Then the ideal of `h` is of square zero: for every `g : T ⟶ Y`, two
functions on `T` vanishing on `T ×_Y I.subscheme` have product zero. -/
lemma Scheme.mul_eq_zero_of_appTop_pullback_fst_eq_zero {X Y T : Scheme.{u}} (ιY : Y ⟶ X)
    [IsClosedImmersion ιY] (I J : X.IdealSheafData) (hJ : J ≤ ιY.ker) (hIJ : I * I ≤ J)
    (h : I.subscheme ⟶ Y) (hh : h ≫ ιY = I.subschemeι) (g : T ⟶ Y) (a b : Γ(T, ⊤))
    (ha : (pullback.fst g h).appTop a = 0) (hb : (pullback.fst g h).appTop b = 0) :
    a * b = 0 := by
  have : IsClosedImmersion (h ≫ ιY) := by rw [hh]; infer_instance
  have : IsClosedImmersion h := IsClosedImmersion.of_comp h ιY
  -- the ideal of `h` is of square zero over the preimages of the affine opens of `X`
  have hsq (U : X.affineOpens) (c d : Γ(Y, ιY ⁻¹ᵁ U.1))
      (hc : c ∈ h.ker.ideal ⟨ιY ⁻¹ᵁ U.1, U.2.preimage ιY⟩)
      (hd : d ∈ h.ker.ideal ⟨ιY ⁻¹ᵁ U.1, U.2.preimage ιY⟩) : c * d = 0 := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hc hd
    obtain ⟨c', rfl⟩ := ιY.app_surjective U.1 U.2 c
    obtain ⟨d', rfl⟩ := ιY.app_surjective U.1 U.2 d
    have hI (e : Γ(X, U.1)) (he : h.app (ιY ⁻¹ᵁ U.1) (ιY.app U.1 e) = 0) : e ∈ I.ideal U := by
      rw [← IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, ← hh, Scheme.Hom.comp_app,
        CommRingCat.comp_apply]
      exact he
    have hJ' := hJ U (hIJ U (Ideal.mul_mem_mul (hI c' hc) (hI d' hd)))
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hJ'
    rw [← map_mul]
    exact hJ'
  refine TopCat.Presheaf.section_ext T.sheaf ⊤ _ _ fun t _ ↦ ?_
  rw [map_zero]
  obtain ⟨U, hU, hgt, -⟩ := exists_isAffineOpen_mem_and_subset (x := ιY (g t)) (U := ⊤) trivial
  have hU' : IsAffineOpen (ιY ⁻¹ᵁ U) := hU.preimage ιY
  obtain ⟨V, hV, htV, hVle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := t) (U := g ⁻¹ᵁ (ιY ⁻¹ᵁ U)) hgt
  have hmem (c : Γ(T, ⊤)) (hc : (pullback.fst g h).appTop c = 0) :
      T.presheaf.map (homOfLE le_top).op c ∈
        (h.ker.ideal ⟨ιY ⁻¹ᵁ U, hU'⟩).map (g.appLE (ιY ⁻¹ᵁ U) V hVle).hom := by
    rw [← IdealSheafData.ideal_comap_appLE h.ker g ⟨ιY ⁻¹ᵁ U, hU'⟩ ⟨V, hV⟩ hVle,
      ← IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.Hom.ker_apply, RingHom.mem_ker,
      ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
    erw [hc, map_zero]
  have hK : h.ker.ideal ⟨ιY ⁻¹ᵁ U, hU'⟩ * h.ker.ideal ⟨ιY ⁻¹ᵁ U, hU'⟩ = ⊥ :=
    eq_bot_iff.2 (Ideal.mul_le.2 fun c hc d hd ↦ Ideal.mem_bot.2 (hsq ⟨U, hU⟩ c d hc hd))
  have hprod := Ideal.mul_mem_mul (hmem a ha) (hmem b hb)
  rw [← Ideal.map_mul, hK, Ideal.map_bot, ← map_mul] at hprod
  rw [← T.presheaf.germ_res_apply (homOfLE le_top) t htV, Ideal.mem_bot.1 hprod, map_zero]

namespace IsCurve

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- A closed subscheme of a curve is a curve. -/
lemma comp_isClosedImmersion (f : C ⟶ Spec (.of k)) [IsCurve f] {Y : Scheme.{u}} (i : Y ⟶ C)
    [IsClosedImmersion i] : IsCurve (i ≫ f) where
  krullDim_le_one :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans (IsCurve.krullDim_le_one (f := f))

variable [IsAlgClosed k]

/-- The ideal sheaf `K` of a closed subscheme of a curve, the kernel of `𝔾ₐ ⟶ h_* 𝔾ₐ`, has no
`H²`: it is acyclic on affine étale schemes
(`AlgebraicGeometry.Scheme.subsingleton_H_upperStar_gaKernel`). -/
theorem subsingleton_H_two_gaKernel {Y Z : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsCurve f]
    (h : Z ⟶ Y) [IsClosedImmersion h] : Subsingleton (Sheaf.H (Scheme.gaKernel h) 2) :=
  subsingleton_sheafH_two_of_forall_isAffine f _ fun W w hw hW q ↦ by
    have := hw
    have := hW
    exact Scheme.subsingleton_H_upperStar_gaKernel h w q

/-- **Brauer groups along square-zero thickenings.** Let `Y` be a curve over an algebraically
closed field, embedded in `X` by a closed immersion whose ideal contains `J`, and let `I` be an
ideal sheaf on `X` with `I * I ≤ J` whose subscheme lies in `Y`. If the Brauer group of
`I.subscheme` vanishes, so does the Brauer group of `Y`. -/
theorem subsingleton_cohomologicalBrauerGroup_of_squareZero {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsCurve f] (ιY : Y ⟶ X) [IsClosedImmersion ιY]
    (I J : X.IdealSheafData) (hJ : J ≤ ιY.ker) (hIJ : I * I ≤ J) (h : I.subscheme ⟶ Y)
    (hh : h ≫ ιY = I.subschemeι) (hZ : Subsingleton I.subscheme.CohomologicalBrauerGroup) :
    Subsingleton Y.CohomologicalBrauerGroup := by
  have : IsClosedImmersion (h ≫ ιY) := by rw [hh]; infer_instance
  have : IsClosedImmersion h := IsClosedImmersion.of_comp h ιY
  exact Scheme.subsingleton_H_two_gmSheaf_of_squareZero
    (fun T a b ha hb ↦
      Scheme.mul_eq_zero_of_appTop_pullback_fst_eq_zero ιY I J hJ hIJ h hh T.hom a b ha hb)
    (subsingleton_H_two_gaKernel f h) hZ

/-- **The Brauer group of a curve vanishes.** For a curve `C` over an algebraically closed
field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. Neither smoothness, nor properness, nor reducedness is
assumed. With `𝒩` the nilradical of `C`, some power `𝒩ᵐ` vanishes
(`AlgebraicGeometry.Scheme.exists_nilradical_pow_eq_bot`); the closed subscheme `C₁` cut out by
`𝒩` is reduced, so `Br(C₁) = 0`
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_isReduced`), and the closed
subschemes `Cⱼ ⊆ Cⱼ₊₁` cut out by `𝒩ʲ ⊇ 𝒩ʲ⁺¹` form square-zero thickenings, along which the
vanishing of the Brauer group propagates
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_squareZero`).
(blueprint: `lem-sc-brauer-zero-all-curves`) -/
theorem subsingleton_cohomologicalBrauerGroup (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Subsingleton C.CohomologicalBrauerGroup := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  obtain ⟨m, hm⟩ := C.exists_nilradical_pow_eq_bot
  let N := C.nilradical
  have hpow (a b : ℕ) (hab : b ≤ a) : N ^ a ≤ N ^ b := fun U ↦ Ideal.pow_le_pow_right hab
  have hmul (j a : ℕ) (ha : a ≤ j + j) : N ^ j * N ^ j ≤ N ^ a := fun U ↦ by
    change N.ideal U ^ j * N.ideal U ^ j ≤ N.ideal U ^ a
    rw [← pow_add]
    exact Ideal.pow_le_pow_right ha
  have key (j : ℕ) : Subsingleton (N ^ (j + 1)).subscheme.CohomologicalBrauerGroup := by
    induction j with
    | zero =>
      have : IsCurve ((N ^ (0 + 1)).subschemeι ≫ f) := comp_isClosedImmersion f _
      have h1 : N ^ (0 + 1) = N :=
        Scheme.IdealSheafData.ext (funext fun U ↦ pow_one (N.ideal U))
      have : IsReduced (N ^ (0 + 1)).subscheme := by
        rw [h1]
        infer_instance
      exact subsingleton_cohomologicalBrauerGroup_of_isReduced ((N ^ (0 + 1)).subschemeι ≫ f)
    | succ j ih =>
      have : IsCurve ((N ^ (j + 1 + 1)).subschemeι ≫ f) := comp_isClosedImmersion f _
      exact subsingleton_cohomologicalBrauerGroup_of_squareZero
        ((N ^ (j + 1 + 1)).subschemeι ≫ f) (N ^ (j + 1 + 1)).subschemeι (N ^ (j + 1))
        (N ^ (j + 1 + 1)) (by rw [Scheme.IdealSheafData.ker_subschemeι]) (hmul _ _ (by omega))
        (Scheme.IdealSheafData.inclusion (hpow _ _ (by omega)))
        (Scheme.IdealSheafData.inclusion_subschemeι _) ih
  exact subsingleton_cohomologicalBrauerGroup_of_squareZero f (𝟙 C) (N ^ (m + 1)) ⊥ bot_le
    ((hmul (m + 1) m (by omega)).trans hm.le) (N ^ (m + 1)).subschemeι (Category.comp_id _)
    (key m)

/-- **`H²` via the Kummer sequence.** For a curve `C` over an algebraically closed field `k`
(not necessarily smooth) and every `n ≥ 1` prime to `char k`,

`H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`.

This is the remark of blueprint `sk-prop-h2` that the identity holds for every curve, since
the Brauer group of every curve vanishes
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup`, blueprint
`lem-sc-brauer-zero-all-curves`); for smooth curves see
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth`.
(blueprint: `sk-prop-h2`, `lem-sc-second-kummer-divisors`) -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two (f : C ⟶ Spec (.of k))
    [IsCurve f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
      C.CohomologicalPicardGroup ⧸
        (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range) := by
  have hn' : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  obtain ⟨α, β, hα, hαβ, -⟩ := C.exists_exact_sheafH_rootsOfUnitySheaf_two n hn'
  have := subsingleton_cohomologicalBrauerGroup f
  rw [← hα]
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective α
    fun y ↦ (hαβ y).1 (Subsingleton.elim _ _)).symm⟩

end IsCurve

end AlgebraicGeometry
