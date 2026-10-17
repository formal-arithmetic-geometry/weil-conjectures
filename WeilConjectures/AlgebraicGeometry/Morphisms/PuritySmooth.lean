/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.NormalizationBasicOpen
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurity

/-!
# Purity of the branch locus over a scheme smooth over a normal Noetherian base

Let `S` be a Noetherian integral normal scheme with generic point `η`, `f : X ⟶ S` smooth, and
`Y ⟶ X` the relative normalization of `X` in a scheme `W` affine over `X` and lying over `η`.
Let `s ≠ η`. If `Y ⟶ X` is étale over the fibres of `f` at all strict generizations of `s`, and
over a dense subset of the fibre `X_s`, then it is étale over all of `X_s`
(`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`).

This is the translation to schemes of the commutative algebra statement
`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`, applied to affine opens
`Spec R₀ ⊆ S` around `s` and `Spec B ⊆ X` above it, with `M = Γ(W, w⁻¹(Spec B))`: the sections
of `Y` over a basic open of `Spec B` are integral closures
(`AlgebraicGeometry.Scheme.Hom.exists_etale_integralClosure_away`,
`AlgebraicGeometry.Scheme.Hom.etale_fromNormalization_basicOpen`).
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace RingTheory.DepthTwo

/-- Converse of `RingTheory.DepthTwo.etale_away_tensor_integralClosure`: if the base change
`B_h ⊗_B T₀` of the integral closure `T₀` of `B` in `L` is étale over `B_h`, then for all
localizations `B' = B[1/h]` and `L' = L[1/h]`, the integral closure of `B'` in `L'` is étale
over `B'` (integral closure commutes with localization). -/
lemma etale_integralClosure_of_etale_away_tensor {B L : Type*} [CommRing B] [CommRing L]
    [Algebra B L] (h : B) (B' L' : Type*) [CommRing B'] [CommRing L']
    [Algebra B B'] [IsLocalization.Away h B'] [Algebra L L']
    [IsLocalization.Away (algebraMap B L h) L'] [Algebra B' L'] [Algebra B L']
    [IsScalarTower B B' L'] [IsScalarTower B L L']
    (hE : Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L)) :
    Algebra.Etale B' (integralClosure B' L') := by
  have : IsLocalization (Algebra.algebraMapSubmonoid L (Submonoid.powers h)) L' := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have : Algebra.IsPushout B L B' L' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers h) B' L L'
  have : Algebra.IsPushout B B' L L' := this.symm
  let e : B' ⊗[B] integralClosure B L ≃ₐ[B'] integralClosure B' L' :=
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure B B' L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization (Submonoid.powers h))).trans
      (Algebra.IsPushout.equiv B B' L L').mapIntegralClosure
  let eB : Localization.Away h ≃ₐ[B] B' :=
    IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h) B'
  let : Algebra (Localization.Away h) B' := eB.toRingHom.toAlgebra
  have : IsScalarTower B (Localization.Away h) B' :=
    .of_algebraMap_eq fun b ↦ (eB.commutes b).symm
  exact .of_equiv ((Algebra.TensorProduct.cancelBaseChange B (Localization.Away h) B' B'
    (integralClosure B L)).trans e)

end RingTheory.DepthTwo

namespace AlgebraicGeometry.Scheme.Hom

/-- **Purity for normal covers of a scheme smooth over a normal Noetherian base.** Let `S` be a
Noetherian integral normal scheme, `f : X ⟶ S` smooth, `w : W ⟶ X` an affine morphism with `W`
lying over the generic point of `S`, and `p : Y ⟶ X` the relative normalization of `X` in `W`.
Let `s ∈ S` be a point other than the generic point. Assume that `p` is étale at all points of
`Y` lying over strict generizations of `s`, and that every point of the fibre `X_s` generizes
inside `X_s` to a point over which `p` is étale. Then `p` is étale at every point of `Y` lying
over `s`.

Proof. Let `x` be the image of the given point of `Y`. Choose affine opens `Spec R₀ = V ∋ s` of
`S` and `Spec B = U ∋ x` of `X` with `U ⊆ f⁻¹ V`, and let `M = Γ(W, w⁻¹ U)`, so that the
sections of `Y` over basic opens `D(h)` of `U` are the integral closures of `B_h` in `M_h`. The
ring `R₀` is a Noetherian integrally closed domain, `B` is smooth over `R₀`, the prime `q` of `s`
is nonzero (`s` is not the generic point) and the nonzero elements of `R₀` are invertible in `M`
(`W` lies over the generic point). For a prime `Q` of `B` contained in the prime `P` of `x`, the
normalization is étale over the corresponding point of `U` if `Q` does not lie over `q` (it lies
over a strict generization of `s`), or if `Q` is a minimal prime of `qB` (its point generizes in
`X_s` to a point over which `p` is étale, which by minimality is the point of `Q` itself); hence
over a basic open around it. So `RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`
applies and gives a basic open `D(h) ∋ x` over which `p` is étale. -/
theorem mem_etaleLocus_fromNormalization_of_smooth {S X W : Scheme.{u}} [IsNoetherian S]
    [IsIntegral S] (hS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [Smooth f] (w : W ⟶ X) [IsAffineHom w]
    (hWη : ∀ z : W, f (w z) = genericPoint S) (s : S) (hs : s ≠ genericPoint S)
    (H : ∀ y : w.normalization, f (w.fromNormalization y) ⤳ s →
      f (w.fromNormalization y) ≠ s → y ∈ w.fromNormalization.etaleLocus)
    (hgen : ∀ x : X, f x = s → ∃ x' : X, x' ⤳ x ∧ f x' = s ∧
      ∀ y : w.normalization, w.fromNormalization y = x' → y ∈ w.fromNormalization.etaleLocus)
    (y : w.normalization) (hy : f (w.fromNormalization y) = s) :
    y ∈ w.fromNormalization.etaleLocus := by
  subst hy
  set x := w.fromNormalization y
  -- affine opens `V ∋ f x` of `S` and `U ∋ x` of `X` with `U ⊆ f⁻¹ V`
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (a := x) hsV (f ⁻¹ᵁ V).2
  have : Nonempty V := ⟨⟨f x, hsV⟩⟩
  have hwU : IsAffineOpen (w ⁻¹ᵁ U) := hU.preimage w
  -- the rings `R₀ = Γ(S, V)`, `B = Γ(X, U)` and `M = Γ(W, w⁻¹ U)`
  let := (f.appLE V U hUV).hom.toAlgebra
  let := (w.app U).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(W, w ⁻¹ᵁ U) := (f.appLE V U hUV ≫ w.app U).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(W, w ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsIntegrallyClosed Γ(S, V) := isIntegrallyClosed_of_isIntegrallyClosed_stalk hS V
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Algebra.Smooth Γ(S, V) Γ(X, U) :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  -- points of `U` and `V` versus primes of `B` and `R₀`
  have hmem (p : PrimeSpectrum Γ(X, U)) : hU.fromSpec p ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self _
  have hpt (p : PrimeSpectrum Γ(X, U)) : hU.primeIdealOf ⟨_, hmem p⟩ = p :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hcomap (p : PrimeSpectrum Γ(X, U)) : p.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U)) =
      (hV.primeIdealOf ⟨f (hU.fromSpec p), hUV (hmem p)⟩).asIdeal := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV (hmem p), hpt]
    rfl
  have hVinj {a b : S} (ha : a ∈ V) (hb : b ∈ V)
      (e : (hV.primeIdealOf ⟨a, ha⟩).asIdeal = (hV.primeIdealOf ⟨b, hb⟩).asIdeal) : a = b := by
    have := congrArg hV.fromSpec (PrimeSpectrum.ext e)
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at this
  -- the primes `q` of `f x` and `P` of `x`
  set q := (hV.primeIdealOf ⟨f x, hsV⟩).asIdeal
  set P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hP : P.comap (algebraMap Γ(S, V) Γ(X, U)) = q :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)
  have hq : q ≠ ⊥ := by
    intro hq0
    have hη : genericPoint S ∈ V :=
      ((genericPoint_spec S).mem_open_set_iff V.2).2 ⟨f x, trivial, hsV⟩
    refine hs (Specializes.antisymm ?_
      ((genericPoint_spec S).specializes (Set.mem_univ _))).eq
    have h1 : hV.primeIdealOf ⟨f x, hsV⟩ ⤳ hV.primeIdealOf ⟨_, hη⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (hq0.le.trans bot_le)
    have := h1.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at this
  -- the nonzero elements of `R₀` are invertible in `M`: `W` lies over the generic point
  have hunit (r : Γ(S, V)) (hr : r ≠ 0) : IsUnit (algebraMap Γ(S, V) Γ(W, w ⁻¹ᵁ U) r) := by
    refine W.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz ↦ ?_
    rw [← Scheme.mem_basicOpen, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
      RingHom.comp_apply, ← Scheme.preimage_basicOpen, Scheme.basicOpen_appLE]
    refine ⟨hz, ?_⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, hWη]
    obtain ⟨t, ht⟩ : (S.basicOpen r : Set S).Nonempty := by
      by_contra hn
      exact hr ((basicOpen_eq_bot_iff r).1
        ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).1 hn))
    exact ((genericPoint_spec S).mem_open_set_iff (S.basicOpen r).2).2 ⟨t, trivial, ht⟩
  -- étaleness over a point of `U` gives the hypothesis of the ring theorem at its prime
  have hloc (Q : Ideal Γ(X, U)) (hQ : Q.IsPrime)
      (hE : ∀ z : w.normalization, w.fromNormalization z = hU.fromSpec ⟨Q, hQ⟩ →
        z ∈ w.fromNormalization.etaleLocus) :
      ∃ h ∉ Q, Algebra.Etale (Localization.Away h)
          (Localization.Away h ⊗[Γ(X, U)] integralClosure Γ(X, U) Γ(W, w ⁻¹ᵁ U)) ∧
        Module.Finite (Localization.Away h)
          (Localization.Away h ⊗[Γ(X, U)] integralClosure Γ(X, U) Γ(W, w ⁻¹ᵁ U)) := by
    obtain ⟨h, hyh, hle⟩ := w.fromNormalization.exists_basicOpen_le_etaleLocus hU (hmem _) hE
    have hhQ : h ∉ Q := by
      have : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen h := hyh
      rwa [hU.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen] at this
    obtain ⟨B', L', _, _, _, _, _, _, _, _, _, _, hE'⟩ :=
      w.exists_etale_integralClosure_away hU hwU h (Scheme.Hom.etale_of_le_etaleLocus hle)
    have := RingTheory.DepthTwo.etale_away_tensor_integralClosure
      (L := Γ(W, w ⁻¹ᵁ U)) h B' L' hE'
    exact ⟨h, hhQ, this, Algebra.IsIntegral.finite⟩
  -- the normalization is étale over the primes required by the ring theorem
  have hpts (Q : Ideal Γ(X, U)) (hQ : Q.IsPrime) (hQP : Q ≤ P)
      (hQq : Q.comap (algebraMap Γ(S, V) Γ(X, U)) ≠ q ∨
        Q ∈ (q.map (algebraMap Γ(S, V) Γ(X, U))).minimalPrimes)
      (z : w.normalization) (hz : w.fromNormalization z = hU.fromSpec ⟨Q, hQ⟩) :
      z ∈ w.fromNormalization.etaleLocus := by
    have hxQx : hU.fromSpec ⟨Q, hQ⟩ ⤳ x := by
      have := ((PrimeSpectrum.le_iff_specializes ⟨Q, hQ⟩ (hU.primeIdealOf ⟨x, hxU⟩)).1
        hQP).map hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf] at this
    have hQc := hcomap ⟨Q, hQ⟩
    rcases hQq with hQq | hQm
    · refine H z ?_ fun he ↦ hQq ?_
      · rw [hz]
        exact hxQx.map f.continuous
      · rw [hz] at he
        exact hQc.trans (congrArg (fun t ↦ (hV.primeIdealOf t).asIdeal) (Subtype.ext he))
    · have hQq : Q.comap (algebraMap Γ(S, V) Γ(X, U)) = q :=
        le_antisymm (hP ▸ Ideal.comap_mono hQP) (Ideal.map_le_iff_le_comap.1 hQm.1.2)
      obtain ⟨x', hx'x, hfx', hE'⟩ := hgen _ (hVinj _ _ (hQc.symm.trans hQq))
      have hx'U : x' ∈ U := hx'x.mem_open U.2 (hmem _)
      have hQ'Q : (hU.primeIdealOf ⟨x', hx'U⟩).asIdeal ≤ Q := by
        have : hU.fromSpec (hU.primeIdealOf ⟨x', hx'U⟩) ⤳ hU.fromSpec ⟨Q, hQ⟩ := by
          rw [hU.fromSpec_primeIdealOf]
          exact hx'x
        exact (PrimeSpectrum.le_iff_specializes _ _).2
          (hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 this)
      have hQ'q : (hU.primeIdealOf ⟨x', hx'U⟩).asIdeal.comap (algebraMap Γ(S, V) Γ(X, U)) = q :=
        (congrArg PrimeSpectrum.asIdeal
          (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hx'U)).trans
          (congrArg (fun t ↦ (hV.primeIdealOf t).asIdeal) (Subtype.ext hfx'))
      have hQQ' := hQm.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.2 hQ'q.ge⟩ hQ'Q
      exact hE' z (hz.trans ((congrArg hU.fromSpec
        (PrimeSpectrum.ext (le_antisymm hQQ' hQ'Q))).trans
          (hU.fromSpec_primeIdealOf ⟨x', hx'U⟩)))
  obtain ⟨h, hhP, hE, -⟩ := RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth q hq
    hunit P hP fun Q hQ hQP hQq ↦ hloc Q hQ (hpts Q hQ hQP hQq)
  have hEg := w.etale_fromNormalization_basicOpen hU hwU h fun B' L' _ _ _ _ _ _ _ _ _ _ ↦
    RingTheory.DepthTwo.etale_integralClosure_of_etale_away_tensor h B' L' hE
  refine Scheme.Hom.mem_etaleLocus.2 ⟨_, ?_, hEg⟩
  have : hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen h := by
    rw [hU.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]
    exact hhP
  rwa [Scheme.Hom.mem_preimage, hU.fromSpec_primeIdealOf] at this

end AlgebraicGeometry.Scheme.Hom
