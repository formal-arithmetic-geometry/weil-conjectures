/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.QuasiFinite.Basic
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Fiber

/-!
# A projective coordinate complement is finite

Let `p : Y ⟶ S` be proper over an integral locally noetherian scheme, covered by finitely many
opens `Y_α`, each embedded as a closed subscheme of an affine space `𝔸^{σ_α}_S`. Choose for every
coordinate `t_{α r} : Y_α ⟶ 𝔸¹_S` a nonempty (equivalently, dense) open `V_{α r} ⊆ 𝔸¹_S`. Over a
nonempty open of `S`, the complement `Z` of the union of the `t_{α r}⁻¹ V_{α r}` is finite over
`S`. This is the first step of Deligne's generic constructibility theorem
(`thm-fin-deligne-generic-open`).

## Main statements

- `MvPolynomial.finite_setOf_comap_C_eq_of_monic`: over a prime of `A`, only finitely many primes
  of `A[X_r]` contain given monic polynomials `g_r(X_r)`.
- `AlgebraicGeometry.AffineSpace.finite_setOf_reindex_notMem`: the points of `𝔸^σ_S` all of whose
  coordinates avoid opens with monic complements form finite fibres.
- `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_range_subset`
  (`lem-fin-projective-coordinate-boundary`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped Polynomial

/-- Evaluating a one-variable polynomial `g` at the variable `X r` and then applying `eval₂Hom`
is the same as evaluating `g` at `v r`. -/
lemma MvPolynomial.eval₂Hom_polynomial_eval₂_X {R S σ : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (v : σ → S) (g : R[X]) (r : σ) :
    eval₂Hom f v (g.eval₂ C (X r)) = g.eval₂ f (v r) := by
  rw [Polynomial.hom_eval₂, eval₂Hom_comp_C, eval₂Hom_X']

/-- Let `g_r` be monic polynomials over `A`, indexed by a finite type `σ`. Over each prime `p`
of `A` there are only finitely many primes of `A[X_r : r ∈ σ]` containing every `g_r(X_r)`. -/
theorem MvPolynomial.finite_setOf_comap_C_eq_of_monic {A σ : Type*} [CommRing A] [Finite σ]
    (g : σ → A[X]) (hg : ∀ r, (g r).Monic) (p : PrimeSpectrum A) :
    {P : PrimeSpectrum (MvPolynomial σ A) |
      PrimeSpectrum.comap (C : A →+* MvPolynomial σ A) P = p ∧
        ∀ r, (g r).eval₂ C (X r) ∈ P.asIdeal}.Finite := by
  classical
  set I : Ideal (MvPolynomial σ A) := Ideal.span (Set.range fun r ↦ (g r).eval₂ C (X r))
  have hint (r : σ) : IsIntegral A (Ideal.Quotient.mkₐ A I (X r)) := by
    refine ⟨g r, hg r, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Polynomial.aeval_def,
      MvPolynomial.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨r, rfl⟩)
  have hadj : Algebra.adjoin A (Set.range fun r ↦ Ideal.Quotient.mkₐ A I (X r)) = ⊤ := by
    rw [Set.range_comp' (Ideal.Quotient.mkₐ A I) X, ← AlgHom.map_adjoin, adjoin_range_X,
      Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A I
  have : Module.Finite A (MvPolynomial σ A ⧸ I) := by
    refine ⟨?_⟩
    have := fg_adjoin_of_finite (Set.finite_range _) (by rintro _ ⟨r, rfl⟩; exact hint r)
    rwa [hadj, Algebra.top_toSubmodule] at this
  refine ((Algebra.QuasiFinite.finite_comap_preimage_singleton (R := A)
    (S := MvPolynomial σ A ⧸ I) p).image (PrimeSpectrum.comap (Ideal.Quotient.mk I))).subset ?_
  rintro P ⟨hP, hPg⟩
  have hIP : P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact Ideal.span_le.2 (Set.range_subset_iff.2 hPg)
  obtain ⟨Q, rfl⟩ := hIP
  refine ⟨Q, ?_, rfl⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff, ← hP, ← PrimeSpectrum.comap_comp_apply]
  rfl

namespace AlgebraicGeometry

namespace AffineSpace

variable {σ : Type u} {T : Scheme.{u}} [IsAffine T]

lemma mem_isoOfIsAffine_hom_apply_iff (x : 𝔸(σ; T)) (m : MvPolynomial σ Γ(T, ⊤)) :
    m ∈ ((isoOfIsAffine σ T).hom x).asIdeal ↔
      x ∉ 𝔸(σ; T).basicOpen
        (MvPolynomial.eval₂Hom (𝔸(σ; T) ↘ T).appTop.hom (coord T) m) := by
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  simp only [isoOfIsAffine_hom, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
    MvPolynomial.coe_eval₂Hom, TopologicalSpace.Opens.mem_map]
  exact not_not.symm

lemma comap_C_isoOfIsAffine_hom_apply (x : 𝔸(σ; T)) :
    PrimeSpectrum.comap MvPolynomial.C ((isoOfIsAffine σ T).hom x) =
      T.isoSpec.hom ((𝔸(σ; T) ↘ T) x) := by
  have h1 : (isoOfIsAffine σ T).hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      (𝔸(σ; T) ↘ T) ≫ T.isoSpec.hom := by
    rw [← cancel_epi (isoOfIsAffine σ T).inv, Iso.inv_hom_id_assoc, isoOfIsAffine_inv_over_assoc,
      Iso.inv_hom_id, Category.comp_id]
  have h2 := congrArg (fun f ↦ f x) h1
  simp only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom] at h2
  exact h2

/-- Let `g_r` be monic polynomials over `Γ(T, ⊤)` for an affine scheme `T`. In every fibre of
`𝔸^σ_T ⟶ T`, only finitely many points lie in the common zero locus of the `g_r(t_r)`. -/
theorem finite_setOf_notMem_basicOpen_of_monic [Finite σ] (g : σ → Γ(T, ⊤)[X])
    (hg : ∀ r, (g r).Monic) (t : T) :
    {x : 𝔸(σ; T) | (𝔸(σ; T) ↘ T) x = t ∧
      ∀ r, x ∉ 𝔸(σ; T).basicOpen ((g r).eval₂ (𝔸(σ; T) ↘ T).appTop.hom (coord T r))}.Finite := by
  refine ((MvPolynomial.finite_setOf_comap_C_eq_of_monic g hg (T.isoSpec.hom t)).preimage
    (Scheme.homeoOfIso (isoOfIsAffine σ T)).injective.injOn).subset ?_
  rintro x ⟨hxt, hx⟩
  refine ⟨?_, fun r ↦ ?_⟩
  · rw [Scheme.homeoOfIso_apply, comap_C_isoOfIsAffine_hom_apply, hxt]
  · rw [Scheme.homeoOfIso_apply, mem_isoOfIsAffine_hom_apply_iff,
      MvPolynomial.eval₂Hom_polynomial_eval₂_X]
    exact hx r

/-- The complement of a nonempty open `U` of the affine line over an integral affine scheme `T` is
contained in the zero locus of a nonzero polynomial. -/
theorem exists_ne_zero_forall_notMem_basicOpen [IsIntegral T] (U : 𝔸(PUnit.{u + 1}; T).Opens)
    (hU : (U : Set 𝔸(PUnit.{u + 1}; T)).Nonempty) :
    ∃ g : Γ(T, ⊤)[X], g ≠ 0 ∧ ∀ x ∉ U, x ∉ 𝔸(PUnit.{u + 1}; T).basicOpen
      (g.eval₂ (𝔸(PUnit.{u + 1}; T) ↘ T).appTop.hom (coord T PUnit.unit)) := by
  set Ψ := Scheme.homeoOfIso (isoOfIsAffine PUnit.{u + 1} T)
  set Z := Ψ '' (U : Set 𝔸(PUnit.{u + 1}; T))ᶜ
  have hZ : IsClosed Z := Ψ.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨m, hmZ, hmx₀⟩ : ∃ m ∈ PrimeSpectrum.vanishingIdeal Z, m ∉ (Ψ x₀).asIdeal := by
    by_contra! h
    have : Ψ x₀ ∈ Z := by
      rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact h
    obtain ⟨y, hy, hyx⟩ := this
    exact hy (Ψ.injective hyx ▸ hx₀)
  obtain ⟨g, rfl⟩ := (MvPolynomial.uniqueAlgEquiv Γ(T, ⊤) PUnit.{u + 1}).symm.surjective m
  refine ⟨g, fun h ↦ hmx₀ (by simp [h]), fun x hx ↦ ?_⟩
  have hm := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hmZ _ ⟨x, hx, rfl⟩
  rw [Scheme.homeoOfIso_apply, mem_isoOfIsAffine_hom_apply_iff,
    MvPolynomial.uniqueAlgEquiv_symm_apply, MvPolynomial.eval₂Hom_polynomial_eval₂_X] at hm
  exact hm

/-- Let `c : T ⟶ S` be an open immersion from an affine scheme and `V_r ⊆ 𝔸¹_S` opens, indexed by
a finite type `σ`, whose complements over `T` lie in the zero loci of monic polynomials. Then over
each point of `T`, only finitely many points of `𝔸^σ_S` have all their coordinates outside the
`V_r`. -/
theorem finite_setOf_reindex_notMem {S : Scheme.{u}} (c : T ⟶ S) [IsOpenImmersion c] [Finite σ]
    (V : σ → 𝔸(PUnit.{u + 1}; S).Opens) (g : σ → Γ(T, ⊤)[X]) (hg : ∀ r, (g r).Monic)
    (hV : ∀ r x, map PUnit c x ∉ V r → x ∉ 𝔸(PUnit.{u + 1}; T).basicOpen
      ((g r).eval₂ (𝔸(PUnit.{u + 1}; T) ↘ T).appTop.hom (coord T PUnit.unit))) (t : T) :
    {x : 𝔸(σ; S) | (𝔸(σ; S) ↘ S) x = c t ∧
      ∀ r, reindex (fun _ : PUnit.{u + 1} ↦ r) S x ∉ V r}.Finite := by
  refine ((finite_setOf_notMem_basicOpen_of_monic g hg t).image (map σ c)).subset ?_
  rintro x ⟨hxt, hx⟩
  obtain ⟨x', rfl⟩ : x ∈ Set.range (map σ c) := by
    rw [range_map]
    exact ⟨t, hxt.symm⟩
  refine ⟨x', ⟨c.isOpenEmbedding.injective ?_, fun r ↦ ?_⟩, rfl⟩
  · rw [← Scheme.Hom.comp_apply, map_over, Scheme.Hom.comp_apply] at hxt
    exact hxt
  · have h := hV r (reindex (fun _ : PUnit.{u + 1} ↦ r) T x') (by
      rw [← Scheme.Hom.comp_apply, ← map_reindex, Scheme.Hom.comp_apply]
      exact hx r)
    have h' : x' ∉ reindex (fun _ : PUnit.{u + 1} ↦ r) T ⁻¹ᵁ 𝔸(PUnit.{u + 1}; T).basicOpen
        ((g r).eval₂ (𝔸(PUnit.{u + 1}; T) ↘ T).appTop.hom (coord T PUnit.unit)) := h
    have hc : (reindex (fun _ : PUnit.{u + 1} ↦ r) T).appTop.hom.comp
        (𝔸(PUnit.{u + 1}; T) ↘ T).appTop.hom = (𝔸(σ; T) ↘ T).appTop.hom := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, reindex_over]
    rwa [Scheme.preimage_basicOpen_top, Polynomial.hom_eval₂, hc, reindex_appTop_coord] at h'

end AffineSpace

/-- Blueprint `lem-fin-projective-coordinate-boundary`: A projective coordinate complement is
finite.

Let `S` be integral and locally noetherian (the blueprint takes `S = Spec A` affine) and let
`p : Y ⟶ S` be proper (the blueprint takes `p` projective). Let `Y = ⋃_α Y_α` be a finite open
cover with closed immersions `e_α : Y_α ⟶ 𝔸^{σ_α}_S` over `S`, and for each coordinate
`t_{α r} : Y_α ⟶ 𝔸¹_S` let `V_{α r} ⊆ 𝔸¹_S` be a nonempty open. Then there is a nonempty open
`W ⊆ S` over which every closed subscheme `Z` of `Y` supported in the complement of
`⋃_{α, r} t_{α r}⁻¹(V_{α r})` (for instance the reduced one) is finite over `W`. -/
theorem exists_isFinite_morphismRestrict_of_range_subset {S Y : Scheme.{u}} [IsIntegral S]
    [IsLocallyNoetherian S] (p : Y ⟶ S) [IsProper p] {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hU : ⨆ α, U α = ⊤) (σ : ι → Type u) [∀ α, Finite (σ α)]
    (e : ∀ α, (U α).toScheme ⟶ 𝔸(σ α; S)) [∀ α, IsClosedImmersion (e α)]
    (he : ∀ α, e α ≫ 𝔸(σ α; S) ↘ S = (U α).ι ≫ p)
    (V : ∀ α, σ α → 𝔸(PUnit; S).Opens) (hV : ∀ α r, (V α r : Set 𝔸(PUnit; S)).Nonempty) :
    ∃ W : S.Opens, (W : Set S).Nonempty ∧
      ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i],
        Set.range i ⊆ (⋃ (α : ι) (r : σ α), (U α).ι ''
          ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹' (V α r : Set 𝔸(PUnit; S))))ᶜ →
        IsFinite ((i ≫ p) ∣_ W) := by
  classical
  -- a nonempty affine open `S₀` of `S`
  obtain ⟨s⟩ : Nonempty S := inferInstance
  obtain ⟨S₀, hS₀, hsS₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  have : IsAffine S₀ := hS₀
  have : Nonempty S₀ := ⟨⟨s, hsS₀⟩⟩
  -- the opens `V α r` meet the part of `𝔸¹_S` over `S₀`
  have hV₀ (α : ι) (r : σ α) :
      ((AffineSpace.map PUnit S₀.ι ⁻¹ᵁ V α r : 𝔸(PUnit; S₀).Opens) :
        Set 𝔸(PUnit; S₀)).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := (𝔸(PUnit; S) ↘ S).surjective s
    obtain ⟨x, hxV, hx⟩ := nonempty_preirreducible_inter (V α r).isOpen
      ((𝔸(PUnit; S) ↘ S) ⁻¹ᵁ S₀).isOpen (hV α r) ⟨x₀, show _ ∈ S₀ from hx₀ ▸ hsS₀⟩
    have hx' : x ∈ Set.range (AffineSpace.map PUnit S₀.ι) := by
      rw [AffineSpace.range_map, Scheme.Opens.range_ι]
      exact hx
    obtain ⟨y, rfl⟩ := hx'
    exact ⟨y, hxV⟩
  choose g hg0 hg using fun α r ↦ AffineSpace.exists_ne_zero_forall_notMem_basicOpen _ (hV₀ α r)
  -- invert all the leading coefficients
  have : Fintype ((α : ι) × σ α) := Fintype.ofFinite _
  set b : Γ(S₀, ⊤) := ∏ i : (α : ι) × σ α, (g i.1 i.2).leadingCoeff
  have hb0 : b ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦
    Polynomial.leadingCoeff_ne_zero.2 (hg0 i.1 i.2)
  set W' : S₀.toScheme.Opens := S₀.toScheme.basicOpen b
  have hW'ne : (W' : Set S₀.toScheme).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact hb0 (by simpa [W'] using hne)
  have : IsAffine W' := (isAffineOpen_top S₀.toScheme).basicOpen b
  have : Nonempty W' := hW'ne.to_subtype
  have hb : IsUnit (W'.ι.appTop b) := by
    refine W'.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun x _ ↦
      (W'.toScheme.mem_basicOpen_top _ x).1 ?_
    rw [← Scheme.preimage_basicOpen_top, Scheme.Opens.ι_preimage_self]
    trivial
  have hunit (α : ι) (r : σ α) : IsUnit (W'.ι.appTop (g α r).leadingCoeff) :=
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem
      (fun i : (α : ι) × σ α ↦ (g i.1 i.2).leadingCoeff) (Finset.mem_univ ⟨α, r⟩))) hb
  set h : ∀ α, σ α → Γ(W', ⊤)[X] := fun α r ↦
    Polynomial.C ((hunit α r).unit⁻¹ : Γ(W', ⊤)ˣ).1 * (g α r).map W'.ι.appTop.hom
  have hmonic (α : ι) (r : σ α) : (h α r).Monic := by
    refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (hunit α r).ne_zero]
    exact (hunit α r).val_inv_mul
  set c : W'.toScheme ⟶ S := W'.ι ≫ S₀.ι
  have hVh (α : ι) (r : σ α) (x : 𝔸(PUnit; W')) (hx : AffineSpace.map PUnit c x ∉ V α r) :
      x ∉ 𝔸(PUnit; W').basicOpen
        ((h α r).eval₂ (𝔸(PUnit; W') ↘ W').appTop.hom (AffineSpace.coord _ PUnit.unit)) := by
    have h1 : AffineSpace.map PUnit W'.ι x ∉ AffineSpace.map PUnit S₀.ι ⁻¹ᵁ V α r := by
      simpa [c, AffineSpace.map_comp] using hx
    have h2 : x ∉ AffineSpace.map PUnit W'.ι ⁻¹ᵁ 𝔸(PUnit; S₀).basicOpen
        ((g α r).eval₂ (𝔸(PUnit; S₀) ↘ S₀).appTop.hom (AffineSpace.coord _ PUnit.unit)) :=
      hg α r _ h1
    have hc : (AffineSpace.map PUnit W'.ι).appTop.hom.comp (𝔸(PUnit; S₀) ↘ S₀).appTop.hom =
        (𝔸(PUnit; W') ↘ W').appTop.hom.comp W'.ι.appTop.hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, AffineSpace.map_over]
    rw [Scheme.preimage_basicOpen_top, Polynomial.hom_eval₂, hc, AffineSpace.map_appTop_coord,
      ← Polynomial.eval₂_map] at h2
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Scheme.basicOpen_mul]
    exact fun hx' ↦ h2 hx'.2
  refine ⟨c.opensRange, ?_, fun Z i _ hZ ↦ ?_⟩
  · obtain ⟨t⟩ : Nonempty W' := inferInstance
    exact ⟨c t, t, rfl⟩
  -- the fibres of `Y ⟶ S` over `W` meet the complement in finitely many points
  have hY (t : W') : {y : Y | p y = c t ∧ y ∈ (⋃ (α : ι) (r : σ α), (U α).ι ''
      ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹'
        (V α r : Set 𝔸(PUnit; S))))ᶜ}.Finite := by
    have hα (α : ι) : {u : U α | p ((U α).ι u) = c t ∧
        ∀ r, AffineSpace.reindex (fun _ : PUnit ↦ r) S (e α u) ∉ V α r}.Finite := by
      refine ((AffineSpace.finite_setOf_reindex_notMem c (V α) (h α) (hmonic α) (hVh α)
        t).preimage (e α).injective.injOn).subset ?_
      rintro u ⟨hut, hu⟩
      refine ⟨?_, hu⟩
      rw [← hut, ← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
    refine (Set.finite_iUnion fun α ↦ (hα α).image (U α).ι).subset ?_
    rintro y ⟨hyt, hy⟩
    obtain ⟨α, hα⟩ : ∃ α, y ∈ U α := by
      rw [← TopologicalSpace.Opens.mem_iSup, hU]
      trivial
    refine Set.mem_iUnion.2 ⟨α, ⟨y, hα⟩, ⟨hyt, fun r hr ↦ hy ?_⟩, rfl⟩
    exact Set.mem_iUnion₂.2 ⟨α, r, ⟨y, hα⟩, by simpa using hr, rfl⟩
  have hfib (t : W') : {z : Z | (i ≫ p) z = c t}.Finite :=
    ((hY t).preimage i.injective.injOn).subset fun z hz ↦ ⟨hz, hZ ⟨z, rfl⟩⟩
  have : LocallyQuasiFinite ((i ≫ p) ∣_ c.opensRange) := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun w ↦ ?_
    obtain ⟨t, ht⟩ := w.2
    refine ((hfib t).preimage ((i ≫ p) ⁻¹ᵁ c.opensRange).ι.injective.injOn).subset ?_
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    change (i ≫ p) (((i ≫ p) ⁻¹ᵁ c.opensRange).ι z) = c t
    rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hz, ht]
    rfl
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end AlgebraicGeometry
