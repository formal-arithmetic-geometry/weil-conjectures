/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel
public import WeilConjectures.RingTheory.GradedAlgebra.LinearPair

/-!
# Finite projections of projective curves to the projective line

Let `k` be an infinite field and `X` an integral closed subscheme of a projective space over
`k` of dimension one. Then there is a finite morphism `X ⟶ ℙ¹_k` over `k`.

The proof goes through the homogeneous coordinate ring: `X ≅ Proj S` for a standard graded
`k`-algebra `S` which is a domain; since `Proj S` has dimension one, there are linear forms
`l₀, l₁ ∈ S₁` without common zero on `Proj S`, and the linear projection
`π_{l₀,l₁} : Proj S ⟶ ℙ¹_k` is finite.

## Main statements

- `AlgebraicGeometry.exists_isStandard_iso_proj` — the homogeneous coordinate ring of an
  integral closed subscheme of projective space.
- `AlgebraicGeometry.exists_isFinite_toProjectiveLine` — a projective curve over an infinite
  field admits a finite morphism to `ℙ¹_k`.
-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

/-- **The homogeneous coordinate model**: an integral closed subscheme `X` of `ℙ(n; Spec k)`
is, over `k`, isomorphic to `Proj S` for a standard graded `k`-algebra `S` which is a domain,
namely the quotient of the polynomial ring by the homogeneous ideal of `X`
(blueprint: `lem-pc-projective-coordinate-model`). -/
theorem exists_isStandard_iso_proj {k : Type u} [Field k] {n : Type u} [Finite n]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X] (i : X ⟶ ℙ(n; Spec (.of k)))
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (𝒜 : ℕ → Submodule k S)
      (_ : GradedAlgebra 𝒜), GradedAlgebra.IsStandard 𝒜 ∧ IsDomain S ∧
        ∃ e : X ≅ Proj 𝒜, e.hom ≫ Proj.toSpecBase 𝒜 = X ↘ Spec (.of k) := by
  classical
  -- A standard chart `U = D₊(T_{j₀})` containing the image of the generic point `ξ` of `X`.
  obtain ⟨j₀, hj₀⟩ : ∃ j, i (genericPoint X) ∈ ProjectiveSpace.standardOpen n (Spec (.of k)) j :=
    TopologicalSpace.Opens.mem_iSup.mp
      ((ProjectiveSpace.iSup_standardOpen n (Spec (.of k))).ge (Set.mem_univ _))
  set U := ProjectiveSpace.standardOpen n (Spec (.of k)) j₀
  set W := i ⁻¹ᵁ U
  have hW : IsAffineOpen W := (ProjectiveSpace.isAffineOpen_standardOpen n _ j₀).preimage i
  have : IsAffine W.toScheme := hW
  have : Nonempty W.toScheme := ⟨⟨genericPoint X, hj₀⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  -- The chart `W = i⁻¹ U ⟶ U ≅ 𝔸(n ∖ {j₀}; Spec k)` and its coordinates.
  set g : W.toScheme ⟶ 𝔸({j : n // j ≠ j₀}; Spec (.of k)) :=
    (i ∣_ U) ≫ (ProjectiveSpace.standardOpenIso n _ j₀).hom
  let _ : Algebra k Γ(W.toScheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫
      (g ≫ 𝔸({j : n // j ≠ j₀}; Spec (.of k)) ↘ Spec (.of k)).appTop).hom.toAlgebra
  have hg := AffineSpace.isoSpec_inv_comp_eq_homOfVector g
  set v : {j : n // j ≠ j₀} → Γ(W.toScheme, ⊤) := fun j ↦ g.appTop (AffineSpace.coord _ j)
  -- The homogeneous coordinate ring `k[a_j t] ⊆ Γ(W, ⊤)[t]`, with `a_{j₀} = 1`.
  let a : n → Γ(W.toScheme, ⊤) := fun j ↦ if hj : j = j₀ then 1 else v ⟨j, hj⟩
  have ha : a j₀ = 1 := dif_pos rfl
  set V := Submodule.span k (Set.range a)
  have hstd : GradedAlgebra.IsStandard V.powersGrading :=
    Submodule.isStandard_powersGrading (Submodule.fg_span (Set.finite_range a))
  set l := Submodule.powersLinearForm k a
  have hl := Submodule.powersLinearForm_mem k a
  have hcov : ⨆ j, Proj.basicOpen V.powersGrading (l j) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _
      (GradedAlgebra.IsStandard.irrelevant_le_of_grade_one_subset fun x hx ↦
        Submodule.span_le_restrictScalars k _ _ (Submodule.powersGrading_one_le_span k a hx))
  -- The linear projection `p : Proj S ⟶ ℙ(n; Spec k)` is a closed immersion.
  set p := Proj.linearProjection V.powersGrading l hl hcov
  have hgen (j : n) : Algebra.adjoin k (Set.range fun j' : {j' // j' ≠ j} ↦
      Away.mk V.powersGrading (hl j) 1 (l j'.1) (by simpa using hl j'.1)) = ⊤ := by
    refine eq_top_iff.mpr ((GradedAlgebra.IsStandard.adjoin_away_eq_top hl
      (Submodule.powersGrading_one_le_span k a) j).symm.le.trans (Algebra.adjoin_le ?_))
    rintro _ ⟨j', rfl⟩
    by_cases hj : j' = j
    · subst hj
      beta_reduce
      rw [SetLike.mem_coe, Away.mk_self]
      exact one_mem _
    · exact Algebra.subset_adjoin (Set.mem_range.mpr ⟨⟨j', hj⟩, rfl⟩)
  have : IsClosedImmersion p := Proj.isClosedImmersion_linearProjection _ l hl hcov hgen
  have : IsReduced (Proj V.powersGrading) := Proj.isReduced_of_isDomain _
  -- Comparison on the chart `U`: `Γ(W, ⊤) ≅ S_(l_{j₀})`.
  obtain ⟨e, he⟩ := Proj.exists_iso_linearProjection_restrict V.powersGrading l hl hcov j₀
  set φ := Submodule.powersAwayEval k ha
  set φ' : CommRingCat.of (Away V.powersGrading (l j₀)) ⟶ Γ(W.toScheme, ⊤) :=
    CommRingCat.ofHom φ.toRingHom
  have hφ (j : {j : n // j ≠ j₀}) :
      φ (Away.mk V.powersGrading (hl j₀) 1 (l j.1) (by simpa using hl j.1)) = v j := by
    rw [Submodule.powersAwayEval_powersLinearForm]
    exact dif_neg j.2
  have key : W.toScheme.isoSpec.inv ≫ g =
      Spec.map φ' ≫ e.hom ≫ (p ∣_ U) ≫ (ProjectiveSpace.standardOpenIso n _ j₀).hom := by
    rw [hg, he, AffineSpace.comp_homOfVector, ← Spec.map_comp]
    congr 1
    · congr 1
      ext c
      exact (φ.commutes c).symm
    · funext j
      simp only [Function.comp_apply]
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      congr 1
      exact (hφ j).symm
  have key' : W.toScheme.isoSpec.inv ≫ W.ι ≫ i =
      Spec.map φ' ≫ e.hom ≫ (p ⁻¹ᵁ U).ι ≫ p := by
    have k1 : W.toScheme.isoSpec.inv ≫ (i ∣_ U) = Spec.map φ' ≫ e.hom ≫ (p ∣_ U) := by
      rw [← cancel_mono (ProjectiveSpace.standardOpenIso n (Spec (.of k)) j₀).hom]
      simpa only [Category.assoc, g] using key
    have k2 := congrArg (· ≫ U.ι) k1
    simpa only [Category.assoc, morphismRestrict_ι] using k2
  -- `φ` is bijective: injective by construction, surjective since `i` is a closed immersion.
  have hsurj : Function.Surjective φ := by
    have hv : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (R := k) v).toRingHom)) := by
      have h1 := AffineSpace.homOfVector_SpecMap_eq (R := k) v
      have h2 : Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom) =
          W.toScheme.isoSpec.inv ≫ g ≫ (AffineSpace.SpecIso _ (.of k)).hom := by
        rw [← Category.assoc, hg, h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [h2]
      infer_instance
    intro r
    obtain ⟨P, rfl⟩ := surjective_of_isClosedImmersion_SpecMap _ r
    refine ⟨MvPolynomial.aeval (fun j : {j : n // j ≠ j₀} ↦
      Away.mk V.powersGrading (hl j₀) 1 (l j.1) (by simpa using hl j.1)) P, ?_⟩
    change φ.comp (MvPolynomial.aeval _) P = MvPolynomial.aeval v P
    rw [MvPolynomial.comp_aeval]
    congr 1
    funext j
    exact hφ j
  have : IsIso φ' := (ConcreteCategory.isIso_iff_bijective φ').mpr
    ⟨Submodule.powersAwayEval_injective k ha, hsurj⟩
  -- The two closed subschemes have the same image.
  have hrange : Set.range i = Set.range p := by
    have hcl_i : IsClosed (Set.range i) := i.isClosedEmbedding.isClosed_range
    have hcl_p : IsClosed (Set.range p) := p.isClosedEmbedding.isClosed_range
    refine subset_antisymm ?_ ?_
    · have hξ : i (genericPoint X) ∈ Set.range p := by
        have hx : genericPoint X = W.ι ⟨genericPoint X, hj₀⟩ := rfl
        have : (W.toScheme.isoSpec.hom ≫ W.toScheme.isoSpec.inv ≫ W.ι ≫ i)
            ⟨genericPoint X, hj₀⟩ = i (genericPoint X) := by
          simp [hx]
        rw [← this, key']
        exact ⟨_, rfl⟩
      rintro _ ⟨x, rfl⟩
      exact ((genericPoint_specializes x).map i.continuous).mem_closed hcl_p hξ
    · have hl0 : l j₀ ≠ 0 := by
        intro h
        have := congrArg (fun F : V.powersAlgebra ↦ (F : Polynomial Γ(W.toScheme, ⊤)).coeff 1) h
        simp [l, Submodule.powersLinearForm, ha] at this
      have hirr : l j₀ ∈ HomogeneousIdeal.irrelevant V.powersGrading := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
          DirectSum.decompose_of_mem_ne _ (hl j₀) one_ne_zero]
      let x₀ : ProjectiveSpectrum V.powersGrading :=
        ⟨⊥, by simpa using Ideal.isPrime_bot, fun h ↦ hl0 (by
          have h' := h hirr
          rwa [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h')⟩
      have hx₀ : x₀ ∈ p ⁻¹ᵁ U := by
        rw [Proj.linearProjection_preimage_standardOpen, Proj.mem_basicOpen]
        exact hl0
      have hpx₀ : p x₀ ∈ Set.range i := by
        have : ((inv (Spec.map φ') ≫ e.inv) ≫ Spec.map φ' ≫ e.hom ≫ (p ⁻¹ᵁ U).ι ≫ p)
            ⟨x₀, hx₀⟩ = p x₀ := by
          simp
        rw [← this, ← key']
        exact ⟨_, rfl⟩
      rintro _ ⟨x, rfl⟩
      have hsp : x₀ ⤳ x := specializes_iff_mem_closure.mpr
        ((ProjectiveSpectrum.le_iff_mem_closure _ x₀ x).mp
          ((ProjectiveSpectrum.as_ideal_le_as_ideal _ x₀ x).mp bot_le))
      exact (hsp.map p.continuous).mem_closed hcl_i hpx₀
  -- Conclusion.
  obtain ⟨e', he'⟩ := IsClosedImmersion.exists_iso_of_range_eq i p hrange
  refine ⟨V.powersAlgebra, inferInstance, inferInstance, V.powersGrading, inferInstance, hstd,
    inferInstance, e', ?_⟩
  rw [← Proj.linearProjection_over V.powersGrading l hl hcov, ← Category.assoc, he',
    Scheme.Hom.comp_over]

/-- **A projective curve admits a finite morphism to the projective line**: if `k` is an
infinite field and `X` is an integral closed subscheme of `ℙ(n; Spec k)` of dimension one,
then there is a finite morphism `X ⟶ ℙ¹_k` over `k`. Writing `X ≅ Proj S` with `S` a
standard graded domain, it is the linear projection `π_{l₀,l₁}` for linear forms
`l₀, l₁ ∈ S₁` without common zero
(blueprint: `lem-pc-projective-curve-finite-projection`). -/
theorem exists_isFinite_toProjectiveLine {k : Type u} [Field k] [Infinite k] {n : Type u}
    [Finite n] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hdim : topologicalKrullDim X = 1) :
    ∃ π : X ⟶ ProjectiveLine (Spec (.of k)),
      IsFinite π ∧ π ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = X ↘ Spec (.of k) := by
  obtain ⟨S, _, _, 𝒜, _, hstd, _, e, he⟩ := exists_isStandard_iso_proj X i
  have hdim' : topologicalKrullDim (ProjectiveSpectrum 𝒜) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm.trans hdim
  obtain ⟨l₀, h₀, l₁, h₁, hcov⟩ := GradedAlgebra.IsStandard.exists_basicOpen_sup_eq_top hdim'
  have := Proj.isFinite_linearPairProjection h₀ h₁ hcov
  refine ⟨e.hom ≫ Proj.linearPairProjection h₀ h₁ hcov, inferInstance, ?_⟩
  rw [Category.assoc, Proj.linearPairProjection_over, he]

end AlgebraicGeometry
