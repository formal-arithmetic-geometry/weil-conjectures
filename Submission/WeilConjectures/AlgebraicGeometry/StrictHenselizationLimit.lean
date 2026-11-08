/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationLimitAux
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationLimitDimension
public import Submission.WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField
public import Submission.WeilConjectures.RingTheory.HenselianSepClosedSubfield
public import Submission.WeilConjectures.RingTheory.KrullDimensionAdjoinTranscendental
public import Submission.WeilConjectures.RingTheory.FiniteTypeSubalgebraUnion
public import Submission.WeilConjectures.AlgebraicGeometry.ClosedPointResidueField
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.SupportDimension

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The strict henselization at a non-closed point as a limit of smaller schemes

Let `K` be a field, `X` a scheme of finite type over `K` and `s : Spec Ω ⟶ X` a geometric point
lying over a point `x` with `trdeg_K κ(x) > 0`, equivalently a non-closed point `x`. Let
`X' = Spec 𝒪^{sh}_{X,s}` be the strict localization (`AlgebraicGeometry.Scheme.strictLocalization`;
recall that it is also the limit of the affine pointed étale neighbourhoods of `s`,
`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConeOver`). Then there is a separably closed
field `L` over `K` such that `X'` is an `L`-scheme and a cofiltered limit, with affine transition
maps, of affine schemes `X_i` of finite type over `L` with `dim X_i < dim X`
(blueprint `lem-kun-0f0u`, Stacks 0F0U).

## References

- Stacks Project, Lemma 0F0U, <https://stacks.math.columbia.edu/tag/0F0U>
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme

/-- Blueprint `lem-kun-0f0u`: the strict henselization as a limit.

Let `K` be a field, `aX : X ⟶ Spec K` of finite type and `s : Spec Ω ⟶ X` a geometric point
(`Ω` separably closed) lying over a non-closed point `x` of `X` (for `X` of finite type over `K`
this is equivalent to `trdeg_K κ(x) > 0`). Then there are

* a separably closed field `L` over `K` and a morphism `ℓ : X' ⟶ Spec L` from the strict
  localization `X' = Spec 𝒪^{sh}_{X,s}`, compatible with `X' ⟶ X ⟶ Spec K` and
  `Spec L ⟶ Spec K`;
* a small cofiltered category `I`, a diagram `D : I ⥤ Scheme` and a limit cone `π` from `X'`
  to `D`;
* structure morphisms `q i : D i ⟶ Spec L`, locally of finite type, compatible with the
  transition maps and with `ℓ`,

such that every `D i` is affine, all transition maps are affine, and `dim D i < dim X`. -/
@[stacks 0F0U]
theorem exists_isLimit_strictLocalization_of_not_isClosed {K Ω : Type u} [Field K] [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] (s : Spec (.of Ω) ⟶ X) (hs : ¬ IsClosed {s (IsLocalRing.closedPoint Ω)}) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (_ : Algebra K L)
      (ℓ : strictLocalization s ⟶ Spec (.of L))
      (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (π : (Functor.const I).obj (strictLocalization s) ⟶ D)
      (q : ∀ i, D.obj i ⟶ Spec (.of L)),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = strictLocalizationToBase s ≫ aX ∧
      (∀ i, IsAffine (D.obj i)) ∧ (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      (∀ i, LocallyOfFiniteType (q i)) ∧ (∀ i, π.app i ≫ q i = ℓ) ∧
      (∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f ≫ q j = q i) ∧
      ∀ i, topologicalKrullDim (D.obj i) < topologicalKrullDim X := by
  classical
  let κR : K →+* strictHenselization s := (Spec.preimage (strictLocalizationToBase s ≫ aX)).hom
  let : Algebra K (strictHenselization s) := κR.toAlgebra
  let : Algebra K Ω := (Spec.preimage (s ≫ aX)).hom.toAlgebra
  obtain ⟨N₀, c₀, hc₀⟩ := exists_transcendental_pt aX hs
  let ev : strictHenselization s →ₐ[K] Ω :=
    { (strictHenselizationEval s).hom with
      commutes' k := congr($(preimage_comp_strictHenselizationEval aX) k) }
  let tR := N₀.ι c₀
  have hunit (g : nonZeroDivisors K[X]) : IsUnit (aeval tR (g : K[X])) := by
    refine isUnit_of_strictHenselizationEval_ne_zero fun h ↦
      hc₀ ⟨g, nonZeroDivisors.ne_zero g.2, ?_⟩
    have hev : ev tR = N₀.pt c₀ := SpecPointedEtaleNeighborhood.strictHenselizationEval_ι N₀ c₀
    have : ev (aeval tR (g : K[X])) = 0 := h
    rwa [← Polynomial.aeval_algHom_apply, hev] at this
  let F := FractionRing K[X]
  let φ : F →+* strictHenselization s :=
    IsLocalization.lift (M := nonZeroDivisors K[X]) (g := (aeval tR).toRingHom) hunit
  have hφ (p : K[X]) : φ (algebraMap K[X] F p) = aeval tR p := IsLocalization.lift_eq _ _
  obtain ⟨L, _, _, ψ, ρ, hψρ⟩ := HenselianLocalRing.exists_isSepClosed_factor φ
  let : Algebra K L := (ρ.comp ((algebraMap K[X] F).comp Polynomial.C)).toAlgebra
  let : Algebra L (strictHenselization s) := ψ.toAlgebra
  have hψK (k : K) : ψ (algebraMap K L k) = κR k := by
    change (ψ.comp ρ) _ = _
    rw [hψρ, RingHom.comp_apply, hφ, aeval_C]
    rfl
  have : IsScalarTower K L (strictHenselization s) :=
    .of_algebraMap_eq fun k ↦ (hψK k).symm
  let t : L := ρ (algebraMap K[X] F Polynomial.X)
  have hψt : algebraMap L (strictHenselization s) t = tR := by
    change (ψ.comp ρ) _ = _
    rw [hψρ, hφ, aeval_X]
  have ht : Transcendental K t := by
    rintro ⟨p, hp, hpt⟩
    have h := hunit ⟨p, mem_nonZeroDivisors_of_ne_zero hp⟩
    rw [← hψt] at h
    have : algebraMap L _ (aeval t p) = aeval (algebraMap L (strictHenselization s) t) p :=
      (Polynomial.aeval_algebraMap_apply _ _ _).symm
    rw [← this, hpt, map_zero] at h
    exact not_isUnit_zero h
  -- the index set: the `L`-subalgebras generated by neighbourhoods containing `tR`
  let Dset : Set (Subalgebra L (strictHenselization s)) :=
    {D | ∃ N : SpecPointedEtaleNeighborhood s, tR ∈ Set.range N.ι ∧
      D = Algebra.adjoin L (Set.range N.ι)}
  have hdir : DirectedOn (· ≤ ·) Dset := by
    rintro _ ⟨N₁, h₁, rfl⟩ _ ⟨N₂, -, rfl⟩
    obtain ⟨N₃, h₁₃, h₂₃⟩ := N₁.exists_range_subset N₂
    exact ⟨_, ⟨N₃, h₁₃ h₁, rfl⟩, Algebra.adjoin_mono h₁₃, Algebra.adjoin_mono h₂₃⟩
  have hcov (r : strictHenselization s) : ∃ D ∈ Dset, r ∈ D := by
    obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 2 ![r, tR]
    exact ⟨_, ⟨N, by simpa using hN 1, rfl⟩, Algebra.subset_adjoin (by simpa using hN 0)⟩
  have hne : Dset.Nonempty := by
    obtain ⟨D, hD, -⟩ := hcov 0
    exact ⟨D, hD⟩
  have : IsFiltered Dset := Subalgebra.isFiltered_of_directedOn hdir hne
  have hdimX := topologicalKrullDim_lt_top_of_finiteType aX
  have hD (D : Subalgebra L (strictHenselization s)) (hD : D ∈ Dset) :
      Algebra.FiniteType L D ∧ ringKrullDim D + 1 ≤ topologicalKrullDim X := by
    obtain ⟨N, ⟨c, hc⟩, rfl⟩ := hD
    let : Algebra K N.R := (Spec.preimage (N.hom ≫ aX)).hom.toAlgebra
    have : Algebra.FiniteType K N.R := N.finiteType_preimage aX
    let ιN : N.R →ₐ[K] strictHenselization s :=
      { N.ι.hom with commutes' k := congr($(N.preimage_comp_ι aX) k) }
    refine ⟨Algebra.finiteType_adjoin_range ιN, ?_⟩
    refine (ringKrullDim_adjoin_range_add_one_le ιN ht (c := c) (hc.trans hψt.symm)).trans ?_
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_le_of_locallyQuasiFinite N.hom
  let c := Scheme.Spec.mapCone (Subalgebra.cocone Dset).op
  refine ⟨L, inferInstance, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom ψ),
    Dsetᵒᵖ, inferInstance, inferInstance, (Subalgebra.diagram Dset).op ⋙ Scheme.Spec, c.π,
    fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap L i.unop.1)),
    ⟨isLimitOfPreserves Scheme.Spec (Subalgebra.isColimitCocone hdir hcov).op⟩, ?_,
    fun i ↦ inferInstanceAs (IsAffine (Spec _)),
    fun i j f ↦ inferInstanceAs (IsAffineHom (Spec.map _)), fun i ↦ ?_, fun i ↦ ?_, fun i j f ↦ ?_,
    fun i ↦ ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : ψ.comp (algebraMap K L) = κR := RingHom.ext hψK
    rw [this, CommRingCat.ofHom_hom, Spec.map_preimage]
  · have := (hD _ i.unop.2).1
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr this)
  · exact (Spec.map_comp (CommRingCat.ofHom (algebraMap L i.unop.1))
      (CommRingCat.ofHom i.unop.1.val.toRingHom)).symm.trans rfl
  · exact (Spec.map_comp (CommRingCat.ofHom (algebraMap L j.unop.1))
      (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f.unop)).toRingHom)).symm.trans rfl
  · have h := (hD _ i.unop.2).2
    have hnt : ringKrullDim i.unop.1 ≠ ⊥ :=
      ne_bot_of_le_ne_bot WithBot.coe_ne_bot ringKrullDim_nonneg_of_nontrivial
    change topologicalKrullDim (PrimeSpectrum i.unop.1) < _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnt
    rw [← hm] at h ⊢
    induction m using ENat.recTopCoe with
    | top =>
      refine absurd (lt_of_le_of_lt h hdimX) ?_
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      exact lt_irrefl _
    | coe n =>
      refine lt_of_lt_of_le ?_ h
      exact_mod_cast Nat.lt_succ_self n

end AlgebraicGeometry.Scheme
