/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothUniformizer
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorGenericPoint
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparable
public import WeilConjectures.AlgebraicGeometry.NormalizationReduction
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteGeneric
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorUniversalHomeomorphism
public import WeilConjectures.TraceFormula.Specialization.ResidueConstantCase

/-!

# The constant case of generic vanishing along a divisor, with coefficients `𝔽_E`

Let `X` be normal of finite type over `k`, `Z = V(h)` a principal divisor, `j : X ∖ Z ⟶ X` and `ζ`
a generic point of `Z`. Then `Le^* Ψ_X(j_! 𝔽_E)` vanishes near `ζ`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_residueField`, blueprint
`det-sp-generic-divisor-constant`).

Over a perfect field `k`, the local ring `𝒪_{X,ζ}` is a discrete valuation ring, so `X` is
smooth at `ζ` and some uniformizer defines a smooth morphism to `𝔸¹_k` near `ζ`
(`exists_smooth_polyAffine_irreducible_germ`); the constant case with such a chart is
`nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_uniformizer`.

## Unfinished

The case of an imperfect field `k`,
`ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_not_perfectField`,
is `sorry`ed: there `X` need not be smooth at `ζ` (for instance `X = 𝔸¹_{k(a^{1/p})}`), and the
blueprint assumes `k` algebraically closed. See its docstring for the planned route.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **The constant case over a perfect field** (blueprint `det-sp-generic-divisor-constant`, `k`
perfect): the local ring at a generic point `ζ` of the divisor `V(h)` of the normal scheme `X`
is a discrete valuation ring, so a uniformizer near `ζ` is a smooth morphism to `𝔸¹_k`
(`exists_smooth_polyAffine_irreducible_germ`), and the constant case with a smooth uniformizer
applies. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_perfectField [PerfectField k]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) := by
  have := hX.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have := (hX.2 (I.subschemeι ζ)).1
  have := (hX.2 (I.subschemeι ζ)).2
  have : IsDiscreteValuationRing (X.left.presheaf.stalk (I.subschemeι ζ)) :=
    IsDiscreteValuationRing.of_maximalIdeal_mem_minimalPrimes_span_singleton
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral X.left (U := ⊤) _ trivial)).2 hh)
      (maximalIdeal_stalk_mem_minimalPrimes (subschemeι_mem_zeroLocus hI ζ)
        (eq_of_specializes_subschemeι hI ζ hζ))
  obtain ⟨W₀, hW₀, f₀, hsm, hf₀⟩ := exists_smooth_polyAffine_irreducible_germ X (I.subschemeι ζ)
  have := hsm
  exact nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_uniformizer k' hX hh hI ζ hζ E W₀
    hW₀ f₀ hf₀

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- **The constant case after a universal homeomorphism onto a normal scheme, over a perfect
field** (blueprint `det-sp-generic-divisor-constant`): let `X₀` be separated of finite type over a
perfect field `k`, with a universal homeomorphism `π : X₀ ⟶ Y` onto a normal scheme `Y`, and
`Z₀ = V(h₀)` with `h₀` not nilpotent. Then `Le^* Ψ_{X₀}(j_! 𝔽_E)` vanishes near every generic
point `ζ₀` of `Z₀`. The normalization `ν : X₀' ⟶ X₀` of the reduction of `X₀` is finite and
normal (`Scheme.exists_isNormalScheme_isFinite_of_irreducibleSpace`); it is a universal
homeomorphism, since `X₀' ⟶ Y` is integral and universally injective on a dense open
(`Scheme.Hom.isUniversalHomeomorphism_of_universallyInjective_comp`). The constant case over the
perfect field `k` holds at the generic points of `ν⁻¹ Z₀`, and descends along `ν`
(`nearbyCyclesVanishNear_lowerShriek_unit_of_isUniversalHomeomorphism`). -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_isUniversalHomeomorphism
    [PerfectField k] {X₀ : Over (Spec (.of k))} [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] {Y : Scheme.{u}} (hY : IsNormalScheme Y)
    (π : X₀.left ⟶ Y) [IsUniversalHomeomorphism π] {h₀ : Γ(X₀.left, ⊤)}
    (hh₀ : (X₀.left.basicOpen h₀ : Set X₀.left).Nonempty) {I₀ : X₀.left.IdealSheafData}
    (hI₀ : I₀ = IdealSheafData.ofIdealTop (Ideal.span {h₀}))
    (ζ₀ : (centre X₀ I₀).left) (hζ₀ : closure {ζ₀} ∈ irreducibleComponents (centre X₀ I₀).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    nearbyCyclesVanishNear X₀ I₀ k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))
      ζ₀ ((D(((overRestrictι X₀ I₀.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) := by
  have := hY.1
  have : IrreducibleSpace X₀.left :=
    (IsUniversalHomeomorphism.homeomorph π).symm.surjective.irreducibleSpace
      (IsUniversalHomeomorphism.homeomorph π).symm.continuous
  obtain ⟨X'', f, _, W, _, t, _, hX'', htf⟩ :=
    Scheme.exists_isNormalScheme_isFinite_of_irreducibleSpace X₀.left X₀.hom
  have := hX''.1
  let X' : Over (Spec (.of k)) := Over.mk (f ≫ X₀.hom)
  let ν : X' ⟶ X₀ := Over.homMk f rfl
  have : LocallyOfFiniteType X'.hom := inferInstanceAs (LocallyOfFiniteType (f ≫ X₀.hom))
  have : QuasiCompact X'.hom := inferInstanceAs (QuasiCompact (f ≫ X₀.hom))
  have : IsSeparated X'.hom := inferInstanceAs (IsSeparated (f ≫ X₀.hom))
  have : IsFinite ν.left := ‹IsFinite f›
  -- `ν` is a universal homeomorphism
  have : IsUniversalHomeomorphism ν.left := by
    have : IrreducibleSpace X₀.left.nilradical.subscheme :=
      (IsUniversalHomeomorphism.homeomorph X₀.left.nilradical.subschemeι).symm.surjective.irreducibleSpace
        (IsUniversalHomeomorphism.homeomorph X₀.left.nilradical.subschemeι).symm.continuous
    have : IsDominant W.ι :=
      Opens.isDominant_ι (W.isOpen.dense (Set.nonempty_of_nonempty_subtype))
    have hc : t ≫ f ≫ π = W.ι ≫ X₀.left.nilradical.subschemeι ≫ π := by
      rw [← Category.assoc, htf, Category.assoc]
    have : IsDominant (t ≫ f ≫ π) := by
      rw [hc]
      infer_instance
    have : IsDominant (f ≫ π) := IsDominant.of_comp t (f ≫ π)
    have : UniversallyInjective (t ≫ f ≫ π) := by
      rw [hc]
      infer_instance
    have : IsUniversalHomeomorphism (f ≫ π) :=
      Scheme.Hom.isUniversalHomeomorphism_of_universallyInjective_comp (f ≫ π)
        (fun y ↦ (hY.2 y).2) t
    exact IsUniversalHomeomorphism.of_comp f π
  refine nearbyCyclesVanishNear_lowerShriek_unit_of_isUniversalHomeomorphism _ k' ν I₀ ζ₀
    fun ζ' hζ' ↦ ?_
  have hζ'g := closure_singleton_mem_irreducibleComponents_of_centreMap ν I₀ hζ' hζ₀
  have hI' : I₀.comap ν.left = IdealSheafData.ofIdealTop (Ideal.span {ν.left.appTop h₀}) := by
    rw [hI₀, IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
  have hh' : ν.left.appTop h₀ ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hh₀
    obtain ⟨y, rfl⟩ := ν.left.surjective x
    have hy : y ∈ ν.left ⁻¹ᵁ X₀.left.basicOpen h₀ := hx
    rw [Scheme.preimage_basicOpen] at hy
    change y ∈ X'.left.basicOpen (ν.left.appTop h₀) at hy
    rw [h0, Scheme.basicOpen_zero] at hy
    exact hy
  exact nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_perfectField k' hX'' hh' hI' ζ'
    hζ'g E

/-- **The constant case over an imperfect field** (blueprint `det-sp-generic-divisor-constant`,
which assumes `k` algebraically closed). Let `K` be an algebraic closure of `k'`, purely
inseparable over `k'`, and `K₀ ⊆ K` the perfect closure of `k`. The base change
`π : X₀ = X ×_k K₀ ⟶ X` is a universal homeomorphism, so `X₀` satisfies the constant case over the
perfect field `K₀` with the trait `Spec K⟦t⟧`
(`nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_isUniversalHomeomorphism`), and the
vanishing descends to `X` by the invariance of nearby cycles under change of trait
(`nearbyCyclesVanishNear_of_overBaseChange`); `Lπ^* j_! 𝔽_E ≅ j₀_! 𝔽_E`
(`nonempty_leftDerivedUpperStar_openImmersionLowerShriek_unit_iso`). -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_not_perfectField
    (hk : ¬ PerfectField k)
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) := by
  have := hX.1
  -- the fields `K = (k')^alg` and `K₀ = k^perf ⊆ K`
  let K := AlgebraicClosure k'
  let K₀ := perfectClosure k K
  have : Fact (ringChar K).Prime := ⟨Algebra.ringChar_eq k' K ▸ Fact.out⟩
  have : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k' K ▸ Fact.out⟩
  -- the base change `X₀ = X ×_k K₀`
  let X₀ : Over (Spec (.of K₀)) :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))).obj X
  let π : X₀.left ⟶ X.left := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))
  have : IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap k K₀))) :=
    Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism (A := k) (B := K₀)
  have : IsUniversalHomeomorphism π := inferInstanceAs (IsUniversalHomeomorphism
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))
  have : LocallyOfFiniteType X₀.hom := inferInstanceAs (LocallyOfFiniteType
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))
  have : QuasiCompact X₀.hom := inferInstanceAs (QuasiCompact
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))
  have : IsSeparated X₀.hom := inferInstanceAs (IsSeparated
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K₀)))))
  have : IsLocallyNoetherian X₀.left := LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  -- the divisor `Z₀ = V(π^* h)` and the generic point `ζ₀` over `ζ`
  have hI₀ : I.comap π = IdealSheafData.ofIdealTop (Ideal.span {π.appTop h}) := by
    rw [hI, IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
  have hh₀ : (X₀.left.basicOpen (π.appTop h) : Set X₀.left).Nonempty := by
    have hne : X.left.basicOpen h ≠ ⊥ := fun h0 ↦ hh ((Scheme.basicOpen_eq_bot_iff h).1 h0)
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    obtain ⟨y, rfl⟩ := π.surjective x
    refine ⟨y, ?_⟩
    have hy : y ∈ π ⁻¹ᵁ X.left.basicOpen h := hx
    rwa [Scheme.preimage_basicOpen] at hy
  let πZ : (centre X₀ (I.comap π)).left ⟶ (centre X I).left :=
    IdealSheafData.subschemeMap _ _ π (I.le_map_comap π)
  have hπZ : IsPullback πZ (I.comap π).subschemeι I.subschemeι π := by
    have := (I.isPullback_comap π).flip
    rwa [IdealSheafData.comapIso_hom_snd] at this
  have : IsUniversalHomeomorphism πZ := MorphismProperty.of_isPullback hπZ.flip ‹_›
  let e := IsUniversalHomeomorphism.homeomorph πZ
  have hζ₀ : closure {e.symm ζ} ∈ irreducibleComponents (centre X₀ (I.comap π)).left := by
    have h₁ := preimage_mem_irreducibleComponents hζ e.isOpenEmbedding
      ⟨ζ, subset_closure (Set.mem_singleton ζ), e.surjective ζ⟩
    have hs : e ⁻¹' {ζ} = {e.symm ζ} := by
      ext x
      exact ⟨fun hx ↦ by rw [← Set.mem_singleton_iff.1 hx, e.symm_apply_apply],
        fun hx ↦ by rw [Set.mem_singleton_iff.1 hx, Set.mem_preimage, e.apply_symm_apply]; rfl⟩
    rwa [e.preimage_closure, hs] at h₁
  sorry

/-- **The constant case of generic vanishing along a divisor, with coefficients `𝔽_E`** (blueprint
`det-sp-generic-divisor-constant`): `Le^* Ψ_X(j_! 𝔽_E)` vanishes near a generic point `ζ` of the
divisor `V(h)` of a normal scheme `X`. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) := by
  by_cases hk : PerfectField k
  · exact nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_perfectField k' hX hh hI ζ hζ E
  · exact nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_not_perfectField k' hk hX hh hI
      ζ hζ E

end AlgebraicGeometry.ProEtale.CondensedRing
