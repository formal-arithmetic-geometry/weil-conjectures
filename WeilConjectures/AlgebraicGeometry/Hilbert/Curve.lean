/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Hilbert.Representability
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Hilbert schemes of curves

Let `f : X ⟶ S` be a separated smooth morphism of relative dimension `1`. A closed subscheme of
`X_T` which is finite locally free over `T` is a relative effective Cartier divisor
(`AlgebraicGeometry.Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite`), and such
divisors can be added, by multiplying their ideals. When the Hilbert functors `Hilb^d_{X/S}` are
representable, by schemes `H_d`, this gives addition morphisms `H_d ×[S] X ⟶ H_{d + 1}`, finite
locally free of degree `d + 1`, which show that `H_d` is smooth of relative dimension `d` over
`S`.

For a geometrically integral smooth proper curve `X` over a field `k` all Hilbert functors are
representable, and `H_d` is a smooth proper geometrically integral `k`-scheme of dimension `d`,
whose `k'`-points are the effective Cartier divisors of degree `d` on `X_{k'}`, and which carries
addition morphisms `H_{d₁} ×[k] H_{d₂} ⟶ H_{d₁ + d₂}`.

## Main statements

- `AlgebraicGeometry.IsHilbertSubscheme.mul`: the sum of two finite locally free divisors.
- `AlgebraicGeometry.exists_addition_hilbertPresheaf`: the addition morphism
  `H_d ×[S] X ⟶ H_{d + 1}` (blueprint `lem-pc-hilb-addition`).
- `AlgebraicGeometry.smoothOfRelativeDimension_of_representableBy_hilbertPresheaf`: `H_d` is
  smooth of relative dimension `d` (blueprint `lem-pc-hilb-smooth`).
- `AlgebraicGeometry.isRelativeEffectiveCartier_universal_hilbertPresheaf`: the universal
  divisor and its line bundle (blueprint `lem-pc-universal-divisor`).
- `AlgebraicGeometry.hilbertPresheaf_curve_representable`,
  `AlgebraicGeometry.hilbertPresheaf_curve_points`,
  `AlgebraicGeometry.hilbertPresheaf_curve_add`: the Hilbert schemes of a smooth proper curve
  (blueprint `sk-thm-picard-hilb-curves`, `thm-pc-hilb-curves`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

section Relative

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The underlying ideal sheaf of the element of `Hilb^d_{X/S}(T')` obtained by base change
along `φ : T' ⟶ T` is the pullback of the ideal sheaf along the base-change map. -/
@[simp]
lemma hilbertPresheaf_map_val {d : ℕ} {T T' : Over S} (φ : T' ⟶ T)
    (I : (hilbertPresheaf f d).obj (op T)) :
    ((hilbertPresheaf f d).map φ.op I).1 = I.1.comap (baseChangeMap f φ) :=
  rfl

/-- The point of `Hilb^d_{X/S}` classified by a composite `φ ≫ h` is the pullback of the point
classified by `h` along the base-change map of `φ`. -/
lemma hilbertPresheaf_homEquiv_comp_val {d : ℕ} {H : Over S}
    (e : (hilbertPresheaf f d).RepresentableBy H) {T T' : Over S} (φ : T' ⟶ T) (h : T ⟶ H) :
    (e.homEquiv (φ ≫ h)).1 = (e.homEquiv h).1.comap (baseChangeMap f φ) := by
  rw [e.homEquiv_comp]
  rfl

/-- The empty subscheme `⊤` lies in `Hilb^0_{X/S}(T)`. -/
lemma isHilbertSubscheme_top {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S) :
    IsHilbertSubscheme f 0 T ⊤ :=
  ⟨inferInstance, inferInstance, inferInstance, fun t ↦ Scheme.Hom.finrank_eq_zero_of_isEmpty _ t⟩

/-- The only element of `Hilb^0_{X/S}(T)` is the empty subscheme `⊤`. -/
lemma IsHilbertSubscheme.eq_top_of_zero {X S : Scheme.{u}} {f : X ⟶ S} {T : Over S}
    {I : (pullback f T.hom).IdealSheafData} (hI : IsHilbertSubscheme f 0 T I) : I = ⊤ := by
  obtain ⟨_, _, _, h⟩ := hI
  have : IsEmpty I.subscheme := ⟨fun x ↦ by
    simpa [h] using Scheme.Hom.one_le_finrank_map (I.subschemeι ≫ pullback.snd f T.hom) x⟩
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, ← SetLike.coe_set_eq,
    ← Scheme.IdealSheafData.range_subschemeι]
  simp [Set.range_eq_empty]

/-- `Hilb^0_{X/S}(T)` has at most one element. -/
instance hilbertPresheaf_zero_subsingleton {X S : Scheme.{u}} (f : X ⟶ S) (T : (Over S)ᵒᵖ) :
    Subsingleton ((hilbertPresheaf f 0).obj T) :=
  ⟨fun I J ↦ Subtype.ext (I.2.eq_top_of_zero.trans J.2.eq_top_of_zero.symm)⟩

/-- **The sum of two finite locally free divisors.** Let `f : X ⟶ S` be smooth of relative
dimension `1` and let `D₁, D₂ ⊆ X_T` be closed subschemes, with ideals `I₁` and `I₂`, finite
locally free of degrees `d₁` and `d₂` over `T`. Then `D₁ + D₂`, with ideal `I₁ * I₂`, is finite
locally free of degree `d₁ + d₂` over `T`.

Both are relative effective Cartier divisors by the Cartier criterion; locally `D₁ + D₂` is cut
out by the product `v₁ v₂` of local equations, and the exact sequence
`0 ⟶ 𝒪/(v₁) ⟶ 𝒪/(v₁ v₂) ⟶ 𝒪/(v₂) ⟶ 0` (the first map is multiplication by the
non-zerodivisor `v₂`) shows that `𝒪_{D₁ + D₂}` is finite flat over `T` of rank `d₁ + d₂`.

(blueprint: `thm-pc-hilb-curves`, Step 3, and `lem-pc-hilb-addition`, Step 1) -/
theorem IsHilbertSubscheme.mul [SmoothOfRelativeDimension 1 f] {d₁ d₂ : ℕ} {T : Over S}
    {I₁ I₂ : (pullback f T.hom).IdealSheafData} (h₁ : IsHilbertSubscheme f d₁ T I₁)
    (h₂ : IsHilbertSubscheme f d₂ T I₂) : IsHilbertSubscheme f (d₁ + d₂) T (I₁ * I₂) :=
  sorry

/-- **The addition morphism on Hilbert schemes.** Let `f : X ⟶ S` be separated and smooth of
relative dimension `1`, and let `H` and `H'` represent `Hilb^d_{X/S}` and `Hilb^{d + 1}_{X/S}`.
There is a morphism `a : H ×[S] X ⟶ H'` over `S`, finite locally free of degree `d + 1`,
sending a pair `(Z, x)` of a point `Z` of `H` and a point `x` of `X` to `Z + Γ_x`, where
`Γ_x ⊆ X_T` is the graph of `x : T ⟶ X`, the kernel of `⟨x, 𝟙⟩ : T ⟶ X ×[S] T`.

The morphism `a` identifies `H ×[S] X` with the universal divisor over `H'`, since a divisor
`D` of degree `d + 1` containing the graph `Γ_x` is uniquely `D' + Γ_x` with `D'` of degree `d`.

(Stacks, Tag 0B9G; blueprint: `lem-pc-hilb-addition`) -/
theorem exists_addition_hilbertPresheaf [IsSeparated f] [SmoothOfRelativeDimension 1 f] (d : ℕ)
    (H H' : Over S) (e : (hilbertPresheaf f d).RepresentableBy H)
    (e' : (hilbertPresheaf f (d + 1)).RepresentableBy H') :
    ∃ a : pullback H.hom f ⟶ H'.left, a ≫ H'.hom = pullback.snd H.hom f ≫ f ∧
      IsFinite a ∧ Flat a ∧ LocallyOfFinitePresentation a ∧ (∀ t, a.finrank t = d + 1) ∧
      ∀ (T : Over S) (z : T ⟶ H) (x : T.left ⟶ X) (hx : x ≫ f = T.hom) (t : T ⟶ H'),
        t.left = pullback.lift z.left x (by rw [Over.w z, hx]) ≫ a →
          (e'.homEquiv t).1 = (e.homEquiv z).1 *
            (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom).ker :=
  sorry

/-- **Hilbert schemes of relative curves are smooth.** Let `f : X ⟶ S` be separated and smooth
of relative dimension `1`, such that all Hilbert functors `Hilb^e_{X/S}` are representable. Then
the scheme `H` representing `Hilb^d_{X/S}` is smooth of relative dimension `d` over `S`.

For `d = 0` and `d = 1` the representing schemes are `S` and `X`; then one inducts with the
addition morphism `H_d ×[S] X ⟶ H_{d + 1}` of `exists_addition_hilbertPresheaf`, which is
finite locally free of positive degree, hence faithfully flat, along which smoothness descends.

(Stacks, Tag 0B9H; blueprint: `lem-pc-hilb-smooth`) -/
theorem smoothOfRelativeDimension_of_representableBy_hilbertPresheaf [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (hrep : ∀ e, (hilbertPresheaf f e).IsRepresentable) (d : ℕ)
    (H : Over S) (e : (hilbertPresheaf f d).RepresentableBy H) :
    SmoothOfRelativeDimension d H.hom :=
  sorry

/-- **The universal divisor.** Let `f : X ⟶ S` be smooth of relative dimension `1`, and let `H`
represent `Hilb^d_{X/S}`. The universal closed subscheme `D_univ ⊆ X ×[S] H`, the point of
`Hilb^d_{X/S}(H)` classified by `𝟙 H`, is a relative effective Cartier divisor over `H`, and for
every point `h : T ⟶ H` the line bundle of the divisor `D_h ⊆ X_T` classified by `h` is the
pullback of `𝒪(D_univ)` along `X_T ⟶ X ×[S] H`.

For `T = Spec k` a rational point `[D]` of `H`, this says that `𝒪(D_univ)` restricts on the
fibre `{[D]} × X ≅ X` to `𝒪_X(D)`.

(Stacks, Tag 0B9J; blueprint: `lem-pc-universal-divisor`) -/
theorem isRelativeEffectiveCartier_universal_hilbertPresheaf [SmoothOfRelativeDimension 1 f]
    {d : ℕ} {H : Over S} (e : (hilbertPresheaf f d).RepresentableBy H) :
    (e.homEquiv (𝟙 H)).1.IsRelativeEffectiveCartier (pullback.snd f H.hom) ∧
      ∀ (T : Over S) (h : T ⟶ H), Nonempty ((e.homEquiv h).1.toModulesᵛ ≅
        (Scheme.Modules.pullback (baseChangeMap f h)).obj (e.homEquiv (𝟙 H)).1.toModulesᵛ) := by
  obtain ⟨hfin, hflat, hlfp, -⟩ := (e.homEquiv (𝟙 H)).2
  have hD : (e.homEquiv (𝟙 H)).1.IsRelativeEffectiveCartier (pullback.snd f H.hom) :=
    Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite _
  refine ⟨hD, fun T h ↦ ?_⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have hsq : IsPullback (baseChangeMap f h) (pullback.snd f T.hom) (pullback.snd f H.hom)
      h.left := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f H.hom)
    rw [Over.w h]
    simpa using IsPullback.of_hasPullback f T.hom
  obtain ⟨-, hiso⟩ := hD.comap_of_isPullback hsq
  have hh := hilbertPresheaf_homEquiv_comp_val f e h (𝟙 H)
  rw [Category.comp_id] at hh
  rwa [hh]

end Relative

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A geometrically integral smooth curve has a non-closed point, its generic point: otherwise
it would be a single point, of dimension `0`. -/
lemma exists_not_isClosed_singleton_of_smoothOfRelativeDimension_one
    [SmoothOfRelativeDimension 1 f] [GeometricallyIntegral f] :
    ∃ x : X, ¬ IsClosed ({x} : Set X) := by
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hdim := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mp inferInstance
  refine ⟨genericPoint X, fun h ↦ ?_⟩
  have huniv : ({genericPoint X} : Set X) = Set.univ := by
    rw [← h.closure_eq, (genericPoint_spec X).def]
  have : Subsingleton X := ⟨fun a b ↦ by
    have ha : a ∈ ({genericPoint X} : Set X) := huniv ▸ trivial
    have hb : b ∈ ({genericPoint X} : Set X) := huniv ▸ trivial
    exact ha.trans hb.symm⟩
  have : DiscreteTopology X := inferInstance
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at this
  exact absurd this (by norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- A closed point of a locally noetherian scheme whose local ring is a discrete valuation ring
has an affine neighbourhood on which its vanishing ideal is generated by a non-zerodivisor. -/
lemma exists_affineOpen_isRegularPrincipal_vanishingIdeal [IsLocallyNoetherian X] {Q : X}
    (hQ : IsClosed ({Q} : Set X)) [IsDomain (X.presheaf.stalk Q)]
    [IsDiscreteValuationRing (X.presheaf.stalk Q)] :
    ∃ U : X.affineOpens, Q ∈ U.1 ∧
      ((Scheme.IdealSheafData.vanishingIdeal ⟨{Q}, hQ⟩).ideal U).IsRegularPrincipal := by
  obtain ⟨U, hU, hQU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := Q) trivial
  let x : U := ⟨Q, hQU⟩
  set q := hU.primeIdealOf x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have := hU.isLocalization_stalk x
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨g, hg, π, hπ, h1, h2⟩ :=
    Ideal.exists_away_regularPrincipal_of_isDiscreteValuationRing q.asIdeal (X.presheaf.stalk Q)
  let F := X.presheaf.map (homOfLE (X.basicOpen_le g)).op
  let : Algebra Γ(X, U) Γ(X, X.basicOpen g) := F.hom.toAlgebra
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hU.isLocalization_of_eq_basicOpen _ _ rfl
  refine ⟨X.affineBasicOpen (U := ⟨U, hU⟩) g, ?_, ?_⟩
  · have : q ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hg
    have e : hU.fromSpec q = Q := hU.fromSpec_primeIdealOf x
    change Q ∈ X.basicOpen g
    rw [← e]
    exact this
  · rw [← Scheme.IdealSheafData.map_ideal_basicOpen (U := ⟨U, hU⟩)]
    have hJU : (Scheme.IdealSheafData.vanishingIdeal ⟨{Q}, hQ⟩).ideal ⟨U, hU⟩ = q.asIdeal := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      have : hU.fromSpec ⁻¹' {Q} = {q} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hy
          apply hU.fromSpec.isOpenEmbedding.injective
          rw [hy, hU.fromSpec_primeIdealOf]
        · rintro rfl; exact hU.fromSpec_primeIdealOf x
      erw [this]
      rw [PrimeSpectrum.vanishingIdeal_singleton]
    rw [hJU]
    have := Ideal.isRegularPrincipal_map_away (B := Γ(X, X.basicOpen g)) g _ π hπ h1 h2
    exact this

/-- A closed point of a scheme smooth of relative dimension one over a field has a local ring of
dimension `1`. -/
lemma ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one
    [SmoothOfRelativeDimension 1 f] {Q : X} (hQ : IsClosed ({Q} : Set X)) :
    ringKrullDim (X.presheaf.stalk Q) = 1 := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hle : ringKrullDim (X.presheaf.stalk Q) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim Q).trans
      (by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension f 1)
  have hne : Order.coheight Q ≠ 0 := by
    intro h0
    obtain ⟨U, hU, hQU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := Q) trivial
    let x : U := ⟨Q, hQU⟩
    set q := hU.primeIdealOf x with hq
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
    have := hU.isLocalization_stalk x
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hht : q.asIdeal.height = 0 := by
      have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (X.presheaf.stalk Q)
      rw [ringKrullDim_stalk_eq_coheight, h0] at h1
      exact_mod_cast h1.symm
    have hmin : q.asIdeal ∈ minimalPrimes Γ(X, U) := Ideal.height_eq_zero_iff.mp hht
    have hmax : q.asIdeal.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed x hQ
    -- `{q}` is open in `Spec Γ(X, U)`
    have hfin := minimalPrimes.finite_of_isNoetherianRing Γ(X, U)
    have hopen : IsOpen ({q} : Set (PrimeSpectrum Γ(X, U))) := by
      have : ({q} : Set (PrimeSpectrum Γ(X, U)))ᶜ =
          ⋃ p ∈ minimalPrimes Γ(X, U) \ {q.asIdeal}, PrimeSpectrum.zeroLocus (p : Set _) := by
        ext P
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_sdiff,
          PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, exists_prop]
        constructor
        · intro hP
          obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ P.asIdeal)
          refine ⟨p, ⟨hp, fun hpq ↦ hP ?_⟩, hpP⟩
          subst hpq
          exact (PrimeSpectrum.ext (hmax.eq_of_le P.2.ne_top hpP)).symm
        · rintro ⟨p, ⟨hp, hpq⟩, hpP⟩ rfl
          exact hpq (Set.mem_singleton_iff.mpr (le_antisymm hpP (hmin.2 hp.1 hpP)))
      rw [← isClosed_compl_iff, this]
      exact (hfin.sdiff).isClosed_biUnion fun p _ ↦ PrimeSpectrum.isClosed_zeroLocus _
    have hQopen : IsOpen ({Q} : Set X) := by
      have := hU.fromSpec.isOpenEmbedding.isOpenMap _ hopen
      rwa [Set.image_singleton, hU.fromSpec_primeIdealOf x] at this
    let V : X.Opens := ⟨{Q}, hQopen⟩
    have : SmoothOfRelativeDimension 1 (V.ι ≫ f) :=
      (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (V.ι ≫ f))
    have : Smooth (V.ι ≫ f) := SmoothOfRelativeDimension.smooth 1 _
    have : Subsingleton V := ⟨fun a b ↦ Subtype.ext
      ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)⟩
    let pt : V := ⟨Q, Set.mem_singleton Q⟩
    have : IrreducibleSpace V := by
      have h := isIrreducible_singleton (x := pt)
      rw [show ({pt} : Set V) = Set.univ from
        Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _] at h
      exact (irreducibleSpace_def _).mpr h
    have hdim := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq (V.ι ≫ f) 1).mp
      inferInstance
    have : DiscreteTopology V := inferInstance
    have := topologicalKrullDim_zero_of_discreteTopology V
    rw [hdim] at this
    exact absurd this (by norm_num)
  rw [ringKrullDim_stalk_eq_coheight] at hle ⊢
  have hle' : Order.coheight Q ≤ 1 := by exact_mod_cast hle
  exact_mod_cast le_antisymm hle' (Order.one_le_iff_ne_zero.mpr hne)

/-- **Closed points of a smooth curve are effective Cartier divisors.** On a smooth curve over a
field the local ring at a closed point `Q` is regular of dimension `1`, a discrete valuation
ring; a uniformizer generates the reduced ideal of `Q` near `Q` and is a non-zerodivisor there,
and away from `Q` the ideal is the unit ideal.

(blueprint: `thm-pc-hilb-curves`, Step 0, the divisor `[Q]`) -/
lemma isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one
    [SmoothOfRelativeDimension 1 f] {Q : X}
    (hQ : IsClosed ({Q} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨{Q}, hQ⟩).IsInvertible := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular X := IsRegular.of_smooth f
  have hdim1 := ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one f hQ
  have hR : ¬ IsField (X.presheaf.stalk Q) := fun h => by
    let := h.toField
    rw [ringKrullDim_eq_zero_of_field] at hdim1
    exact zero_ne_one hdim1
  have hfin : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk Q))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk Q)) = 1 := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk Q)).mp inferInstance
    rw [hdim1] at this
    exact_mod_cast this
  have : IsDiscreteValuationRing (X.presheaf.stalk Q) :=
    ((IsDiscreteValuationRing.TFAE _ hR).out 0 5).mpr hfin
  intro x
  by_cases hx : x = Q
  · subst hx
    exact exists_affineOpen_isRegularPrincipal_vanishingIdeal hQ
  · obtain ⟨U, hU, hxU, hUQ⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⟨{Q}ᶜ, hQ.isOpen_compl⟩) (x := x) hx
    refine ⟨⟨U, hU⟩, hxU, 1, one_mem _, ?_⟩
    rw [Ideal.span_singleton_one, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have : hU.fromSpec ⁻¹' {Q} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hy
      have : hU.fromSpec y ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨y, rfl⟩
      exact hUQ this hy
    erw [this]
    rw [PrimeSpectrum.vanishingIdeal_empty]

/-- **Finite sets of points of a curve lie in an affine open.** Let `X` be a geometrically
integral smooth proper curve over `k`. Every finite set of points of `X` is contained in an
affine open of `X`.

Choose a closed point `Q` outside the given set. The divisor `[Q]` is effective Cartier of
positive degree `[κ(Q) : k]`, so `𝒪_X(Q)` is ample
(`AlgebraicGeometry.Scheme.isAmple_of_degree_pos`, using `H⁰(X, 𝒪_X) = k`), and `X \ {Q}` is affine
(`AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple`).

(blueprint: `thm-pc-hilb-curves`, Step 0) -/
theorem exists_affineOpens_forall_mem_of_curve [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (t : Finset X) : ∃ U : X.affineOpens, ∀ x ∈ t, x ∈ U.1 := by
  classical
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx⟩ := exists_not_isClosed_singleton_of_smoothOfRelativeDimension_one f
  set C : Set X := {y | y ∈ t ∧ IsClosed ({y} : Set X)}
  have hCfin : C.Finite := (t.finite_toSet).subset fun y hy ↦ hy.1
  have hCcl : IsClosed C := by
    rw [← C.biUnion_of_singleton]
    exact hCfin.isClosed_biUnion fun y hy ↦ hy.2
  obtain ⟨Q, hQC, hQ⟩ := nonempty_inter_closedPoints (Z := Cᶜ) ⟨x, fun h ↦ hx h.2⟩
    hCcl.isOpen_compl.isLocallyClosed
  have hQt : Q ∉ t := fun h ↦ hQC ⟨h, hQ⟩
  set J := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨{Q}, hQ⟩
  have hJ : J.IsInvertible := isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one f hQ
  have hsupp : (J.support : Set X) = {Q} := by
    simp [J]
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have hf : X ↘ Spec (.of k) = f := rfl
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) := by rw [hf]; infer_instance
  have : IsProper (X ↘ Spec (.of k)) := by rw [hf]; infer_instance
  have : GeometricallyIntegral (X ↘ Spec (.of k)) := by rw [hf]; infer_instance
  have : Scheme.GlobalSectionsBijective k X :=
    Scheme.GlobalSectionsBijective.of_geometricallyIntegral
  -- the subscheme `[Q]` is finite and nonempty over `k`
  have hsub : Subsingleton J.subscheme := by
    refine ⟨fun a b ↦ J.subschemeι.isEmbedding.injective ?_⟩
    have ha : J.subschemeι a ∈ Set.range J.subschemeι := ⟨a, rfl⟩
    have hb : J.subschemeι b ∈ Set.range J.subschemeι := ⟨b, rfl⟩
    rw [J.range_subschemeι, hsupp] at ha hb
    exact ha.trans hb.symm
  have hne : Nonempty J.subscheme := by
    have : Q ∈ Set.range J.subschemeι := by rw [J.range_subschemeι, hsupp]; rfl
    obtain ⟨a, -⟩ := this
    exact ⟨a⟩
  have : LocallyQuasiFinite (J.subschemeι ≫ f) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  have : IsFinite (J.subschemeι ≫ f) := .of_isProper_of_locallyQuasiFinite _
  have hpos : 0 < (J.subschemeι ≫ f).finrankΓ := by
    have hfin := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)
      (f := J.subschemeι ≫ f)).mp inferInstance
    let := (J.subschemeι ≫ f).ΓAlgebra
    have : Module.Finite k Γ(J.subscheme, ⊤) := by
      have h2 : RingHom.Finite ((Scheme.ΓSpecIso (.of k)).inv ≫
          (J.subschemeι ≫ f).appTop).hom := by
        rw [CommRingCat.hom_comp]
        exact hfin.2.comp (RingHom.Finite.of_surjective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
      exact h2
    have : Nonempty (⊤ : J.subscheme.Opens) := ⟨⟨hne.some, trivial⟩⟩
    exact Module.finrank_pos
  have hdeg : 0 < J.toModulesᵛ.degree k := by
    rw [hJ.degree_dual_toModules]
    exact_mod_cast hpos
  have := hJ.isInvertible_dual_toModules
  have hample := Scheme.isAmple_of_degree_pos (k := k) J.toModulesᵛ hdeg
  let U : X.Opens := ⟨(J.support : Set X)ᶜ, J.support.isClosed.isOpen_compl⟩
  have hU : IsAffine U := Scheme.isAffine_compl_of_isAmple hJ hample U.ι (by simp [U])
  refine ⟨⟨U, hU⟩, fun y hy ↦ ?_⟩
  change y ∈ (J.support : Set X)ᶜ
  rw [hsupp]
  rintro rfl
  exact hQt hy

/-- **The Hilbert functors of a curve are representable.** For a geometrically integral smooth
proper curve `X` over `k`, every `Hilb^d_{X/k}` is representable: `X` is separated over `k`,
and every finite set of points lies in an affine open by
`exists_affineOpens_forall_mem_of_curve`.

(blueprint: `thm-pc-hilb-curves`, Step 1, representability) -/
theorem isRepresentable_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) : (hilbertPresheaf f d).IsRepresentable := by
  classical
  refine isRepresentable_hilbertPresheaf f d fun s t _ ↦ ?_
  obtain ⟨U, hU⟩ := exists_affineOpens_forall_mem_of_curve f (t.image (f.fiberι s).base)
  exact ⟨U, fun x hx ↦ hU _ (Finset.mem_image_of_mem _ hx)⟩

/-- **Hilbert schemes are separated.** If `f : X ⟶ S` is separated and `H` represents
`Hilb^d_{X/S}`, then `H` is separated over `S`: for two points `Z₁, Z₂` of `Hilb^d_{X/S}` over
`H ×[S] H` the locus where `Z₁ ⊆ Z₂` is closed, since `Z₁` and `Z₂` are finite locally free,
and the diagonal of `H` is the intersection of this locus with the one where `Z₂ ⊆ Z₁`.

(blueprint: `thm-pc-hilb-curves`, Step 1, separatedness) -/
theorem isSeparated_of_representableBy_hilbertPresheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] {d : ℕ} {H : Over S} (e : (hilbertPresheaf f d).RepresentableBy H) :
    IsSeparated H.hom :=
  sorry

/-- **The Hilbert scheme of degree zero is the base.** `Hilb^0_{X/S}(T)` has exactly one
element, the empty subscheme of `X_T`, so a scheme `H` representing it is terminal over `S`.

(blueprint: `lem-pc-hilb-smooth`, the case `d = 0`) -/
theorem isIso_of_representableBy_hilbertPresheaf_zero {X S : Scheme.{u}} (f : X ⟶ S)
    {H : Over S} (e : (hilbertPresheaf f 0).RepresentableBy H) : IsIso H.hom := by
  have hext : ∀ {T : Over S} (a b : T ⟶ H), a = b := fun a b ↦
    e.homEquiv.injective (Subsingleton.elim _ _)
  let s : Over.mk (𝟙 S) ⟶ H := e.homEquiv.symm ⟨⊤, isHilbertSubscheme_top f _⟩
  refine ⟨s.left, ?_, by simp⟩
  have := congrArg CommaMorphism.left (hext (Over.homMk (H.hom ≫ s.left) (by simp [Over.w s]) :
    H ⟶ H) (𝟙 H))
  simpa using this

/-- A locally of finite type morphism to the spectrum of a field is universally open: it is flat
(every module over a field is flat) and locally of finite presentation (the base is
noetherian). -/
lemma universallyOpen_of_locallyOfFiniteType_spec_field {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType g] : UniversallyOpen g := by
  have : LocallyOfFinitePresentation g :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  infer_instance

/-- The identity of `Spec k` is geometrically irreducible. -/
lemma geometricallyIrreducible_id_spec_field : GeometricallyIrreducible (𝟙 (Spec (.of k))) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  rw [(asIso (pullback.snd (𝟙 _) y)).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

/-- **The Hilbert scheme of a curve is dominated by a power of the curve.** For a geometrically
integral smooth proper curve `X` over `k` and `H` representing `Hilb^d_{X/k}`, there is a
surjection onto `H` over `k` from a proper geometrically irreducible `k`-scheme, namely the
iterated addition `X^d ⟶ H`, `(x₁, …, x_d) ↦ x₁ + ⋯ + x_d`.

(blueprint: `thm-pc-hilb-curves`, Step 1, the morphism `π_d`) -/
theorem exists_surjective_of_representableBy_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIntegral f] (d : ℕ) (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf f d).RepresentableBy H) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (π : Y ⟶ H.left), IsProper q ∧
      GeometricallyIrreducible q ∧ Surjective π ∧ π ≫ H.hom = q := by
  induction d generalizing H with
  | zero =>
    have := isIso_of_representableBy_hilbertPresheaf_zero f e
    exact ⟨Spec (.of k), 𝟙 _, inv H.hom, inferInstance,
      geometricallyIrreducible_id_spec_field, inferInstance, by simp⟩
  | succ d ih =>
    obtain ⟨H₀, ⟨e₀⟩⟩ := isRepresentable_hilbertPresheaf_curve f d
    obtain ⟨Y, _, π, hq, hirr, hπ, rfl⟩ := ih H₀ e₀
    obtain ⟨a, ha, hfin, hflat, hlfp, hrank, -⟩ := exists_addition_hilbertPresheaf f d H₀ H e₀ e
    have hasurj : Surjective a :=
      (Scheme.Hom.one_le_finrank_iff_surjective a).mp fun t ↦ by simp [hrank t]
    have := universallyOpen_of_locallyOfFiniteType_spec_field f
    have := universallyOpen_of_locallyOfFiniteType_spec_field (π ≫ H₀.hom)
    refine ⟨pullback (π ≫ H₀.hom) f, pullback.fst _ _ ≫ π ≫ H₀.hom,
      (pullbackRightPullbackFstIso H₀.hom f π).inv ≫ pullback.snd _ _ ≫ a, inferInstance,
      GeometricallyIrreducible.comp _ _, inferInstance, ?_⟩
    rw [Category.assoc, Category.assoc, ha, pullbackRightPullbackFstIso_inv_snd_snd_assoc,
      pullback.condition]

/-- **The Hilbert scheme of a curve is proper and geometrically integral.** For a geometrically
integral smooth proper curve `X` over `k`, the scheme `H` representing `Hilb^d_{X/k}` is proper
and geometrically integral over `k`: it is separated, it is the image of the proper
geometrically irreducible `X^d`, and it is smooth, hence geometrically reduced.

(blueprint: `thm-pc-hilb-curves`, Step 1) -/
theorem isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f] (d : ℕ)
    (H : Over (Spec (.of k))) (e : (hilbertPresheaf f d).RepresentableBy H) :
    IsProper H.hom ∧ GeometricallyIntegral H.hom := by
  have := isSeparated_of_representableBy_hilbertPresheaf f e
  have hsm := smoothOfRelativeDimension_of_representableBy_hilbertPresheaf f
    (isRepresentable_hilbertPresheaf_curve f) d H e
  have := SmoothOfRelativeDimension.smooth d H.hom
  obtain ⟨Y, _, π, hq, hirr, hπ, rfl⟩ :=
    exists_surjective_of_representableBy_hilbertPresheaf_curve f d H e
  have : UniversallyClosed H.hom := UniversallyClosed.of_comp_surjective π H.hom
  refine ⟨⟨⟩, ?_⟩
  have := GeometricallyReduced.of_smooth H.hom
  have : GeometricallyIrreducible H.hom := by
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
    have : IrreducibleSpace ↥(Limits.pullback (π ≫ H.hom) y) :=
      GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
    have hs : Surjective ((pullbackRightPullbackFstIso H.hom y π).inv ≫ pullback.snd _ _) :=
      inferInstance
    exact hs.surj.irreducibleSpace (Scheme.Hom.continuous _)
  exact .of_geometricallyReduced_of_geometricallyIrreducible _

/-- **The Hilbert scheme of a smooth projective curve.** For a geometrically integral smooth
proper curve `X` over `k` and `d : ℕ`, the functor `Hilb^d_{X/k}` is represented by a smooth
proper geometrically integral `k`-scheme `H` of dimension `d`, and `H ×[k] X` carries an
effective Cartier divisor `D` which is universal, in the sense that the point of `Hilb^d_{X/k}`
classified by a `k`-morphism `h : T ⟶ H` is the pullback of `D` along the induced morphism
`X_T ⟶ H ×[k] X`:

```
        X_T ──────────────▶ H ×[k] X ─────▶ X
         │  ⟨pr_T ≫ h, pr_X⟩    │            │
         │                      │            f
         ▼                      ▼            ▼
         T ─────── h ─────────▶ H ─── p ──▶ Spec k
```

(blueprint: `sk-thm-picard-hilb-curves`, parts (1) and (3)) -/
theorem hilbertPresheaf_curve_representable [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) :
    ∃ (H : Scheme.{u}) (p : H ⟶ Spec (.of k)), SmoothOfRelativeDimension d p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ ∃ e : (hilbertPresheaf f d).RepresentableBy (Over.mk p),
        ∃ D : (Limits.pullback p f).IdealSheafData, IsEffectiveCartierCenter D.subschemeι ∧
          ∀ (T : Over (Spec (.of k))) (h : T.left ⟶ H) (hh : h ≫ p = T.hom),
            D.comap (Limits.pullback.lift (Limits.pullback.snd f T.hom ≫ h)
                (Limits.pullback.fst f T.hom)
                (by rw [Category.assoc, hh, Limits.pullback.condition])) =
              (e.homEquiv (Over.homMk h hh)).1 := by
  obtain ⟨H, ⟨e⟩⟩ := isRepresentable_hilbertPresheaf_curve f d
  obtain ⟨hprop, hint⟩ :=
    isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve f d H e
  refine ⟨H.left, H.hom, smoothOfRelativeDimension_of_representableBy_hilbertPresheaf f
    (isRepresentable_hilbertPresheaf_curve f) d H e, hprop, hint, e,
    (e.homEquiv (𝟙 H)).1.comap (pullbackSymmetry H.hom f).hom, ?_, fun T h hh ↦ ?_⟩
  · have hD := (isRelativeEffectiveCartier_universal_hilbertPresheaf f e).1.1
    exact (hD.comap_of_flat _).isEffectiveCartierCenter
  · rw [← Scheme.IdealSheafData.comap_comp]
    have : Over.homMk (U := T) (V := Over.mk H.hom) h hh = Over.homMk h hh ≫ 𝟙 H := rfl
    rw [this, hilbertPresheaf_homEquiv_comp_val]
    congr 1
    apply pullback.hom_ext <;> simp

/-- **The points of the Hilbert scheme of a curve.** For a field extension `k'` of `k`, the
`k'`-points of `Hilb^d_{X/k}` are exactly the effective Cartier divisors of degree `d` on
`X_{k'}`. Since both sides are described by ideal sheaves on `X_{k'}`, the bijection is the
identity on underlying ideal sheaves, which is the naturality in `k'`.

`Scheme.Hom.finrank` is junk-valued away from the finite flat case, so the right-hand side
carries the finiteness and flatness of the projection explicitly.

(blueprint: `sk-thm-picard-hilb-curves`, part (2)) -/
theorem hilbertPresheaf_curve_points [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) (k' : Type u) [Field k'] [Algebra k k']
    (T : Over (Spec (.of k))) (hT : T = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (I : (Limits.pullback f T.hom).IdealSheafData) :
    (∃ Z : (hilbertPresheaf f d).obj (op T), Z.1 = I) ↔
      IsEffectiveCartierCenter I.subschemeι ∧
        IsFinite (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
        Flat (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
        ∀ t, (I.subschemeι ≫ Limits.pullback.snd f T.hom).finrank t = d := by
  constructor
  · rintro ⟨⟨I, hfin, hflat, hlfp, hrank⟩, rfl⟩
    exact ⟨(Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite
      (pullback.snd f T.hom)).1.isEffectiveCartierCenter, hfin, hflat, hrank⟩
  · rintro ⟨-, hfin, hflat, hrank⟩
    subst hT
    have hlfp : LocallyOfFinitePresentation
        (I.subschemeι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
      have : IsFinite
          (I.subschemeι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
        hfin
      infer_instance
    exact ⟨⟨I, hfin, hflat, hlfp, hrank⟩, rfl⟩

/-- **The addition morphism is finite locally free.** For a geometrically integral smooth proper
curve `X` over `k`, let `H₁`, `H₂` and `H` represent `Hilb^{d₁}_{X/k}`, `Hilb^{d₂}_{X/k}` and
`Hilb^{d₁ + d₂}_{X/k}`, and let `α : H₁ ×[k] H₂ ⟶ H` be the addition morphism, the morphism
classifying the sum of the two universal divisors. Then `α` is finite, flat and locally of
finite presentation of degree `(d₁ + d₂).choose d₁`.

It is proper, since `H₁ ×[k] H₂` is proper and `H` is separated, and quasi-finite, since its
composite with the finite surjection `X^{d₁} ×[k] X^{d₂} ⟶ H₁ ×[k] H₂` is the finite morphism
`X^{d₁ + d₂} ⟶ H`; so it is finite. It is flat by descent along that flat surjection
(`AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective`), and its degree `N` satisfies
`d₁! d₂! N = (d₁ + d₂)!`.

(blueprint: `thm-pc-hilb-curves`, Step 3) -/
theorem isFinite_flat_finrank_of_hilbertPresheaf_add [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIntegral f] (d₁ d₂ : ℕ) (H₁ H₂ H : Over (Spec (.of k)))
    (e₁ : (hilbertPresheaf f d₁).RepresentableBy H₁)
    (e₂ : (hilbertPresheaf f d₂).RepresentableBy H₂)
    (e : (hilbertPresheaf f (d₁ + d₂)).RepresentableBy H)
    (α : Over.mk (pullback.fst H₁.hom H₂.hom ≫ H₁.hom) ⟶ H)
    (hα : (e.homEquiv α).1 =
      (e₁.homEquiv (Over.homMk (pullback.fst H₁.hom H₂.hom))).1 *
        (e₂.homEquiv (Over.homMk (pullback.snd H₁.hom H₂.hom) pullback.condition.symm)).1) :
    IsFinite α.left ∧ Flat α.left ∧ LocallyOfFinitePresentation α.left ∧
      ∀ t, α.left.finrank t = (d₁ + d₂).choose d₁ :=
  sorry

/-- **The addition morphism of the Hilbert schemes of a curve.** If `H₁`, `H₂` and `H`
represent `Hilb^{d₁}_{X/k}`, `Hilb^{d₂}_{X/k}` and `Hilb^{d₁ + d₂}_{X/k}`, then there is a
`k`-morphism `H₁ ×[k] H₂ ⟶ H`, which on points is addition of effective Cartier divisors —
i.e. the product of the corresponding ideal sheaves — and which is finite, flat and locally of
finite presentation of degree `(d₁ + d₂).choose d₁`.

The last clause is what identifies `α`: without it any finite flat morphism of the right degree
would do, and the descent argument of the blueprint needs to know which morphism it is.

(blueprint: `sk-thm-picard-hilb-curves`, part (3)) -/
theorem hilbertPresheaf_curve_add [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d₁ d₂ : ℕ) (H₁ H₂ H : Over (Spec (.of k)))
    (e₁ : (hilbertPresheaf f d₁).RepresentableBy H₁)
    (e₂ : (hilbertPresheaf f d₂).RepresentableBy H₂)
    (e : (hilbertPresheaf f (d₁ + d₂)).RepresentableBy H) :
    ∃ α : Limits.pullback H₁.hom H₂.hom ⟶ H.left,
      α ≫ H.hom = Limits.pullback.fst H₁.hom H₂.hom ≫ H₁.hom ∧
        IsFinite α ∧ Flat α ∧ LocallyOfFinitePresentation α ∧
          (∀ t, α.finrank t = (d₁ + d₂).choose d₁) ∧
          ∀ (T : Over (Spec (.of k))) (t₁ : T ⟶ H₁) (t₂ : T ⟶ H₂) (t : T ⟶ H),
            t.left = Limits.pullback.lift t₁.left t₂.left
                (by rw [Over.w, Over.w]) ≫ α →
              (e.homEquiv t).1 = (e₁.homEquiv t₁).1 * (e₂.homEquiv t₂).1 := by
  let P : Over (Spec (.of k)) := Over.mk (pullback.fst H₁.hom H₂.hom ≫ H₁.hom)
  let p₁ : P ⟶ H₁ := Over.homMk (pullback.fst H₁.hom H₂.hom)
  let p₂ : P ⟶ H₂ := Over.homMk (pullback.snd H₁.hom H₂.hom) pullback.condition.symm
  let u : (hilbertPresheaf f (d₁ + d₂)).obj (op P) :=
    ⟨(e₁.homEquiv p₁).1 * (e₂.homEquiv p₂).1, (e₁.homEquiv p₁).2.mul f (e₂.homEquiv p₂).2⟩
  let α := e.homEquiv.symm u
  have hα : (e.homEquiv α).1 = (e₁.homEquiv p₁).1 * (e₂.homEquiv p₂).1 := by
    simp [α, u]
  obtain ⟨hfin, hflat, hlfp, hrank⟩ :=
    isFinite_flat_finrank_of_hilbertPresheaf_add f d₁ d₂ H₁ H₂ H e₁ e₂ e α hα
  refine ⟨α.left, Over.w α, hfin, hflat, hlfp, hrank, fun T t₁ t₂ t ht ↦ ?_⟩
  let s : T ⟶ P := Over.homMk (pullback.lift t₁.left t₂.left (by rw [Over.w, Over.w]))
    (by simp [P])
  obtain rfl : t = s ≫ α := by
    ext1
    exact ht
  have h₁ : t₁ = s ≫ p₁ := by
    ext1
    simp [s, p₁]
  have h₂ : t₂ = s ≫ p₂ := by
    ext1
    simp [s, p₂]
  rw [hilbertPresheaf_homEquiv_comp_val, hα, Scheme.IdealSheafData.comap_mul, h₁, h₂,
    hilbertPresheaf_homEquiv_comp_val, hilbertPresheaf_homEquiv_comp_val]

end Curve

end AlgebraicGeometry
