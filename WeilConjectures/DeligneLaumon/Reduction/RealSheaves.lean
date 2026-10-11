/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk
public import WeilConjectures.DeligneLaumon.Reduction.RealCurve
public import WeilConjectures.DeligneLaumon.Reduction.TraceReality
public import WeilConjectures.WeilSheaf.LisseLocus

/-!
# Real Weil sheaves on an arbitrary base are mixed

A constructible Weil sheaf is `ι`-*real* (`AlgebraicGeometry.WeilSheaf.IsReal`) if the realization
under `ι` of every local Frobenius characteristic polynomial has real coefficients. Over a curve
this forces purity on a dense open, which is the content of the blueprint section
`sec-purity-real-sheaves`; this file states the extension of that statement to an arbitrary
separated finite-type `k₀`-scheme, which is the input the Deligne–Laumon reduction needs in order
to turn the reality of a local `L`-factor into a weight bound.

## Implementation notes

A Noetherian induction reduces to a lisse real sheaf on a smooth affine irreducible stratum, where
an irreducibility-preserving Bertini theorem produces a family of smooth geometrically irreducible
curve sections on which each constituent becomes pure of a weight independent of the curve;
mixedness then descends along finite constant extensions and is spliced back along the open–closed
sequence.

The geometric and group-theoretic inputs of the reduction are stated and proved separately:
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback` (Bertini),
`Representation.exists_forall_isIrreducible_baseChange_of_congr` (finite matrix witnesses) and
`Representation.exists_filtration_isIrreducible_restrict` (geometric constituents), and curve
testing for geometric irreducibility below.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`:
  blueprint `lem-zl-curve-testing-irreducibility`.
- `AlgebraicGeometry.WeilSheaf.IsReal.isMixed`: blueprint `sk-i-dl-general-real` and
  `thm-zl-real-mixed-by-curves`.

## TODO

`AlgebraicGeometry.WeilSheaf.IsReal.isMixed` is proved here by Noetherian induction from
`AlgebraicGeometry.WeilSheaf.IsReal.exists_isMixed_upperStar_opensι` (mixedness on a nonempty
open), which is stated with `sorry`, as is curve testing
`AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`. Both
need infrastructure that does not exist yet: the dictionary between lisse pro-étale Weil sheaves
and representations of the Weil group (`def-wf-fundamental-representation`) on a base of any
dimension, finite constant-field extensions of Weil sheaves, and the Bertini theorem
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback`. The curve case
is `AlgebraicGeometry.WeilSheaf.IsReal.isMixed_of_isLisse`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1.8, for
  real sheaves and their mixedness.
- [Kiehl, Weissauer, *Weil conjectures, perverse sheaves and l-adic Fourier
  transform*][kiehlWeissauer2001], Springer (2001), Appendix B, for the
  irreducibility-preserving Bertini theorem the proof uses.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

open TopologicalSpace

/-- **Curve testing for geometric irreducibility**
(blueprint: `lem-zl-curve-testing-irreducibility`). Let `X₀` be a smooth geometrically connected
affine scheme of dimension `d ≥ 1` over a finite field `k₀`, with geometric fiber `X`, let
`𝒮₁, …, 𝒮ᵣ` be Weil sheaves on `X₀` whose geometric restrictions are irreducible local systems,
and let `S` be a nonempty finite set of `k̄`-points of `X`. There is a closed immersion
`i : C ⟶ X` of a smooth connected affine curve over `k̄` through `S`, defined over a finite
extension of `k₀` (stable under a power of the geometric Galois Frobenius of `X`), on which
every `𝒮ⱼ` remains geometrically irreducible. -/
theorem WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar {k₀ : Type u}
    [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X₀ : Scheme.{u}}
    [X₀.Over (Spec (CommRingCat.of k₀))] [IsAffine X₀] {d : ℕ} (hd : 1 ≤ d)
    [SmoothOfRelativeDimension d (X₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (CommRingCat.of k₀))] {r : ℕ}
    (𝒮 : Fin r → WeilSheaf k₀ l X₀)
    (h𝒮 : ∀ j, ProEtale.IsIrreducibleAdicLocalSystem (𝒮 j).obj.carrier)
    (S : Finset
      (Spec (.of (AlgebraicClosure k₀)) ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1
        (i ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧
      (∀ j, ProEtale.IsIrreducibleAdicLocalSystem
        ((i)^*ᵃ[l].obj (𝒮 j).obj.carrier)) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C,
        φ.hom ≫ i = i ≫ ((X₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom := by
  sorry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- The pullback of an `ι`-real Weil sheaf is `ι`-real: at a closed point `z` over `x`, the local
Frobenius of the pullback has the characteristic polynomial of a power of the local Frobenius at
`x`, whose traces of powers are real. -/
theorem IsReal.upperStar {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l Y} (hF : F.IsReal ι) (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] : ((WeilSheaf.upperStar φ).obj F).IsReal ι := by
  intro z
  refine LinearMap.conj_charpolyRev_coeff_of_trace ι _ fun m ↦ ?_
  rw [LinearMap.trace_pow_eq_of_charpoly_eq (charpoly_frobeniusEnd_stalk_upperStar φ F z),
    ← pow_mul]
  exact LinearMap.conj_trace_pow_of_charpolyRev ι _ (hF _) _

/-- Every Weil sheaf on a nonempty open of `𝔸⁰ = Spec k₀` is mixed. -/
theorem exists_isMixed_upperStar_opensι_of_isEmpty {n : Type u} [IsEmpty n]
    (O : 𝔸(n; Spec (CommRingCat.of k₀)).Opens) [Nonempty O] (G : WeilSheaf k₀ l O) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι := by
  have hO : IsOpenImmersion (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : LocallyQuasiFinite ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  have : IsSeparated ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  have : LocallyOfFiniteType ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  have : QuasiCompact ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  obtain ⟨o⟩ := ‹Nonempty O›
  exact ⟨⊤, ⟨o, trivial⟩, isMixed_of_locallyQuasiFinite ι _⟩

/-- An `ι`-real Weil sheaf on a nonempty open of the affine line `𝔸¹` (with any one-element index
type) is `ι`-mixed on a nonempty open:
it is lisse on a dense open, a smooth geometrically connected curve. -/
theorem IsReal.exists_isMixed_upperStar_opensι_of_card_eq_one {n : Type u} [Finite n]
    (hn : Nat.card n = 1) (O : 𝔸(n; Spec (CommRingCat.of k₀)).Opens) [Nonempty O]
    {G : WeilSheaf k₀ l O}
    (hG : G.IsReal ι) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι := by
  have := isNoetherian_of_locallyOfFiniteType
    (𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : QuasiCompact (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  obtain ⟨U, hU, hlisse⟩ := exists_dense_isLisse_upperStar G
  have hne : (U : Set O).Nonempty := hU.nonempty
  have : Nonempty U := hne.to_subtype
  have hv : U.toScheme ↘ Spec (CommRingCat.of k₀) =
      (U.ι ≫ O.ι) ≫ 𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀) := by
    rw [Category.assoc, comp_over O.ι, comp_over U.ι]
  have : SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    have := AffineSpace.smoothOfRelativeDimension_over n (Spec (CommRingCat.of k₀))
    rw [hn] at this
    rw [hv, show 1 = 0 + 1 from rfl]; infer_instance
  have : GeometricallyConnected (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    have := GeometricallyIrreducible.comp_of_isOpenImmersion (U.ι ≫ O.ι)
      (𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    rw [hv]; exact GeometricallyConnected.of_geometricallyIrreducible _
  have : IsSeparated (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  have : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  have : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  exact ⟨U, hne, (hG.upperStar U.ι).isMixed_of_isLisse hlisse⟩


/-- **Real sheaves on open subschemes of affine space of dimension at least two are mixed on a
nonempty open** (blueprint: `thm-zl-real-mixed-by-curves`, the curve argument in dimension
`d ≥ 2`). Let `O` be a nonempty open subscheme of `𝔸ᵈ` over `k₀`, `d ≥ 2`, and `G` an `ι`-real
Weil sheaf on `O`. Then `G` is `ι`-mixed on a nonempty open of `O`: after shrinking, `G` is lisse,
its constituents become geometrically irreducible after a finite constant extension, curve
testing (`lem-zl-curve-testing-irreducibility`) produces curves through any two closed points on
which they stay irreducible, and purity of real lisse sheaves on curves
(`thm-rp-real-lisse-purity-affine`) gives each constituent a weight independent of the point. -/
theorem IsReal.exists_isMixed_upperStar_opensι_of_two_le {d : ℕ} (hd : 2 ≤ d)
    (O : 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)).Opens) [Nonempty O]
    {G : WeilSheaf k₀ l O} (hG : G.IsReal ι) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι :=
  sorry

/-- An `ι`-real Weil sheaf on a nonempty open subscheme of `𝔸ᵈ` over `k₀` is `ι`-mixed on a
nonempty open: for `d = 0` every Weil sheaf on a point is mixed, for `d = 1` this is the curve
case, and `d ≥ 2` is `AlgebraicGeometry.WeilSheaf.IsReal.exists_isMixed_upperStar_opensι_of_two_le`.
-/
theorem IsReal.exists_isMixed_upperStar_opensι_of_affineSpace {d : ℕ}
    (O : 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)).Opens) [Nonempty O]
    {G : WeilSheaf k₀ l O} (hG : G.IsReal ι) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι := by
  rcases d with _ | _ | d
  · exact exists_isMixed_upperStar_opensι_of_isEmpty O G
  · exact hG.exists_isMixed_upperStar_opensι_of_card_eq_one (by simp) O
  · exact hG.exists_isMixed_upperStar_opensι_of_two_le (by omega) O
open ZeroObject in
/-- A Weil sheaf on a scheme without points is mixed of weights at most `w`, for every `w`: the
filtration `0 ⊆ F` has the single quotient `F`, which is punctually pure of weight `w` since
there are no closed points. -/
theorem isMixedOfWeightsAtMost_of_isEmpty {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [IsEmpty X] (F : WeilSheaf k₀ l X)
    (w : ℝ) : F.IsMixedOfWeightsAtMost ι w :=
  ⟨1, ![0, F], fun i ↦ Fin.cases (0 : (0 : WeilSheaf k₀ l X) ⟶ F) (fun j ↦ j.elim0) i,
    Limits.isZero_zero _, ⟨Iso.refl _⟩,
    fun i ↦ Fin.cases ⟨fun _ _ _ ↦ (Limits.isZero_zero _).eq_of_tgt _ _⟩ (fun j ↦ j.elim0) i,
    fun _ ↦ ⟨w, le_rfl, fun x ↦ isEmptyElim x.1⟩⟩

/-- **Real sheaves are mixed on a nonempty open.** Let `X` be a nonempty reduced separated
`k₀`-scheme of finite type and `F` an `ι`-real Weil sheaf on `X`. Then the restriction of `F` to
some nonempty open of `X` is `ι`-mixed (blueprint: `thm-zl-real-mixed-by-curves`, the lisse
stratum: after shrinking, `F` is lisse on a smooth affine stratum, where curve testing
`lem-zl-curve-testing-irreducibility` and purity of real lisse sheaves on curves
`thm-rp-real-lisse-purity-affine` make the constituents of `F` pure, after a finite constant
extension which is then descended). -/
theorem IsReal.exists_isMixed_upperStar_opensι {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsReduced X] [Nonempty X]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ ((WeilSheaf.upperStar U.ι).obj F).IsMixed ι :=
  sorry

/-- Every constructible `ι`-real Weil sheaf on a separated finite-type `k₀`-scheme is `ι`-mixed
(blueprint: `sk-i-dl-general-real`, `thm-zl-real-mixed-by-curves`).

Noetherian induction on the closed subsets of `X`: on a reduced closed subscheme `T`, a real
sheaf is mixed on a nonempty open `U`
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isMixed_upperStar_opensι`)
and, by induction, on the reduced closed complement of `U`; mixed filtrations glue along the
open–closed exact sequence (`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed`),
and reality is inherited by restrictions (`AlgebraicGeometry.WeilSheaf.IsReal.upperStar`). -/
theorem IsReal.isMixed {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    F.IsMixed ι := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
  -- Noetherian induction on the closed subsets of `X`.
  have key : ∀ (Z : Closeds X) (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
      [IsReduced T] (i : T ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))],
      Set.range i ⊆ Z → ∀ G : WeilSheaf k₀ l T,
        haveI : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
          rw [← comp_over i]; infer_instance
        G.IsReal ι → G.IsMixed ι := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
    intro T _ _ i _ _ hiZ G hG
    have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have : IsSeparated (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
    cases isEmpty_or_nonempty T
    · exact ⟨0, isMixedOfWeightsAtMost_of_isEmpty G 0⟩
    obtain ⟨U, ⟨u, hu⟩, w₁, hU⟩ := hG.exists_isMixed_upperStar_opensι
    -- The reduced closed complement `T'` of `U`.
    let C : Closeds T := ⟨(U : Set T)ᶜ, U.isOpen.isClosed_compl⟩
    let i' := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over
        (Spec (CommRingCat.of k₀)) := ⟨i' ≫ T ↘ Spec (CommRingCat.of k₀)⟩
    have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘
        Spec (CommRingCat.of k₀)) := inferInstanceAs (LocallyOfFiniteType (i' ≫ _))
    have hrange : Set.range i' = C := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let Z' : Closeds X := ⟨i '' C, i.isClosedEmbedding.isClosedMap _ C.isClosed⟩
    have hZ' : Z' < Z := by
      refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiZ ⟨t, ht⟩) fun h ↦ ?_
      have : i u ∈ (Z' : Set X) := h ▸ hiZ ⟨u, rfl⟩
      obtain ⟨t, ht, hti⟩ := this
      exact ht (i.isClosedEmbedding.injective hti ▸ hu)
    obtain ⟨w₂, hT'⟩ := ih Z' hZ' _ (i' ≫ i) (by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]; exact subset_rfl)
      _ (hG.upperStar i')
    have : NoetherianSpace U.toScheme := inferInstanceAs (NoetherianSpace (U : Set T))
    exact ⟨max w₁ w₂, IsMixedOfWeightsAtMost.of_openClosed (j := U.ι) (i := i')
      (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl)
      (hU.mono_weight (le_max_left _ _)) (hT'.mono_weight (le_max_right _ _))⟩
  -- `X` is the union of the empty open and its reduction.
  let i := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme.Over
      (Spec (CommRingCat.of k₀)) := ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme ↘
      Spec (CommRingCat.of k₀)) := inferInstanceAs (LocallyOfFiniteType (i ≫ _))
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have : QuasiCompact (⊥ : X.Opens).ι := inferInstance
  obtain ⟨w, hw⟩ := key ⊤ _ i (Set.subset_univ _) _ (hF.upperStar i)
  exact ⟨w, IsMixedOfWeightsAtMost.of_openClosed (j := (⊥ : X.Opens).ι) (i := i)
    (by rw [Scheme.Opens.range_ι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact isCompl_bot_top)
    (isMixedOfWeightsAtMost_of_isEmpty _ w) hw⟩

end WeilSheaf

end AlgebraicGeometry
