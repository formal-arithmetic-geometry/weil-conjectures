/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.WeilSheaf.Curve
public import WeilConjectures.WeilSheaf.Defs

/-!
# The Deligne–Laumon upper bound on a smooth curve

Let `C₀` be a smooth geometrically connected curve over `k₀ = 𝔽_q` and `F` a lisse Weil sheaf,
punctually `ι`-pure of weight `w`. The Deligne–Laumon estimate on the affine line
(`WeilConjectures.DeligneLaumon.AffineLine.Upper`) transports to `C₀`: `H_c^i(C, F)` has weights
at most `w + i` when `C₀` is affine, and `H_c^r(C, j_*F)` has weights at most `w + r` for the
middle extension along a dense open `j : U₀ ↪ C₀`.

The transport goes through a finite generically étale map `g : C'₀ ⟶ 𝔸¹` from a curve `C'₀`
containing `C₀` (`AlgebraicGeometry.IsCurve.exists_isFinite_affineLine`): `g` is proper and
`g₀*` is exact, so `H_c^i(C, F) = H_c^i(𝔸¹, g₀*j₀!F)`, and over the open of `𝔸¹` above which
`g` is étale and which misses `g(C'₀ \ C₀)` this sheaf is lisse and pure of weight `w`.

## Scope of the curve reduction

The degree-one estimate for an irreducible factor on the line identifies the Fourier transform
of the middle extension `(j_*M)[1]` with a middle extension `(j'_*M')[1]` on the dual line,
reads off the weight of `M'` and then `H_c^1(𝔸¹, j_*M)` as an origin stalk of `j'_*M'`. The
curve reduction only needs finite-map transport, geometric constituents after a constant
extension, and the surjection supplied by deleting a regular point; it performs no further
Fourier-theoretic identification (blueprint: `rem-a1-fourier-ready-interface`,
`rem-a1-reduction-discharged`).

## Implementation notes

The provisional Weil sheaves of `WeilConjectures.WeilSheaf.Defs` are zero, and the category
`AlgebraicGeometry.WeilComplex` is not triangulated, so the long exact sequences of compactly
supported cohomology the blueprint uses cannot be formed. The statements below that the
blueprint derives from such sequences are proved from the vanishing of every Weil sheaf; the
others follow the blueprint.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two`: on a smooth
  geometrically connected affine curve, `H_c^2` is pure of weight `w + 2`.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine`:
  the affine-curve estimate.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_directImage`:
  the estimate for a middle extension on a smooth curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Finite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

-- the stalks of the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- *Purity under finite étale pushforward.* If `g : X ⟶ Y` is finite étale and `F` is
punctually `ι`-pure of weight `w`, then so is `g₀*F`. At a closed point `y` the geometric stalk
of `g₀*F` is the sum of the stalks at the geometric points over `y`; a closed point `x` over
`y` of residue degree `e` contributes a Frobenius cycle of `e` copies of `F_x̄`, on which
`F_yᵉ = Fₓ`. An eigenvalue `λ` of `F_y` there has `λᵉ` an eigenvalue `α` of `Fₓ`, so
`|ι λ|ᵉ = q_x ^ (w / 2) = q_y ^ (e w / 2)`.

With the present coefficients the stalks of `g₀*F` are zero, which is how the statement is
proved here. (blueprint: `lem-a1-finite-map-purity`) -/
theorem IsPunctuallyPureOfWeight.lowerStar {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) (g : X ⟶ Y) [IsFinite g] [Etale g]
    [g.IsOver (Spec (CommRingCat.of k₀))] :
    ((WeilSheaf.lowerStar g).obj F).IsPunctuallyPureOfWeight ι w :=
  fun x α hα ↦ absurd hα (((WeilSheaf.lowerStar g).obj F).not_hasEigenvalue_frobeniusEnd_stalk x α)

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- *Cohomology under a finite map.* For a finite morphism `g : X ⟶ Y` of separated
`k₀`-schemes of finite type and a Weil sheaf `F` on `X`,
`H_c^i(X, F) ≅ H_c^i(Y, g₀*F)` Frobenius-equivariantly, for every `i`. A finite morphism is
proper, so `Rg₀! = Rg₀*`, and `g₀*` is exact, so `RΓ_c(X, F) = Ra_!Rg₀!F ≅ Ra_!g₀*F`.

The blueprint states this for `Y = 𝔸¹` and `F` lisse. The compact-support composition
`R(g ≫ a)_! ≅ Ra_! ∘ Rg_!` is not available for the provisional Weil complexes; both sides are
zero, which is how the statement is proved here. (blueprint: `lem-a1-finite-map-cohomology`) -/
theorem nonempty_equiv_compactlySupportedCohomology_lowerStar (g : X ⟶ Y) [IsFinite g]
    [g.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) (i : ℤ) :
    Nonempty ((F.compactlySupportedCohomology i).Equiv
      (((lowerStar g).obj F).compactlySupportedCohomology i)) :=
  have : Subsingleton (F.compactlySupportedCohomology i).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  have : Subsingleton (((lowerStar g).obj F).compactlySupportedCohomology i).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  ⟨.ofSubsingleton _ _⟩

end Finite

section Boundary

variable {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [IsFinite (Z ↘ Spec (CommRingCat.of k₀))]

-- the provisional Weil complexes are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- *Weights of the cohomology of a finite boundary.* Let `Z₀` be finite over `k₀` and `G` a
Weil sheaf on `Z₀` whose stalks have weights at most `w`. Then `H_c^0(Z, G)` has weights at most
`w`: it is the sum over the closed points `x` of `Z₀` of the Frobenius modules induced from the
stalks `G_x̄`, so each eigenvalue `λ` has `λᵉ` an eigenvalue of `Fₓ`, `e = [κ(x) : k₀]`, and
`|ι λ| ≤ (q_x ^ (w / 2)) ^ (1 / e) = q ^ (w / 2)`.

With the present coefficients `H_c^0(Z, G)` is zero, which is how the statement is proved here.
(blueprint: `lem-a1-finite-boundary-weights`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite
    (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l Z) {w : ℝ} (hG : G.HasWeightsAtMost ι w) :
    (G.compactlySupportedCohomology 0).HasWeightsAtMostOver k₀ ι w :=
  have : Subsingleton (G.compactlySupportedCohomology 0).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _

end Boundary

section AffineCurve

variable {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [IsCurve (C ↘ Spec (CommRingCat.of k₀))]

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedSectionVars false in
/-- *Finite length of a lisse Weil sheaf on a curve.* A lisse Weil sheaf `F` on a smooth
geometrically connected curve has finite length among lisse Weil sheaves: there is a finite
filtration `0 = G 0 ↪ G 1 ↪ ⋯ ↪ G n ≅ F` by lisse Weil subsheaves whose graded pieces
`coker φᵢ` are nonzero, lisse and irreducible, that is, every lisse subsheaf of `coker φᵢ` is
zero or all of it. A nonzero lisse sheaf which is not irreducible has a nonzero proper lisse
subsheaf, of strictly smaller rank, so induction on the rank terminates.

With the present coefficients `F` is zero, and the filtration of length zero exhibits it.
(blueprint: `lem-a1-finite-length`) -/
theorem IsLisse.exists_filtration [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l C}
    (hF : F.IsLisse) :
    ∃ (n : ℕ) (G : Fin (n + 1) → WeilSheaf k₀ l C) (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      IsZero (G 0) ∧ IsIsomorphic (G (Fin.last n)) F ∧ (∀ i, Mono (φ i)) ∧
        (∀ i, (G i).IsLisse) ∧ ∀ i : Fin n, (cokernel (φ i)).IsLisse ∧
          ¬ IsZero (cokernel (φ i)) ∧ ∀ (S : WeilSheaf k₀ l C) (s : S ⟶ cokernel (φ i)),
            Mono s → S.IsLisse → IsZero S ∨ IsIso s :=
  ⟨0, fun _ ↦ F, fun i ↦ i.elim0, isZero F, ⟨Iso.refl F⟩, fun i ↦ i.elim0, fun _ ↦ hF,
    fun i ↦ i.elim0⟩

variable [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth curve `C₀` over `k₀` is locally of finite type over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  inferInstance

-- the provisional Weil complexes are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- *The top cohomology of an affine curve.* Let `U₀` be a smooth geometrically connected affine
curve and `F` a lisse Weil sheaf on `U₀`. Global Verdier duality on the smooth nonproper curve
identifies `H_c^2(U, F)` with the geometric coinvariants `V_{π₁(U)}` of `F`, Tate-twisted by
`(-1)`: the Frobenius of the cohomology is `q` times the Frobenius of the coinvariants.

With the present coefficients both sides are zero, which is how the statement is proved here.
(blueprint: `lem-a1-affine-hc2`) -/
theorem nonempty_equiv_compactlySupportedCohomology_two
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l C)
    (hF : F.IsLisse) :
    Nonempty ((F.compactlySupportedCohomology 2).Equiv
      (F.geometricCoinvariants.tateTwist (Nat.card k₀) (-1))) :=
  have : Subsingleton (F.compactlySupportedCohomology 2).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  have : Subsingleton (F.geometricCoinvariants.tateTwist (Nat.card k₀) (-1)).carrier :=
    have : Subsingleton F.dual.globalSections.carrier :=
      ModuleCat.isZero_iff_subsingleton.1 ((WeilCoefficients.toModuleCat l).map_isZero
        F.dual.isZero_globalSectionsObj)
    inferInstanceAs (Subsingleton (Module.Dual (PadicAlgCl l) F.dual.globalSections.carrier))
  ⟨.ofSubsingleton _ _⟩

/-- *Purity of `H_c^2` on an affine curve.* Let `U₀` be a smooth geometrically connected affine
curve and `F` a lisse Weil sheaf on `U₀`, punctually `ι`-pure of weight `w`. Then
`H_c^2(U, F)` is `ι`-pure of weight `w + 2` (possibly zero): it is the Tate twist `W(-1)` of the
geometric coinvariants `W = V_{π₁(U)}`, which are pure of weight `w`, and the twist `(-1)`
multiplies the Frobenius by `q`. (blueprint: `lem-a1-affine-hc2-pure`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ)
    (F : WeilSheaf k₀ l C) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) := by
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_two F hF
  have h := (isPureOfWeightOver_geometricCoinvariants ι F hF hw).tateTwist Nat.card_pos (-1)
  rw [show w - 2 * ((-1 : ℤ) : ℝ) = w + 2 by push_cast; ring] at h
  exact FrobeniusModule.IsPureOfWeight.of_equiv e h

-- the provisional Weil complexes are zero, and degree one needs no hypothesis
set_option linter.unusedVariables false in
/-- *Affine compact-support upper bound.* Let `C₀` be a smooth geometrically connected affine
curve and `F` a lisse Weil sheaf, punctually `ι`-pure of weight `w`. Then every `H_c^i(C, F)`
has weights at most `w + i`. More precisely `H_c^0(C, F) = 0`, `H_c^2(C, F)` is pure of weight
`w + 2`, and `H_c^i(C, F) = 0` for `i ∉ {0, 1, 2}`.

Degrees zero and two and the range are
`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`,
`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two` and
`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`. In degree
one the blueprint transports `H_c^1(C, F)` to `H_c^1(𝔸¹, g₀*j₀!F)` along a finite map
(`AlgebraicGeometry.IsCurve.exists_isFinite_affineLine`,
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_lowerShriek_lowerStar`),
which is a quotient of `H_c^1` of a lisse pure sheaf on a dense open of `𝔸¹`
(`AlgebraicGeometry.WeilSheaf.isLisse_and_isPunctuallyPureOfWeight_upperStar_lowerStar`), then
of `H_c^1(V, E)` for `E` unramified at infinity after a constant extension
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_surjective_compactlySupportedCohomology_one`),
an extension of `H_c^1(𝔸¹, v_*E)`, bounded by the affine-line estimate, by a boundary term of
weights at most `w`
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite`).
These steps run through long exact sequences of compactly supported cohomology, which the
provisional, non-triangulated Weil complexes do not provide; with the present coefficients
`H_c^1(C, F)` is zero, which is how degree one is proved here.
(blueprint: `thm-a1-affine-curve-upper`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ)
    (F : WeilSheaf k₀ l C) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    (∀ i : ℤ, (F.compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι (w + i)) ∧
      Subsingleton (F.compactlySupportedCohomology 0).carrier ∧
      (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) ∧
      ∀ i : ℤ, i < 0 ∨ 2 < i → Subsingleton (F.compactlySupportedCohomology i).carrier := by
  have h0 := subsingleton_compactlySupportedCohomology_zero F hF
  have h2 := isPureOfWeightOver_compactlySupportedCohomology_two ι F hF hw
  have hr := fun (i : ℤ) (hi : i < 0 ∨ 2 < i) ↦
    subsingleton_compactlySupportedCohomology_of_isAffine F hi
  refine ⟨fun i ↦ ?_, h0, h2, hr⟩
  obtain hi | rfl | rfl | rfl | hi : i < 0 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ 2 < i := by omega
  · have := hr i (.inl hi)
    exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _
  · exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _
  · -- degree one: see the docstring
    have : Subsingleton (F.compactlySupportedCohomology 1).carrier :=
      WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
    exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _
  · simpa using h2.hasWeightsAtMostOver
  · have := hr i (.inr hi)
    exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _

end AffineCurve

section Reduction

variable {C C' : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [C'.Over (Spec (CommRingCat.of k₀))] [IsCurve (C ↘ Spec (CommRingCat.of k₀))]
  [IsCurve (C' ↘ Spec (CommRingCat.of k₀))] (j : C ⟶ C') [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))] (g : C' ⟶ affineLine k₀) [IsFinite g]
  [g.IsOver (Spec (CommRingCat.of k₀))]

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedSectionVars false in
/-- *Cohomology transport under the finite-map reduction.* Let `j : C₀ ↪ C'₀` be an open
immersion of curves and `g : C'₀ ⟶ 𝔸¹` a finite morphism, as provided for a smooth
geometrically connected affine curve `C₀` by `AlgebraicGeometry.IsCurve.exists_isFinite_affineLine`.
For a Weil sheaf `F` on `C₀`, put `K = g₀*j₀!F`. Then `H_c^i(C, F) ≅ H_c^i(𝔸¹, K)` for every
`i`: `RΓ_c(C, F) = RΓ_c(C', j₀!F)`, and the finite-map transport
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_lowerStar` applies to
`j₀!F`.

The first identification is the compact-support composition along `j`, which is not available
for the provisional Weil complexes; both sides are zero, which is how it is proved here.
(blueprint: `lem-a1-reduction-composition`) -/
theorem nonempty_equiv_compactlySupportedCohomology_lowerShriek_lowerStar
    (F : WeilSheaf k₀ l C) (i : ℤ) :
    Nonempty ((F.compactlySupportedCohomology i).Equiv
      (((lowerStar g).obj ((extensionByZero j).obj F)).compactlySupportedCohomology i)) := by
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_lowerStar g
    ((extensionByZero j).obj F) i
  -- `RΓ_c(C, F) = RΓ_c(C', j₀!F)`: both sides are zero with the present coefficients
  have : Subsingleton (F.compactlySupportedCohomology i).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  have : Subsingleton (((extensionByZero j).obj F).compactlySupportedCohomology i).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  exact ⟨(FrobeniusModule.Equiv.ofSubsingleton _ _).trans e⟩

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- *Lisse purity of the transported sheaf.* In the situation of
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_lowerShriek_lowerStar`,
let `F` be lisse and punctually `ι`-pure of weight `w` on `C₀`, and let `W₀ ⊆ 𝔸¹` be an open
over which `g` is étale and whose inverse image lies in `C₀`, for instance the complement of
the branch locus of `g` and of `g(C'₀ \ C₀)`. Then `K|_W = (g₀*j₀!F)|_W` is lisse and punctually
`ι`-pure of weight `w`: over `W₀` it is the pushforward of `F` along the finite étale map
`g⁻¹(W₀) ⟶ W₀`, so `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.lowerStar` applies.

With the present coefficients `K|_W` is zero, which is how the statement is proved here.
(blueprint: `lem-a1-reduction-lisse-pure`) -/
theorem isLisse_and_isPunctuallyPureOfWeight_upperStar_lowerStar (ι : PadicAlgCl l →+* ℂ)
    (W : (affineLine k₀).Opens) (hW : Etale (g.resLE W (g ⁻¹ᵁ W) le_rfl))
    (hWC : g ⁻¹ᵁ W ≤ j.opensRange) {F : WeilSheaf k₀ l C} (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) :
    ((upperStar W.ι).obj ((lowerStar g).obj ((extensionByZero j).obj F))).IsLisse ∧
      ((upperStar W.ι).obj ((lowerStar g).obj ((extensionByZero j).obj F))).IsPunctuallyPureOfWeight
        ι w :=
  ⟨Scheme.IsLocallyConstantSheaf.of_isZero (isZero_carrier _),
    fun x α hα ↦ absurd hα (not_hasEigenvalue_frobeniusEnd_stalk _ x α)⟩

end Reduction

section MiddleExtension

variable {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [C.Over (Spec (CommRingCat.of k₀))] [IsCurve (C ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  [IsDominant j]

-- the provisional Weil complexes are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- *Upper bound for a curve middle extension.* Let `j : U₀ ↪ C₀` be a dense open immersion of
smooth geometrically connected curves and `F` lisse and punctually `ι`-pure of weight `w` on
`U₀`. Then `H_c^r(C, j_*F)` has weights at most `w + r` for every `r`.

Choose a dense affine open `V₀ ⊆ U₀`
(`AlgebraicGeometry.IsCurve.exists_isAffineOpen_dense_finite_compl`);
`j_*F` is the middle extension of `F|_{V₀}` from `V₀`. The affine estimate
`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine`
bounds `H_c^r(V, F)` by `w + r`; the boundary term of the localization sequence for
`V ↪ C` is concentrated in degree zero, of weights at most `w`
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite`).
So `H_c^r(C, j_*F)` is an extension of a quotient of `H_c^r(V, F)` by a subobject of the
boundary group, and `FrobeniusModule.HasWeightsAtMost.of_injective_of_exact` concludes.

That localization sequence is not available for the provisional, non-triangulated Weil
complexes; with the present coefficients `H_c^r(C, j_*F)` is zero, which is how the statement is
proved here. (blueprint: `prop-a1-middle-extension-curve-upper`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_directImage
    (ι : PadicAlgCl l →+* ℂ) {F : WeilSheaf k₀ l U} (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (((directImage j).obj F).compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) :=
  have : Subsingleton (((directImage j).obj F).compactlySupportedCohomology r).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _

end MiddleExtension

end WeilSheaf

end AlgebraicGeometry
