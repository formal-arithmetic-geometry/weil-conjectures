/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CurvePureExactness.Exactness

import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Statement

/-!
# Exactness at a fixed pure weight (sketch statement)

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-the-weight-bound-on-the-affine-line/sk-p-dl-a1-exact/
_section.md and sk-p-dl-a1-exact.proof.md, statement and proof
(blueprint: sk-p-dl-a1-exact).  In the condensed coefficient conventions of
`rem-dl-a1-conventions`, ordinary direct image along the dense open immersion is exact on a
short exact sequence of lisse Weil modules whose two outer terms are punctually pure of the
same weight.  The statement uses the native model and direct image of
`Sheaf.DeligneLaumon.AffineLine.Exactness`; no legacy adic Weil-sheaf model is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CurvePureExactness

set_option linter.style.haveILetI false

/-- In the conventions of `rem-dl-a1-conventions`, let `j₀ : U₀ ⟶ C₀` be a dense
open immersion into a smooth relative curve.  If
`0 → F₁ → F → F₂ → 0` is a short exact sequence of lisse condensed Weil modules on
`U₀`, with `F₁` and `F₂` punctually pure of one common weight, then native ordinary
direct image along `j₀` is exact.  This is the Lean rendering of the sketch statement.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-the-weight-bound-on-the-affine-line/sk-p-dl-a1-exact/
_section.md, statement and proof (blueprint: sk-p-dl-a1-exact).

Proof (the node's two steps).
Step 1: `j₀` is quasi-compact, so no hypothesis is added. `C₀` is smooth over `k₀`, hence
locally of finite presentation, with an affine cover by spectra of finitely generated
`k₀`-algebras; these are Noetherian, so every open of such a chart is quasi-compact.
Refine the cover inside an affine open `V` of `C₀` by principal opens
(`A[1/f] = A[t]/(ft - 1)` is again of finite type); quasi-compactness of `V` selects
finitely many charts, whose intersections with `U₀` are quasi-compact, and their finite
union is `j₀⁻¹(V)`.
Step 2: apply the detailed theorem `shortExact_directImage` (p-dl-a1-exact) to `j₀`, with
Step 1 for its quasi-compactness instance and the reduced closed complement of `U₀` as its
complement datum, and keep its last conclusion: the connecting map
`δ : j_*F₂ → R¹j_*F₁` vanishes on `U₀`; at a missing point the source has weights at
most `w` by boundary semicontinuity, the target has weights at least `w + 2` by local
duality applied to `F₁^∨`, and the Frobenius-stable image of `δ` lies across this strict
gap, so it is zero. -/
theorem shortExact_directImage_sketch
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {U₀ C₀ : Over (Spec (.of D.k₀))}
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (S : ShortComplex (Modules D l U₀)) (hS : S.ShortExact)
    (h₁ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) S.X₁.carrier)
    (h : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) S.X₂.carrier)
    (h₂ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) S.X₃.carrier)
    (w : ℝ) (p₁ : pureOnFiniteTypeOpens D l U₀ S.X₁ iota w)
    (p₂ : pureOnFiniteTypeOpens D l U₀ S.X₃ iota w) :
    (S.map (directImage D l j₀)).ShortExact := by
  letI : IsLocallyNoetherian (Spec (.of D.k₀)) := inferInstance
  letI : Smooth C₀.hom := SmoothOfRelativeDimension.smooth 1 C₀.hom
  letI : LocallyOfFinitePresentation C₀.hom := by infer_instance
  letI : LocallyOfFiniteType C₀.hom :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := C₀.hom)).mp inferInstance
  letI : IsLocallyNoetherian C₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian C₀.hom
  letI : QuasiCompact j₀.left := Etale.quasiCompact_of_isImmersion j₀.left
  obtain ⟨Z, i, hi, hcomplement⟩ :=
    exists_isClosedImmersion_range_eq_compl j₀.left
  let Z₀ : Over (Spec (.of D.k₀)) := Over.mk (i ≫ C₀.hom)
  let i₀ : Z₀ ⟶ C₀ := Over.homMk i rfl
  haveI : IsClosedImmersion i₀.left := hi
  exact (shortExact_directImage D l hl iota j₀ i₀ hcomplement S hS h₁ h h₂ w p₁ p₂).2.2.2

end WeilConjectures.CurvePureExactness
