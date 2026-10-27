module

public import WeilConjectures.DeligneLaumon.Reduction.FiniteMap
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

@[expose] public section

/-!
# Cohomology transport under finite-map reduction

Source: `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/`
`sk-thm-dl-a1-upper/lem-a1-reduction-composition.proof.md`
(blueprint: lem-a1-reduction-composition).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

/- `Spec k₀` is over itself through its identity structure (as in the side framework's
`WeilConjectures.ZetaFunction.Weights`), so that `Ra_!` along a structure morphism elaborates. -/
attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Cohomology transport under the finite-map reduction.  The hypotheses record the
smooth geometrically connected affine curve `C₀`, its smooth geometrically connected
curve compactification `C'₀`, the dense open immersion with finite complement, the
finite generically étale map to the affine line, and the lisse punctually pure Weil
sheaf.  The conclusion is the derived comparison
`RΓ_c(C, F) ≅ RΓ_c(𝔸¹, g_*j_!F)`, rendered as an isomorphism of the Weil complexes
`R(a_{C₀})_! F ≅ R(a_{𝔸¹})_! (g_*j_!F)` on `Spec k₀` (the node's `RΓ_c` is their
image under the fibre equivalence `Fib_s`), and hence the compactly supported
cohomology comparison in every integer degree.

Source: `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/`
`sk-thm-dl-a1-upper/lem-a1-reduction-composition.proof.md`
(blueprint: lem-a1-reduction-composition).

Proof: identify compactly supported sections on `C₀` with those on `C'₀` after
extension by zero; use compact-support composition and properness of the finite map
to replace `Rg_!` by `Rg_*`; use exactness of finite direct image to identify the
result with `g_*j_!F`; finally take cohomology in each integer degree. -/
theorem reductionComposition
    {C₀ C'₀ : Scheme.{u}}
    [C₀.Over (Spec (CommRingCat.of k₀))]
    [C'₀.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (C₀ ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C₀ ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C₀ ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C'₀ ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C'₀ ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C'₀ ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (CommRingCat.of k₀))]
    [IsAffine C₀]
    [SmoothOfRelativeDimension 1 (C'₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C'₀ ↘ Spec (CommRingCat.of k₀))]
    (j : C₀ ⟶ C'₀) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    (_hj : DenseRange j.base) (_hboundary : (Set.range j.base)ᶜ.Finite)
    (g : C'₀ ⟶ affineLine k₀)
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsFinite g]
    (_hgen : ∃ U : C'₀.Opens, Dense (U : Set C'₀) ∧ Etale (U.ι ≫ g))
    (ι : PadicAlgCl l →+* ℂ) (w : ℝ)
    (F : WeilSheaf k₀ l C₀) (_hF : F.IsLisse)
    (_hpure : F.IsPunctuallyPureOfWeight ι w) :
    Nonempty ((WeilComplex.derivedLowerShriek k₀ l (C₀ ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj F) ≅
      (WeilComplex.derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj ((lowerStar g).obj ((extensionByZero j).obj F)))) ∧
    ∀ i : ℤ, Nonempty ((F.compactlySupportedCohomology i).Equiv
      (((lowerStar g).obj ((extensionByZero j).obj F)).compactlySupportedCohomology i)) := by sorry

end AlgebraicGeometry.WeilSheaf
