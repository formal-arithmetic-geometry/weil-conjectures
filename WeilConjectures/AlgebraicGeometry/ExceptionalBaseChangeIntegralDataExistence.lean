/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalBaseChangeIntegralComparisons

/-! # Integral coordinates for exceptional base change

Source: latest blueprint, tower exceptional base change, proof (3).
(blueprint: stage3-sp-exceptional-integral-data-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures Opposite
namespace AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Construct the integral operation and coordinate package. This asserts no base-change
map, invertibility of the tower mate, or conclusion about its integral transpose.
Source: latest blueprint tower exceptional base change, proof (3).

Proof: rank one identifies E with Q_l through its given algebra structure, so the
integral completion bridge applies to the current constructible categories. For
all four schemes take the actual reduction towers and their normalized-equivalence
adjunctions. The completion criterion gives normalized, uniformly constructible
reductions and invertible reconstruction units; restriction of the equivalence
gives fully faithful reduction. Use one cofinal ell-power restriction construction
on all four schemes. Its quotient-generator formula determines each cofinal
reduction comparison and the pullback mate on sections. Localizing gives PullModel.
Apply integral adjunction reconstruction to c and its pulled-back compactification,
retaining the separately derived compact-support functors and their normalized
left comparisons. Restrict the tower adjunctions along the fully faithful reductions.
This supplies right, right', their comparisons, and the counit equations. Naturality
of the reconstruction counit gives right_reduction and its primed version.
Exact pullback preserves finite constant local presentations on the pulled-back
constructible strata. The same cofinal section models and the canonical completed
pullback reconstruction counit give pullComparison and pullLimit, with both
pull_normalized and pull_counit. These comparisons use whole derived systems;
no unrelated collection of finite maps is lifted. Empty schemes, zero complexes
and identity coefficient reductions use the same constructions and unit equations.
(blueprint: stage3-sp-exceptional-integral-data-existence). -/
theorem integral_data_exists
    (k : FiniteFieldDatum.{u}) (_hne : l ≠ k.p)
    (X Y X' Y' : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left)
    (a : SpTowerMate.Data l E b o q sq c)
    (_hrank : Module.finrank (Padic l) E = 1)
    [∀ z : X.left, Invertible (l : X.left.residueField z)]
    [∀ z : Y.left, Invertible (l : Y.left.residueField z)]
    [∀ z : X'.left, Invertible (l : X'.left.residueField z)]
    [∀ z : Y'.left, Invertible (l : Y'.left.residueField z)] :
    Nonempty (IntegralData l E b o q a) := by sorry

end AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
