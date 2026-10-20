/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.GroupTheory.Torsion
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.Paper.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison

/-!
# Compact-support projection with arbitrary finite primary coefficients

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Project, Tag 0F0G
(blueprint: lem-sp-finite-ring-compact-support-projection).

The canonical coefficient realization changes only the presentation of module sheaves.
The projection arrow below is the published counit-defined compactification projection
transported by that realization, on the ordinary unbounded intrinsic derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical compact-support projection is invertible for bounded intrinsically
constructible complexes over every finite primary commutative ring. A compactification
records exactly `j = c.i`, `p = c.g`, `Xbar = c.Z`, and `f = j ≫ p` by `c.comm`.
The coefficient realization is the canonical extension of fixed scalar actions to
locally constant scalar sections; it changes no objects or morphisms mathematically.
Naturality in `M,K` comes from `projectionMapOfCompactification`, a transformation of
bifunctors, and the functors used to transport it.
Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Tag 0F0G
(blueprint: lem-sp-finite-ring-compact-support-projection).

Proof (the node's six steps):
1. By lem-weil-pbc-finite-ring-constructible-derived-origin, choose bounded
   constructible etale origins M0,K0 for M,K, using intrinsic constructibility over
   the given finite ring. No finite Tor amplitude or DVR presentation is required.
2. Put E = j! M0. The exact etale and pro-etale extensions by zero act degreewise
   (lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero).
   Apply lem-cbc-proetale-extension-zero-comparison in each degree; exactness
   descends it and its inverse to identify the pro-etale realization of E with j! M.
3. Form H = E tensor-derived p* K0 in the unbounded etale category.
   lem-weil-pbc-comparison-pullback and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback identify its realization with
   the corresponding pro-etale tensor. They also identify the source tensor.
   These comparisons apply even if H is unbounded below.
4. The ring is torsion by its primary annihilation hypothesis. Stacks 0F0G
   (lem-kun-0f0g) makes the specified etale proper projection an isomorphism.
   lem-sfb-unbounded-direct-image-comparison applies to E and H: the field is
   algebraically closed, the prime is invertible, and p is finite type between
   finite-type schemes. Its comparison is the canonical derived counit mate.
5. lem-weil-pbc-ringed-exchange-tensor-coherence for the etale/pro-etale square
   identifies the two projection maps through those comparison isomorphisms.
   No cartesian-square hypothesis is needed. Hence the actual pro-etale proper
   projection is invertible. Naturality transports it to the given M,K.
6. lem-cbc-extension-zero-projection-formula makes the canonical open factor
   invertible on unbounded categories. Proper pushforward preserves its inverse.
   Compose with step 5 and the pullback-composition isomorphism. Every factor
   is natural in both inputs, so the specified composite is natural as well. -/
theorem isIso_finiteRingCompactSupportProjection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (_hl : l.Prime) (_hlp : l ≠ D.p)
    (R : Type u) [CommRing R] [Finite R]
    (n : ℕ) (_hn : 1 ≤ n) (_hR : ∀ r : R, (l ^ n) • r = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (c : Compactification f)
    [c.Z.Over (Spec (.of D.k))]
    [IsSeparated (c.Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D.k))]
    [QuasiCompact (c.Z ↘ Spec (.of D.k))]
    [c.i.IsOver (Spec (.of D.k))] [c.g.IsOver (Spec (.of D.k))]
    (M : proEtaleDerivedCategory X R) (K : proEtaleDerivedCategory Y R)
    (_hMc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X R
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X R)) i).obj M))
    (_hMb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X R)) i).obj M))
    (_hKc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y R
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y R)) i).obj K))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y R)) i).obj K)) :
    IsIso (((finiteRingCompactSupportProjection R c).app M).app K) := by
  sorry

end AlgebraicGeometry.Scheme
