/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible
import Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Constructible cohomology under quasi-finite lower shriek

Source: Stacks Project, More on Etale Cohomology, Tags 0GK3 and 0GKM,
finite-ring bounded-below specialization
(blueprint: lem-weil-pbc-etale-quasifinite-shriek-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Quasi-finite finitely presented lower shriek preserves constructible cohomology.
Source: Stacks Project, Tags 0GK3 and 0GKM
(blueprint: lem-weil-pbc-etale-quasifinite-shriek-constructible).

Proof plan:
1. Use `lem-weil-pbc-quasifinite-fp-finite-factorization` to factor the morphism
   as a quasi-compact open immersion followed by a finite finitely presented morphism.
   The latter is proper by `lem-weil-pbc-finite-morphism-permanence`.
2. Extension by zero preserves constructibility: transport the given strata through the
   open immersion and add its closed complement with constant zero value. The old parts
   remain constructible by retrocompactness. The restrictions are identified using
   `lem-weil-pbc-extension-by-zero-unit-iso`, `lem-weil-pbc-extension-by-zero-stalks`,
   `lemma-openclosed-stalk-upperstar`, and
   `lem-weil-pbc-sets-etale-iso-on-geometric-stalks`.
3. Finite direct image and open extension by zero are exact by
   `lemma-weil-pbc-finite-direct-image-exact` and
   `lem-weil-pbc-extension-by-zero-exact`. Thus cohomology in degree q is the finite
   pushforward of the extension by zero of the original cohomology in degree q.
   Exactness preserves the lower bound and needs no upper bound or Tor hypothesis.
4. Apply `lem-weil-pbc-finite-fp-pushforward-constructible` in each degree, then
   `lem-weil-pbc-etale-shriek-compactification-independence` to pass to every compactification.
-/
theorem constructibleCohomology_lowerShriek_of_quasiFinite
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace B] [QuasiSeparatedSpace B] (h : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [QuasiSeparated h] [LocallyOfFinitePresentation h] (hqf : h.IsQuasiFinite)
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (c : Compactification h) [QuasiCompact c.i] :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  sorry

/-- The closed-immersion consequence of quasi-finite constructibility.
Source: Stacks Project, Tags 035C, 01TD, 0GK3 and 0GKM
(blueprint: lem-weil-pbc-etale-quasifinite-shriek-constructible).

Proof plan (step 5 of the node): a closed immersion is finite by
`lem-weil-pbc-closed-immersion-finite`, hence of finite type and separated. Its fibres are
empty or spectra of residue fields, so every fibre point is isolated. Apply the preceding
quasi-finite statement, retaining finite presentation and the qcqs scheme assumptions. -/
theorem constructibleCohomology_lowerShriek_of_isClosedImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace B] [QuasiSeparatedSpace B] (h : T ⟶ B)
    [IsClosedImmersion h] [LocallyOfFinitePresentation h]
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (c : Compactification h) [QuasiCompact c.i] :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
