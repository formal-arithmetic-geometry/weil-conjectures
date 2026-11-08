/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Submission.WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.CategoryTheory.Abelian.RightDerived
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSections
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Submission.WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Submission.WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
import Mathlib.CategoryTheory.Functor.EpiMono
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Submission.WeilConjectures.AlgebraicGeometry.LocalStalkSectionsComparisonMap
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageSmallUniverse
import Mathlib.Algebra.Category.Grp.Ulift
import Submission.WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.CategoryTheory.Presentable.Directed
import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteCoverFactorizationDescent
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Submission.WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import Submission.WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Topology.Sheaves.Abelian
import Submission.WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle
import Submission.WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.GabberCriterionDegree

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Gabber's criterion for vanishing of higher etale cohomology

Source: Stacks Project, Etale Cohomology, Lemma 0GY0, label `lemma-gabber-criterion`
(blueprint: lem-weil-pbc-gabber-criterion).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- If all prime localizations of `R` are strictly henselian and the degree-one
restriction map for the two principal opens covering `D(f + g)` has zero kernel,
then every positive-degree etale cohomology group of `F` vanishes.

The two target sheaves in the kernel hypothesis are iterated inverse images of `F`.
The canonical composition isomorphism identifies them with its inverse images along
`D(f * (f + g)) → Spec R` and `D(g * (f + g)) → Spec R`; these additive
isomorphisms preserve zero, so the displayed hypothesis is precisely the restriction
kernel condition in the source.

Source: Stacks Project, Etale Cohomology, Lemma 0GY0, label `lemma-gabber-criterion`
(blueprint: lem-weil-pbc-gabber-criterion).

Proof:
1. Identify `D(h)` with `Spec R_h` using
   `lem-weil-pbc-principal-localization-open-immersion`. Its local rings are `R_p`
   (`lem-weil-pbc-spec-domain-stalks-function-field`), hence strictly henselian.
   Apply `lem-weil-pbc-gabber-strict-henselian-zariski-comparison` (Stacks 09AX)
   on `Spec R` and every principal open.
2. Induct simultaneously on the degree over all `D(h)` with `R` fixed: the claim
   is vanishing for `1 ≤ q ≤ i`, and `i = 0` is vacuous. Fix a degree-`i` class
   `ξ` on `D(h)`. Principal opens of `R_h` are opens `D(ah)` of `Spec R`.
3. Set `I_h = {f | ξ restricts to zero on D(hf)}`. By
   `lem-weil-pbc-zariski-cohomology-locally-zero`, every prime avoiding `h` avoids
   some element of `I_h`. Restriction shows closure under multiplication by `R`.
4. In degree one apply the kernel hypothesis to `hf` and `hg`. The target opens
   `D(h²f(f+g))` and `D(h²g(f+g))` equal `D(hf(f+g))` and `D(hg(f+g))`,
   respectively, so `f, g ∈ I_h` implies `f + g ∈ I_h`.
5. In higher degree use `lem-weil-pbc-etale-mayer-vietoris` for
   `D(h(f+g)) = D(hf(f+g)) ∪ D(hg(f+g))`, with intersection `D(hfg(f+g))`.
   Its degree-`i-1` cohomology vanishes by induction, giving addition closure.
   Thus `I_h` is an ideal. Every prime containing it contains `h`, so `h` lies
   in its radical. Some `h^N` lies in `I_h`, and `D(h^(N+1)) = D(h)` gives
   `ξ = 0`. The empty open when `h = 0` causes no exception. Take `h = 1`
   to conclude vanishing on `Spec R` in every positive degree. -/
theorem gabberCriterion
    (R : Type u) [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsStrictlyHenselianLocalRing (Localization.AtPrime p))
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfg : ∀ (f g : R) (x : Sheaf.H
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1),
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right f (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right g (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
        x = 0) :
    ∀ (q : ℕ), 0 < q → Subsingleton (Sheaf.H F q) := by
  intro q hq
  exact gabberCriterion_degree R hR F hfg q hq

end AlgebraicGeometry.Etale
