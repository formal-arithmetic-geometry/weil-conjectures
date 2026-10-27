/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.CategoryTheory.DerivedLimitEventuallyIso
import WeilConjectures.CategoryTheory.Triangulated.MilnorBoundaryFactorization
import WeilConjectures.CategoryTheory.Triangulated.MilnorProjectionFactorization

/-! # Stationary tower cohomology under local ringed-site bounds

Source: Stacks Project, Cohomology on Sites, Tag 0D6T,
`lemma-olsson-laszlo-modified`, with Situation 0D6R
(blueprint: lem-sfb-ringed-local-bound-stationary-limit-cohomology).

The resolution-derived limit is written as the localization of the termwise limit of
any K-injective tower resolution. Its canonical projection is the limit projection
followed by the inverse of the levelwise resolution quasi-isomorphism. The local bound
is expressed by its defining computation on K-injective resolutions of a sheaf in degree
zero; it is a bound on derived sections, not on sections of cohomology sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The canonical projections from the resolution-derived limit induce the stationary
cohomology isomorphisms, and the limit has all cohomology in the weak Serre class.

Source: Stacks Project, Cohomology on Sites, Tag 0D6T and Situation 0D6R
(blueprint: lem-sfb-ringed-local-bound-stationary-limit-cohomology).

Proof:
1. Use prop-pur-kinjective-resolutions-exist to represent every derived object by a
K-injective complex. Exact abelian sheafification (lem-weil-pbc-sheafification-exact)
identifies the sheafification of the derived-section cohomology presheaf with its
cohomology sheaf. The module action is def-weil-presheaf-modules-sheafification.
2. By lem-pc-sites-sheafification-underlying-sets and
lem-weil-pbc-site-sheafification-sections-local, sheaf sections have local representatives
and zero is detected locally. Refine these coverings into the prescribed cofinal systems.
3. Fix j and V. Replace d_V by max(0,d_V), and choose N beyond the finitely many
stationarity thresholds in [j-d_V-2,j+1]. Apply
lem-sfb-ringed-bounded-below-section-window-comparison in degrees j-1 and j to every
member W of a prescribed covering of V. Derived sections of the tail stabilize in these
two degrees, uniformly in W; the lower bounds of the tower terms need not be uniform.
4. The specified resolution-derived limit has its Roos triangle by
lem-weil-pbc-ringed-strict-tower-homotopy-limit and def-weil-derived-limit.
Apply lem-kun-site-rgamma-derived-limit to retain this triangle and its projections
after derived sections over W. Its cohomology maps give the compatible map to the limit.
5. The first derived limit in degree j-1 vanishes by lem-pc-derived-limit-eventually-iso.
Then lem-pc-milnor-boundary-factorization makes the comparison injective, and
lem-pc-milnor-projection-factorization makes it surjective. Projection to level N is
invertible on a stationary tail, so the actual derived-section projection is invertible.
6. For any n beyond the degree-j threshold, cover a kernel section by V, choose
N at least n and the finite-window threshold for V, and represent the section locally.
Refine to detect its zero image at N and then into the cofinal collection. Step 5 kills
the representative. Separatedness kills the original section, proving injectivity.
7. Lift a target section from n to N using stationary sheaf cohomology. Represent it
locally and refine into the cofinal collection. Step 5 lifts its representatives from N
to the limit. Step 6 makes the lifts compatible, so the sheaf axiom glues them. The
projection is therefore an isomorphism. Strict fullness transfers membership in the
weak Serre class from each stabilized tower term to every cohomology sheaf of the limit.
-/
theorem ringedLocalBound_stationaryLimit_cohomology
    {C : Type c} [Category.{v} C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings)
    [EssentiallySmall.{max c v r} C]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max c v r}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J.toGrothendieck RingCat.{max c v r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r} R)]
    (P : ObjectProperty (ringedSiteModules.{max c v r} R))
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (B : Set C)
    (_hB : ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f → V ∈ B)
    (_hlocal : ∀ V : C, V ∈ B → ∃ d : ℤ, ∃ Cov : Set (Presieve V),
      (∀ S ∈ Cov, S ∈ J V) ∧
      (∀ T : Presieve V, T ∈ J V → ∃ S ∈ Cov, S ≤ Sieve.generate T) ∧
      ∀ S ∈ Cov, ∀ (W : C) (f : W ⟶ V), S f →
        ∀ (p : ℤ), d < p → ∀ (F : ringedSiteModules.{max c v r} R), P F →
          ∀ (K : CochainComplex (ringedSiteModules.{max c v r} R) ℤ)
            (ι : (CochainComplex.singleFunctor (ringedSiteModules.{max c v r} R) 0).obj F
              ⟶ K), K.IsKInjective → QuasiIso ι →
            IsZero ((((SheafOfModules.toSheaf R ⋙
              sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max c v r} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K).homology p))
    (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} R) ℤ)
    (ι : X ⟶ I) (_hI : I.IsKInjective) [QuasiIso ι]
    (_hbounded : ∀ n : ℕ, ∃ b : ℤ, ∀ j : ℤ, j < b →
      IsZero ((X.asFunctor.obj (op n)).homology j))
    (_hP : ∀ (n : ℕ) (j : ℤ), P ((X.asFunctor.obj (op n)).homology j))
    (threshold : ℤ → ℕ)
    (_hstationary : ∀ (j : ℤ) (n : ℕ), threshold j ≤ n →
      IsIso (HomologicalComplex.homologyMap
        (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) j)) :
    (∀ (j : ℤ) (n : ℕ), threshold j ≤ n →
      IsIso ((DerivedCategory.homologyFunctor (ringedSiteModules.{max c v r} R) j).map
        (DerivedCategory.Q.map (limit.π I.asFunctor (op n)) ≫
          inv (DerivedCategory.Q.map
            ((Functor.mapHomologicalComplex
              ((evaluation ℕᵒᵖ (ringedSiteModules.{max c v r} R)).obj (op n))
              (ComplexShape.up ℤ)).map ι))))) ∧
    ∀ j : ℤ, P ((DerivedCategory.homologyFunctor (ringedSiteModules.{max c v r} R) j).obj
      (DerivedCategory.Q.obj (limit I.asFunctor))) := by
  sorry

end CategoryTheory
