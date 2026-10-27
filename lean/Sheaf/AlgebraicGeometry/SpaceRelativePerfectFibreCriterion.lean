/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePerfect
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.SpaceRelativePerfectBaseChange
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.RingTheory.Flat.Stability
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Relative perfection detected by lower bounds on residue fibres

Source: Stacks Project, More on Morphisms of Spaces, Tag 0GFK,
lemma-bounded-on-fibres (blueprint: lem-sfb-space-relative-perfect-fibre-criterion).
The auxiliary base scheme only places all spaces in one existing fppf sheaf category.
The lower bounds are local covering-sieve bounds, with no uniform bound across fibres.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w wF

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical residue-field spectrum map, as a map of represented algebraic spaces.
Source: Stacks, Tag 0GFK, the map Spec κ(s) → S
(blueprint: lem-sfb-space-relative-perfect-fibre-criterion). -/
def residueFieldSpaceMap {B : Scheme.{u}} (S : Over B) (s : S.left) :
    schemeSpace (Over.mk (S.left.fromSpecResidueField s ≫ S.hom)) ⟶ schemeSpace S :=
  ObjectProperty.homMk ⟨yoneda.map (Over.homMk (S.left.fromSpecResidueField s) rfl)⟩

/-- The actual fibre X_s = X ×_S Spec κ(s), in the same ambient sheaf category.
Source: Stacks, Tag 0GFK, definition of X_s
(blueprint: lem-sfb-space-relative-perfect-fibre-criterion). -/
abbrev residueFibre {B : Scheme.{u}} (S : Over B) {X : AlgebraicSpace B}
    (f : X ⟶ schemeSpace S) (s : S.left) : AlgebraicSpace B :=
  enlargedFibreProduct f (residueFieldSpaceMap S s)

/-- The specified first projection i_s : X_s → X of the actual fibre product.
Source: Stacks, Tag 0GFK, the fibre inclusion
(blueprint: lem-sfb-space-relative-perfect-fibre-criterion). -/
abbrev residueFibreInclusion {B : Scheme.{u}} (S : Over B) {X : AlgebraicSpace B}
    (f : X ⟶ schemeSpace S) (s : S.left) : residueFibre S f s ⟶ X :=
  enlargedFibreProductFst f (residueFieldSpaceMap S s)

/-- A pseudo-coherent complex on a flat locally finitely presented space over a scheme
has locally finite relative Tor amplitude if and only if it and all its derived residue
fibres are locally bounded below. The assumed pseudo-coherence makes the Tor condition
exactly relative perfection, using the existing affine-chart predicate.
Source: Stacks, Tag 0GFK, lemma-bounded-on-fibres
(blueprint: lem-sfb-space-relative-perfect-fibre-criterion).
Proof:
1. Relative perfection supplies a local Tor interval. Testing with the inverse-image
structure sheaf gives a lower bound for K. Apply
lem-sfb-space-relative-perfect-base-change to Spec κ(s) → S and repeat the same test
on the fibre. This proves the implication from the right to the left.
2. Conversely use lem-sfb-space-etale-presentation-property-criterion and
lem-sfb-scheme-etale-source-target-properties to pass to affine source and target charts.
By def-sbc-locally-finite-presentation and lem-weil-pbc-flat-ring-map-iff-flat-affine
these have a flat finitely presented ring map R → A. Relative perfection is etale local
by lem-sfb-space-relative-perfect-base-change.
3. By lem-sfb-affine-etale-derived-module-realization realize the chart restriction as
an A-complex C, retaining its lower bound. The comparison of
lem-sfb-derived-etale-zariski-equivalence, lem-sfb-etale-pseudocoherence-descent and
lem-pc-affine-pseudo-coherent-criterion gives a bounded-above finite-free model P of C.
4. The comparisons of lem-sfb-space-derived-etale-chart-calculus and
lem-pc-flat-complex-derived-pullback identify the restricted fibre with P ⊗_R κ(p).
The terms are R-flat by lem-pc-module-flat-transitive, and P is R-K-flat by
lem-pc-module-bounded-flat-kflat, so this is C ⊗^L_R κ(p).
5. For each prime separately, take a finite subcover of the affine fibre, using
lem-weil-pbc-etale-morphism-open-map and lem-weil-pbc-affine-scheme-qcqs. The minimum
of its lower bounds works globally on that fibre, by the jointly conservative stalks of
lem-sfb-space-ring-sheaf-tor-amplitude-stalk-test. Exact faithful realization in
lem-sfb-affine-etale-derived-module-realization gives the same bound for the ring complex.
For an empty fibre any bound works; no bound uniform in p is asserted.
6. Apply lem-sfb-ring-relative-perfect-fibre-criterion. Transport its finite relative Tor
amplitude through lem-trf-affine-relative-tor-amplitude-criterion and
lem-sfb-etale-relative-tor-comparison, then descend using the etale locality of
lem-sfb-space-relative-perfect-base-change. All inverse-image-ring modules are tested. -/
theorem relativePerfect_iff_locally_boundedBelow_fibres {B : Scheme.{u}} (S : Over B)
    {X : AlgebraicSpace B} (f : X ⟶ schemeSpace S)
    (hf : MapIsFlat f) (hfp : MapIsLocallyOfFinitePresentation f)
    [HasDerivedCategory.{w} X.SmallModules]
    [∀ s : S.left, HasDerivedCategory.{wF} (residueFibre S f s).SmallModules]
    (K : X.DerivedModules) (hqc : X.derivedQCohProperty K) (hpc : X.IsPseudoCoherent K) :
    ((∀ V : X.SmallEtaleModel, ∃ T : Sieve V, T ∈ X.smallEtaleModelTopology V ∧
        ∀ (U : X.SmallEtaleModel) (g : U ⟶ V), T g →
          ∃ c : ℤ, ∀ n : ℤ, n < c →
            IsZero ((SheafOfModules.overFunctor.{u} X.smallStructureRings U).obj
              ((DerivedCategory.homologyFunctor X.SmallModules n).obj K))) ∧
      ∀ s : S.left, ∀ V : (residueFibre S f s).SmallEtaleModel,
        ∃ T : Sieve V, T ∈ (residueFibre S f s).smallEtaleModelTopology V ∧
          ∀ (U : (residueFibre S f s).SmallEtaleModel) (g : U ⟶ V), T g →
            ∃ c : ℤ, ∀ n : ℤ, n < c →
              IsZero ((SheafOfModules.overFunctor.{u}
                (residueFibre S f s).smallStructureRings U).obj
                ((DerivedCategory.homologyFunctor (residueFibre S f s).SmallModules n).obj
                  ((derivedTensorPullback (residueFibreInclusion S f s)).obj K)))) ↔
      IsPerfectRelativeToScheme S f K := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
