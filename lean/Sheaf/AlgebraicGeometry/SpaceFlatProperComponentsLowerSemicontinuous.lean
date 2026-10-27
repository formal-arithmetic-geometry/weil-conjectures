/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceSteinFactorizationAffine
import Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Lower semicontinuity of geometric component counts for algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0E1D,
`lemma-proper-flat-nr-geom-conn-comps-lower-semicontinuous`, with a scheme target
(blueprint: lem-sfb-space-flat-proper-components-lower-semicontinuous).

The fibre is the actual sheaf pullback along the residue-field map followed by a chosen
algebraic closure. Its points carry the existing atlas topology. `ConnectedComponents`
counts maximal nonempty connected subsets, including no components for an empty fibre.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Geometric component counts of a proper flat finitely presented algebraic space over a
scheme are finite and lower semicontinuous, for any choice of residue-field closures.
Source: Stacks, More on Morphisms of Spaces, Tag 0E1D
(blueprint: lem-sfb-space-flat-proper-components-lower-semicontinuous).

Proof:
1. Proper base change and the unrestricted first clause of
   lem-sfb-space-proper-global-algebra-components give finitely many clopen components
   in every geometric fibre, without assuming reducedness.
2. Counts are unchanged by scheme base change or enlarging the algebraically closed field:
   embed the fields in a common algebraically closed extension using
   lem-weil-common-extension-fields; reassociate sheaf fibre products using
   lem-trf-space-fibre-products-etale-covers and apply
   lem-sfb-space-sepclosed-components-base-change to both original closures.
3. Restrict to an affine open of the target, using lem-sfb-space-flat-proper-fp-locality.
   Apply lem-sfb-space-stein-factorization-affine and
   lem-sfb-space-stein-finite-fibres-residue-fields. The integral Stein base splits into
   finitely many clopen pieces after an affine etale neighbourhood by
   lem-weil-pbc-integral-fibre-etale-splitting. Each piece has one point over the chosen
   point, with purely inseparable residue extension.
4. Pull these clopen pieces back to open subspaces of the source. They form a finite
   disjoint clopen partition, preserved by base change, by def-a1-space-open-subspace
   and lem-a1-space-point-open-calculus.
5. Over the chosen algebraic closure each Stein piece has exactly one point: radiciality
   gives at most one; the unique-root embedding of its purely inseparable residue field
   gives at least one (in characteristic zero the extension is trivial). The Stein
   theorem gives nonempty connected fibres. Apply lem-sfb-space-scheme-fibre-topology
   and fibre-product reassociation to identify each source piece with such a fibre.
6. The nonempty connected clopen pieces are exactly the connected components. Their
   number equals the original count by step 2. For count zero the desired inequality
   holds throughout the base; this includes empty fibres.
7. Each source piece is flat and locally finitely presented: use
   lem-sfb-space-local-properties-chart-test and restriction to open scheme charts.
   At an affine finite-presentation witness C, a principal open has presentation
   C[z]/(zh-1), so the restriction retains local finite presentation.
   By lem-sfb-flat-lfp-space-universally-open every piece has open image containing
   the chosen point.
8. Intersect the finitely many open images. Every geometric fibre there meets each
   clopen piece by the point-image formula of lem-a1-space-point-open-calculus, hence
   has at least that many components. The etale neighbourhood map is open by
   lem-weil-pbc-etale-morphism-open-map; take the image of the intersection and use
   step 2 to descend the inequality to the original scheme target. -/
theorem geometricComponentCount_lowerSemicontinuous
    {S : Scheme.{u}} (T : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
    (hf : MapIsProper f) (hflat : MapIsFlat f)
    (hlfp : MapIsLocallyOfFinitePresentation f)
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (Ω : T.left → Type u) [∀ t : T.left, Field (Ω t)]
    [∀ t : T.left, Algebra (T.left.residueField t) (Ω t)]
    [∀ t : T.left, IsAlgClosure (T.left.residueField t) (Ω t)] :
    ∃ n : T.left → ℕ,
      (∀ t : T.left,
        Finite (ConnectedComponents (Point (Limits.pullback f.hom
            ((Scheme.fppfTopology.over S).yoneda.map
              (Over.homMk
                (U := Over.mk
                  ((Spec.map (CommRingCat.ofHom
                    (algebraMap (T.left.residueField t) (Ω t))) ≫
                    T.left.fromSpecResidueField t) ≫ T.hom))
                (V := T)
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (T.left.residueField t) (Ω t))) ≫
                  T.left.fromSpecResidueField t) rfl))).obj)) ∧
        n t = Nat.card (ConnectedComponents (Point (Limits.pullback f.hom
            ((Scheme.fppfTopology.over S).yoneda.map
              (Over.homMk
                (U := Over.mk
                  ((Spec.map (CommRingCat.ofHom
                    (algebraMap (T.left.residueField t) (Ω t))) ≫
                    T.left.fromSpecResidueField t) ≫ T.hom))
                (V := T)
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (T.left.residueField t) (Ω t))) ≫
                  T.left.fromSpecResidueField t) rfl))).obj))) ∧
      (∀ t : T.left, IsEmpty (Point (Limits.pullback f.hom
            ((Scheme.fppfTopology.over S).yoneda.map
              (Over.homMk
                (U := Over.mk
                  ((Spec.map (CommRingCat.ofHom
                    (algebraMap (T.left.residueField t) (Ω t))) ≫
                    T.left.fromSpecResidueField t) ≫ T.hom))
                (V := T)
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (T.left.residueField t) (Ω t))) ≫
                  T.left.fromSpecResidueField t) rfl))).obj) → n t = 0) ∧
      ∀ t : T.left, ∃ V : T.left.Opens, t ∈ V ∧
        ∀ v : T.left, v ∈ V → n t ≤ n v := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
