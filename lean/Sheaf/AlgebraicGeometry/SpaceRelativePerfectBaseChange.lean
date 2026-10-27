/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.AlgebraicGeometry.SpaceRelativePerfectGeneral
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat

/-! # Étale locality and base change of relative perfectness

Source: Stacks Project, More on Morphisms of Spaces, Tags 0DKN, 0DKQ and 0DKT;
Derived Categories of Spaces, Tags 08JL and 0DKD
(blueprint: lem-sfb-space-relative-perfect-base-change).
The ambient derived categories are the already specified equivalent small ringed models.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative perfectness implies quasi-coherent cohomology.
Source: Stacks, Tags 0DKN and 08JL
(blueprint: lem-sfb-space-relative-perfect-base-change).
Proof: choose bounded-above finite-free models on étale charts. Each term is
quasi-coherent; kernels, images and cokernels of maps of quasi-coherent modules
are quasi-coherent. Thus each cohomology sheaf is quasi-coherent on every chart.
Quasi-coherence descends along the chart covering, giving the stated predicate. -/
theorem perfectRelativeToSpace_quasiCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : MapIsFlat f) (hfp : MapIsLocallyOfFinitePresentation f)
    [HasDerivedCategory.{w} X.SmallModules] (K : X.DerivedModules)
    (hK : IsPerfectRelativeToSpace f K) : X.derivedQCohProperty K := by
  sorry

/-- Étale locality on both source and target. In every étale commutative diagram
relative perfectness restricts, and a surjective source chart detects it.
Source: Stacks, Tag 0DKQ
(blueprint: lem-sfb-space-relative-perfect-base-change).
Proof: on compatible affine charts restriction retains the bounded-above finite-free
models. The restricted inverse-image structure sheaf is the inverse image from the
target chart. Geometric stalks have exactly the same rings and test Tor amplitude
against all stalk modules, by lem-sfb-space-ring-sheaf-tor-amplitude-stalk-test and
lem-sfb-space-strict-local-flatness. Hence the local intervals restrict unchanged.
Conversely a surjective étale source cover gives local models and local Tor bounds
at every point. Covers compose and these conditions are local, so they descend.
Target charts may be arbitrary étale maps; no target-surjectivity is needed. -/
theorem perfectRelativeToSpace_etale_local {S : Scheme.{u}}
    {X Y U V : AlgebraicSpace S} (f : X ⟶ Y) (h : U ⟶ V)
    (a : U ⟶ X) (b : V ⟶ Y) (ha : IsEtale a.hom.hom) (hb : IsEtale b.hom.hom)
    (comm : a ≫ f = h ≫ b) (hf : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w'} U.SmallModules]
    (K : X.DerivedModules) :
    (IsPerfectRelativeToSpace f K →
      IsPerfectRelativeToSpace h ((derivedTensorPullback a).obj K)) ∧
    (IsSurjective a.hom.hom →
      (IsPerfectRelativeToSpace h ((derivedTensorPullback a).obj K) →
        IsPerfectRelativeToSpace f K)) := by
  sorry

/-- Arbitrary derived base change preserves relative perfectness.
The square is any realization of the sheaf fibre product, including identity and empty cases.
Source: Stacks, Tag 0DKT; Derived Categories of Spaces, Tag 0DKD
(blueprint: lem-sfb-space-relative-perfect-base-change).
Proof:
1. Fibre products of algebraic spaces exist and preserve étale covering charts.
Flatness of f' is stable under base change. Local finite presentation follows on
scheme presentations by the presentation criterion and its scheme base-change clause.
2. Pull a local bounded-above finite-free model back to the resulting charts.
It is K-flat by lem-pc-bounded-above-flat-kflat-site; restriction preserves the
K-flat resolution by lem-sfb-ringed-site-restriction-kflat. Tensor pullback sends
O^r to O^r and applies the structural ring map to every matrix differential.
Thus the derived pullback is pseudo-coherent.
3. On a chart with Tor interval [a,b], the flat case of
lem-sfb-space-tor-independent-relative-amplitude gives the same interval over
(f') inverse O_Y'. The map g remains arbitrary. The pulled-back charts cover X',
so these intervals are locally finite. This proves relative perfectness.
The zero complex and empty charts use [0,0]. -/
theorem perfectRelativeToSpace_baseChange {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (square : IsPullback g'.hom f'.hom f.hom g.hom)
    (hf : MapIsFlat f) (hfp : MapIsLocallyOfFinitePresentation f)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w'} X'.SmallModules]
    (K : X.DerivedModules) (hK : IsPerfectRelativeToSpace f K) :
    IsPerfectRelativeToSpace f' ((derivedTensorPullback g').obj K) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
