/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatTelescope
import Sheaf.Algebra.Homology.RingedDerivedTensorNative

/-! # Affine countability after tensoring with a perfect complex

Source: Stacks Project, perfect.tex, Tag 0CRP, affine paragraph of
`lemma-countable-cohomology`; spaces-perfect.tex, Tag 0CRU, affine base case
(blueprint: lem-sfb-affine-countable-perfect-tensor).

We use the existing small affine etale ringed model, equivalent to the original
small etale module topos. Maps from its structure module are global sections.
Degree n hypercohomology is H-zero R-Gamma of the n-shift.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Spec A as its existing represented algebraic space over itself.
Source: Stacks Project, perfect.tex, Tag 0CRP, affine paragraph; spaces-perfect.tex, 0CRU
(blueprint: lem-sfb-affine-countable-perfect-tensor). -/
abbrev affineCountableEtaleSpace (A : Type u) [CommRing A] :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A))))

/-- Countable cohomology sections on Spec A remain countable after derived tensor
with an etale-locally perfect object. Neither L nor the coefficient ring is bounded
or countable by hypothesis; only the sections of the cohomology sheaves are countable.
Source: Stacks Project, perfect.tex, Tag 0CRP, affine paragraph of
`lemma-countable-cohomology`; spaces-perfect.tex, Tag 0CRU, affine base case
(blueprint: lem-sfb-affine-countable-perfect-tensor).

Proof:
1. Local bounded finite-free-retract models for Q have quasi-coherent terms, cycles,
   boundaries and cohomology, using lem-sfb-space-qcoh-kernels-colimits. Exact etale
   restriction and lem-sfb-space-derived-etale-chart-calculus give quasi-coherence of Q.
2. Use lem-sfb-affine-etale-derived-module-realization to represent L by an unbounded
   A-module complex M. Its cohomology modules are the assumed countable sections.
   Use lem-sfb-scheme-derived-etale-qcoh-comparison and lem-sfb-etale-detects-perfect
   to descend Q to a Zariski perfect object. By lem-pc-perfect-affine-bounded-projective
   it is represented by a bounded complex P of finite projective A-modules.
3. Projectives are flat by lem-weil-pbc-projective-module-flat, and
   lem-pc-module-bounded-flat-kflat makes P K-flat. Use
   lem-pc-source-kflat-module-tensor-model to compute by Tot(P tensor M), the signed
   tensor of def-pc-tensor-complex-sheaves. The comparisons of
   lem-pc-affine-derived-pullback-tensor-tilde and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback, followed by the inverse comparison
   of lem-sfb-affine-etale-derived-module-realization, identify derived sections of
   Q tensor L with this total complex. No boundedness of M is used.
4. Each P^a is a retract of A^r, by def-weil-finitely-generated-module and
   def-weil-pbc-projective-module. Tensor its inclusion and projection with M and take
   cohomology. This embeds H^j(P^a tensor M) in the finite product H^j(M)^r, which is
   countable. This also covers r = 0 and does not assume countability of A or M's terms.
5. Filter the finite complex P by upper stupid tails. The sequences of
   lem-sf-module-stupid-truncation-short-exact stay degreewise split after tensoring
   with M and totalizing. Their quotients have cohomology H^(n-a)(P^a tensor M), up to
   a constant sign. Start at the zero tail and descend finitely many times. By
   lem-weil-pbc-complex-ses-homology-long-exact, each next cohomology group has a
   countable kernel and countable image, hence is countable: choose one lift of each
   image element and use the surjection from kernel times the set of lifts.
6. The derived identification in step 3 and the symmetry of
   lem-sf-ringed-derived-native-tensor give the claimed order L tensor Q. The existing
   small ringed-model equivalence preserves sections, cohomology and the canonical
   derived operations. Empty Spec, zero complexes, zero ranks and all integer degrees
   are included in this same finite induction. -/
theorem countable_affine_hypercohomology_tensor_perfect
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (affineCountableEtaleSpace A).SmallModules]
    (L : (affineCountableEtaleSpace A).DerivedModules)
    (hL : (affineCountableEtaleSpace A).derivedQCohProperty L)
    (hcount : ∀ j : ℤ, Countable
      (SheafOfModules.unit (affineCountableEtaleSpace A).smallStructureRings ⟶
        (DerivedCategory.homologyFunctor (affineCountableEtaleSpace A).SmallModules j).obj L))
    (Q : (affineCountableEtaleSpace A).DerivedModules)
    (hQ : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      (affineCountableEtaleSpace A).smallStructureSheaf Q) (n : ℤ) :
    Countable ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
      (affineCountableEtaleSpace A).smallEtaleModelTopology
      (affineCountableEtaleSpace A).smallStructureSheaf).obj
        (((affineCountableEtaleSpace A).derivedDualityModel.closed.tensor.obj (L, Q))⟦n⟧)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
