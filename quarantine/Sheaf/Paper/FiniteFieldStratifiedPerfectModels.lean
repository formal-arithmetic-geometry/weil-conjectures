/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.AlgebraicGeometry.EtaleSiteBoundedConstantModels
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Stratified perfect constant models over a finite field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.6.11,
forward implication (residue stratification), and Proposition 6.8.11(3);
Stacks Project, Tags 095E, 03RZ and 094G
(blueprint: lem-weil-pbc-finite-field-stratified-perfect-models).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- A bounded constructible etale complex over a finite field has, on an etale cover
of each constructible locally closed stratum, an actual bounded finite-dimensional
constant complex model. The same complex models its pro-etale comparison pullback,
in the continuous-function coefficient-ring presentation.

Source: Bhatt--Scholze, Proposition 6.6.11, forward implication, and 6.8.11(3);
Stacks Project, Tags 095E, 03RZ and 094G
(blueprint: lem-weil-pbc-finite-field-stratified-perfect-models).

Proof:
1. Choose cohomological bounds a <= b. Constructibility gives a finite stratification
for each of the finitely many cohomology degrees in this interval. Repeatedly use
lem-weil-pbc-constructible-stratification-intersection to obtain a common refinement,
using actual fibre products of stratum schemes and constructible intersections.
The first stratification starts the induction; empty fibre products may be retained.
2. Exact inverse image (prop-weil-pbc-inverse-image-modules-exact) identifies homology
on a refined stratum with the inverse image of the original homology. Pull back each
trivializing etale cover along the refinement projection. The natural constant-module
comparison (lem-sfb-geometric-inverse-image-constant-module) preserves its finite values.
This works on every etale object of the stratum, and outside the bounds use zero.
3. Apply lem-weil-pbc-etale-site-bounded-constant-models, Stacks 094G, on each stratum.
It gives an etale cover and actual complexes of finite k-modules, zero outside [a,b],
whose constant differentials give the required derived models. A finite k-module is
finite-dimensional because its finite set of elements spans it.
4. Every k-vector space is projective (lem-weil-pbc-vector-space-projective). Thus
these bounded finite-dimensional complexes themselves witness IsPerfectRingComplex
(def-pc-perfect-ring-complex), including the zero complex and zero terms.
5. Put h = v followed by the stratum immersion. The canonical comparison-pullback
isomorphisms (lem-weil-pbc-comparison-pullback) commute inverse image with nu^*.
Exactness (lem-pe-constant-left-module-inverse-image) descends them termwise to derived
categories. The constant-preserving coefficient identification of
prop-weil-pbc-proetale-constant-ring-map is precisely the realization used by
finiteCoefficientDerivedComparison and finiteCoefficientDerivedPullback.
6. Apply nu^* to the etale model. Naturality in every module differential of
lem-sfb-geometric-inverse-image-constant-module gives the same constant complex on
the pro-etale site, not merely isomorphic graded objects. Realize it over the recorded
coefficient ring sheaf. Etale covers are pro-etale covers (lem-pur-etale-proetale-cover).
There is no integral lifting or completeness hypothesis; empty strata need no model. -/
theorem finite_field_stratified_perfect_models
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (k : Type (u + 1)) [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)))
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) q).obj L))
    (hconstructible : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) q).obj L)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i : Fin S.n, ∃ 𝒰 : Cover.{u} etalePrecoverage (S.domain i),
        ∀ j : 𝒰.I₀, ∃ (P : CochainComplex (ModuleCat.{u + 1} k) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ q : ℤ, Module.Finite k (P.X q)) ∧
          @DerivedCategory.IsPerfectRingComplex k _ (HasDerivedCategory.standard _)
            ((@DerivedCategory.Q (ModuleCat.{u + 1} k) _ _
              (HasDerivedCategory.standard _)).obj P) ∧
          Nonempty
            ((Etale.upperStar (ModuleCat.{u + 1} k)
                (𝒰.f j ≫ S.immersion i)).mapDerivedCategory.obj L ≅
              DerivedCategory.Q.obj
                (((constantSheaf (𝒰.X j).smallEtaleTopology
                  (ModuleCat.{u + 1} k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ∧
          Nonempty
            ((finiteCoefficientDerivedPullback X k (𝒰.f j ≫ S.immersion i)).obj
                ((finiteCoefficientDerivedComparison X k).obj L) ≅
              (finiteCoefficientRealization (𝒰.X j) k).mapDerivedCategory.obj
                (DerivedCategory.Q.obj
                  (((constantSheaf (Scheme.ProEt.topology (𝒰.X j))
                    (ModuleCat.{u + 1} k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) := by
  sorry

end AlgebraicGeometry.ProEtale
