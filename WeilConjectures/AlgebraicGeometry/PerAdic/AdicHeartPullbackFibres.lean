/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Localized.LocalizedTStructure
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.CategoryTheory.StageSystem.Morphism.PbcDescentFunctors
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackTriangles
import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.Pbc.PbcConstructibleReductionPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcConstructibleReductionCriterion
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion

import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
import WeilConjectures.AlgebraicGeometry.Lisse.LisseTensorScalarExtension
import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Constructible adic hearts, pullback, and geometric coefficient fibres

Source: Bhatt--Scholze, The pro-etale topology for schemes, Section 6.8,
Lemmas 6.8.2 and 6.8.7, Definitions 6.8.3, 6.8.6, 6.8.8 and 6.8.10,
Propositions 6.8.4, 6.8.11 and 6.8.14, and Remark 6.8.15
(blueprint: lem-per-adic-heart-pullback-fibres).

The finite-stage categories are the recorded raw localizations, and the algebraic
coefficient category is the recorded common-stage pair category. The fibres below
are normalized by completed geometric pullback, degree-zero cohomology, evaluation
at the final pro-etale object, and inversion of the uniformizer.

## Main definitions

* `rationalT`, `commonT`: the prescribed finite and common-stage standard t-structures.
* `rationalPull`, `commonPull`: the normalized actual completed pullback functors.
* `integralFiber`, `integralLimitFiber`, `fiber`: completed-section and adic-limit fibres.

## Main statement

* `adicHeartPullbackFibres`: all standard-heart, scalar, pullback and geometric-fibre clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v r s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.PerAdic

/-- A separated finite-type k-scheme; no geometric connectedness or nonemptiness is imposed.
Source: BS 6.8, geometric hypotheses (blueprint: lem-per-adic-heart-pullback-fibres). -/
structure Base (k : Type u) [Field k] where
  scheme : Scheme.{u}
  [over : scheme.Over (Spec (.of k))]
  [finiteTypeLocal : LocallyOfFiniteType (scheme ↘ Spec (.of k))]
  [finiteTypeCompact : QuasiCompact (scheme ↘ Spec (.of k))]
  [separated : IsSeparated (scheme ↘ Spec (.of k))]

attribute [instance] Base.over Base.finiteTypeLocal Base.finiteTypeCompact Base.separated

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [hl : Fact (IsUnit (l : k))]

set_option linter.unusedSectionVars false in
include hl in
/-- Finite type over a field gives exactly the hypotheses of the recorded adic categories.
Source: BS 6.8.11 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: finite type over the noetherian one-point scheme Spec k gives noetherianity.
The source library bounds the dimension of a quasi-compact finite-type k-scheme.
The unit l in k maps to a unit in every local ring of the scheme. -/
theorem base_properties (W : Base k) :
    IsNoetherian W.scheme ∧ (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) ∧
      (∀ x : W.scheme, IsUnit (l : W.scheme.presheaf.stalk x)) := by
  have hloc : IsLocallyNoetherian W.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.scheme ↘ Spec (.of k))
  have hcompact : CompactSpace W.scheme :=
    QuasiCompact.compactSpace_of_compactSpace (W.scheme ↘ Spec (.of k))
  refine ⟨⟨⟩, exists_topologicalKrullDim_le (W.scheme ↘ Spec (.of k)), ?_⟩
  intro x
  simpa only [map_natCast] using hl.out.map
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (W.scheme ↘ Spec (.of k)).appTop) ≫
      W.scheme.presheaf.germ ⊤ x trivial).hom

/-- The two geometric finiteness properties do not depend on the coefficient prime.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: finite type over the noetherian affine point gives noetherianity. Apply the
source library theorem exists_topologicalKrullDim_le directly to the structure morphism. -/
theorem base_geometric_properties (W : Base k) :
    IsNoetherian W.scheme ∧ (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) := by
  have hloc : IsLocallyNoetherian W.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.scheme ↘ Spec (.of k))
  have hcompact : CompactSpace W.scheme :=
    QuasiCompact.compactSpace_of_compactSpace (W.scheme ↘ Spec (.of k))
  exact ⟨⟨⟩, exists_topologicalKrullDim_le (W.scheme ↘ Spec (.of k))⟩

/-- The noetherian structure supplied by the finite-type hypothesis.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres). -/
instance baseNoetherian (W : Base k) : IsNoetherian W.scheme :=
  (base_geometric_properties W).1

/-- The finite dimension bound supplied by the finite-type hypothesis.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres). -/
instance baseDimension (W : Base k) : Fact (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) :=
  ⟨(base_geometric_properties W).2⟩

/-- Invertibility of the coefficient prime on every local ring.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres). -/
instance basePrimeUnit (W : Base k) : Fact (∀ x : W.scheme,
    IsUnit (l : W.scheme.presheaf.stalk x)) :=
  ⟨(base_properties l W).2.2⟩

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded localized standard t-structure; its classes are fixed by integral images.
Source: BS 6.8.11 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def rationalT (W : Base k) :
    Triangulated.TStructure
      (PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  @Classical.choose _ _ (pbc_localized_tstructure W.scheme l E
    (hNoeth := baseNoetherian W) (hDim := baseDimension W)
    (hInv := basePrimeUnit l W))

/-- The recorded finite-stage aisle, exposed as an object predicate independently
of competing stage shift instances. Source: BS 6.8.11
(blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev rationalLE (W : Base k) (n : ℤ) :
    ObjectProperty (PbcRationalCategory W.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)) := (rationalT l E W).le n

/-- The recorded finite-stage coaisle, exposed as an object predicate.
Source: BS 6.8.11 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev rationalGE (W : Base k) (n : ℤ) :
    ObjectProperty (PbcRationalCategory W.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)) := (rationalT l E W).ge n

include hl in
variable (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]

/-- The recorded coherent scalar system at a separated finite-type base.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev stages (W : Base k) :=
  pbcScalarSystem l Qbar W.scheme (baseDimension W).out (basePrimeUnit l W).out

/-- The existing inclusion of a finite coefficient field in the raw common-stage category.
Source: BS 6.8.14, common finite stages (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev inclusion (W : Base k) (L : Padic.FiniteCoefficientFields l Qbar) :=
  (stages l Qbar W).ι L

/-- Common-stage classes are precisely the isomorphism closures of finite-stage classes.
Source: BS 6.8.14, common finite stages (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def commonClass (W : Base k) (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (pbcQbarCategory l Qbar W.scheme) :=
  fun K ↦ ∃ (L : Padic.FiniteCoefficientFields l Qbar)
    (M : pbcStageCategory l Qbar W.scheme L),
    (if nonpositive then rationalLE l (pbcFiniteField.{u} l Qbar L) W n M
      else rationalGE l (pbcFiniteField.{u} l Qbar L) W n M) ∧
      Nonempty (K ≅ (inclusion l Qbar W L).obj M)

/-- The common-stage t-structure is fixed by its two finite-stage image classes.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: finite scalar extension is t-exact by its finite free integral description.
Descend both truncations with their scalar comparisons. Orthogonality is checked
at a common field; all later Hom groups are zero, hence so is their colimit. The
finite-stage truncation triangle supplies the decomposition axiom. Finite-stage
bounds give boundedness. The prescribed indexed classes determine the t-structure. -/
theorem commonT_existsUnique (W : Base k) :
    ∃! t : Triangulated.TStructure (pbcQbarCategory l Qbar W.scheme),
      (∀ n : ℤ, t.le n = commonClass l Qbar W true n ∧
        t.ge n = commonClass l Qbar W false n) ∧ t.bounded = ⊤ := by
  sorry

/-- The bounded common-stage t-structure, determined by its specified classes.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def commonT (W : Base k) :
    Triangulated.TStructure (pbcQbarCategory l Qbar W.scheme) :=
  (commonT_existsUnique l Qbar W).exists.choose

end AlgebraicGeometry.Scheme.PerAdic
