/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.SfEtaleExchanges
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.Paper.ProjectionCompactification
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Paper.GeometricStalkPerfect
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.Paper.ProjectionMateExact
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# The finite-coefficient compact-support projection formula on the small etale site

Source: Weil blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sf-pf-finite/_section.md`, order 1706 (blueprint: sk-thm-sf-pf-finite).

The projection is the published natural transformation of etale bifunctors for the
chosen compactification. Its two endpoints belong to the full bounded-below subcategory;
therefore invertibility of its component is invertibility in D+. Naturality in both
arguments is retained from this bifunctor transformation. Only L has finite Tor amplitude.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The finite-coefficient projection transformation is an isomorphism in D+,
natural in both bounded constructible inputs, with finite Tor amplitude only for L.
The compactification is the chosen factorization used to define the projection.
Constructibility is exactly the recorded set-sheaf predicate on each cohomology sheaf.
Source: Weil blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sf-pf-finite/_section.md`, order 1706 (blueprint: sk-thm-sf-pf-finite).

Proof, following the six steps of the DAG node:

1. Write the chosen compactification as j followed by p and put M = j!K.
The projection is the proper counit projection followed by Rp* of the inverse open
extension tensor comparison and the canonical pullback composition comparison.
The open comparison is the ordinary sectionwise tensor map after sheafification,
derived on K-flat representatives. Exact constant-coefficient pullback preserves
K-flat flat-term representatives; site-derived tensor descent makes this construction
independent of representatives. This identifies the actual canonical transformation.
2. Exact extension by zero has stalk K on the open and zero off it. Under the
stalk-tensor and monoidal pullback identifications the open comparison is the identity
inside and the unique map between zero objects outside. Exact geometric stalks and
their conservativity on each cohomology sheaf show that this comparison is invertible.
3. At a geometric point of Y the stalk P of L has a bounded finite-free model by the
small-etale clause of fix-lem-finite-tor-perfect. Sheaves on the spectrum of the
algebraically closed residue field are naturally constant with value their stalk;
this identifies geometric inverse image of L with that constant finite-free complex.
4. The finite ring A_(E,n) is torsion. Unbounded proper base change applies to p,
both for M and for M tensor p-inverse-image L. Projection/base-change compatibility
identifies the actual pulled-back proper projection map with the proper projection
on the geometric fibre. Open-extension base change identifies the fibre M with
extension by zero of the fibre K, giving the compact-support fibre interpretation.
5. On that fibre the two proper-projection functors are exact; their natural
transformation respects shifts and triangles and is the identity at the unit.
It is invertible on finite sums of unit shifts by naturality. Induct on the number
of nonzero terms of the finite-free model of P: the highest term is a finite sum
of unit shifts and the quotient has fewer terms. Their degreewise split exact
sequence gives a distinguished triangle, and two-out-of-three gives invertibility
on the whole model. Naturality transports it to the inverse image of L.
6. Every geometric stalk of the cone of the proper projection vanishes, so exact
and conservative stalks make that cone acyclic. Compose its inverse with the inverse
open comparison in reverse order to invert the specified compact-support projection.
Bounded K and the finite Tor interval of L put both endpoints in D+: tensor with a
bounded flat model preserves lower bounds, as do exact extension by zero and the
right-derived proper image. The full D+ subcategory contains this inverse.
Naturality in K and L is that of projectionMapOfCompactification; componentwise
inversion preserves its naturality squares. -/
theorem sf_finite_etale_projection_formula
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hKc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj K)))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (_hLc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj L)))
    (_hLb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj L))
    (_hLt : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    IsIso (((sfEtaleProjection (Padic.coefficientExtensionRing l E n) c).app K).app L) := by
  sorry

end AlgebraicGeometry.Etale
