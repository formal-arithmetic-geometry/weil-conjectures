/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionScalarPresentation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed

/-! # The open-closed triangle for every admissible coefficient ring

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.md and its proof
(blueprint: prop-sf-open-closed-triangle-all-stages).

All operations act on the ordinary uncompleted derived category of internal modules
on the small pro-etale site. The first two arrows are the actual adjunction counit
and unit. The connecting transformation is restricted to the bounded constructible
full subcategory; its naturality expresses functoriality in every ambient morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The specified composite j_! j^*, using exact termwise localization.
Source: latest blueprint, displayed open-closed triangle
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
abbrev sfOpenClosedOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (upperStar Λ j).mapDerivedCategory ⋙ (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The specified composite Ri_* i^*, with the exact termwise inverse image.
Source: latest blueprint, displayed open-closed triangle
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
abbrev sfOpenClosedClosed {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (upperStar Λ i).mapDerivedCategory ⋙ (lowerStar Λ i).rightDerivedFunctor

/-- The existing recollement triangle constructor with the specified open counit
and closed unit; only the connecting map is a parameter.
Source: latest blueprint, The triangle paragraph; def-weil-open-closed-recollement
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
abbrev sfOpenClosedTriangle {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (δ : (sfOpenClosedClosed Λ i).obj K ⟶ ((sfOpenClosedOpen Λ j).obj K) ⟦(1 : ℤ)⟧) :=
  Recollement.triangle
    ((upperStarLowerStarAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j) K δ

/-- The natural distinguished open-closed triangle, its constructible vertices,
shifted orthogonality and uniqueness, at precisely the four coefficient stages.
The finite ring A is a discrete representative of the specified quotient A_{E,n};
the four alternatives identify Λ as a condensed ring, not merely as an abelian sheaf.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages, The triangle,
Hom vanishing and Constructibility (blueprint: prop-sf-open-closed-triangle-all-stages).

Proof: (1) Finite type over the global algebraic closure makes X Noetherian, hence
j quasi-compact; pulled-back coefficients restrict to the prescribed coefficients.
(2) Apply the ringed short exact localization sequence termwise. Exact localization
and the short-exact-complex triangle identify the first arrows with the counit and unit.
(3) Derived open adjunction and j^*i_*=0 give shifted orthogonality, for different
objects as well. Triangle-morphism extension gives uniqueness and naturality.
(4) Pullback preserves constructible cohomology. Integral extension by zero uses
integral-models (3); field coefficients use Dbc=Dctf and existence (2).
(5) At finite coefficients, take an etale constructible origin, apply constructible
extension by zero, and transport through the pullback and extension-zero comparisons.
(6) Bounded constructible objects form a triangulated subcategory, so the third
vertex is bounded constructible as well. These are exactly the node's steps 1--6. -/
theorem sf_openClosed_triangle_all_stages
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] (_eA : A ≃+* Padic.coefficientExtensionRing ell E n)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {Z U : Scheme.{u}} (i : Z ⟶ X.left) (j : U ⟶ X.left)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ) :
    ∃ δ : (constantModelBoundedConstructible Λ X.left).ι ⋙ sfOpenClosedClosed Λ i ⟶
        (constantModelBoundedConstructible Λ X.left).ι ⋙ sfOpenClosedOpen Λ j ⋙
          shiftFunctor _ (1 : ℤ),
      ∀ K : ConstantModelBoundedConstructible Λ X.left,
        sfOpenClosedTriangle Λ i j K.obj (δ.app K) ∈ distTriang _ ∧
        constantModelBoundedConstructible Λ X.left ((sfOpenClosedOpen Λ j).obj K.obj) ∧
        constantModelBoundedConstructible Λ X.left ((sfOpenClosedClosed Λ i).obj K.obj) ∧
        (∀ m : ℤ, Subsingleton
          (((sfOpenClosedOpen Λ j).obj K.obj) ⟦m⟧ ⟶ (sfOpenClosedClosed Λ i).obj K.obj)) ∧
        (∀ δ' : (sfOpenClosedClosed Λ i).obj K.obj ⟶
            ((sfOpenClosedOpen Λ j).obj K.obj) ⟦(1 : ℤ)⟧,
          sfOpenClosedTriangle Λ i j K.obj δ' ∈ distTriang _ → δ' = δ.app K) := by
  sorry

/-- For finite-field models and field coefficients the Frobenius isomorphism
extends to the localization triangle, with its prescribed middle component.
The outer components are the induced Weil structures: the two triangle squares
force the adjunction-compatible open and closed exchange maps. The third square
is exactly equivariance of the connecting arrow, including the shift comparison.
Native Weil complexes are covered by their recorded realization as strict pairs.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages, Weil structures
(blueprint: prop-sf-open-closed-triangle-all-stages).

Proof (node step 7): the geometric Frobenius squares of the model immersions are
cartesian. The ringed exchange maps, inverted using the inverse squares, give the
outer Weil isomorphisms and the unit/counit squares. Exact Frobenius inverse image
preserves the distinguished triangle. Cross-object shifted orthogonality and
triangle-morphism extension identify the transported third map with the original
one, giving the third square. Thus all three arrows are Weil-equivariant. -/
theorem sf_openClosed_triangle_weil
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (c : WeilCoefficient ell)
    (X₀ Z₀ U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (i₀ : Z₀ ⟶ X₀) (j₀ : U₀ ⟶ X₀)
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    (j : (D.geometricFiber U₀).left ⟶ (D.geometricFiber X₀).left)
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (_hj : j = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ)
    (K : strictWeilComplexCategory D ell hell X₀ c)
    (δ : (sfOpenClosedClosed (WeilCoefficient.ab c) i).obj K.obj.carrier ⟶
      ((sfOpenClosedOpen (WeilCoefficient.ab c) j).obj K.obj.carrier) ⟦(1 : ℤ)⟧)
    (_hδ : sfOpenClosedTriangle (WeilCoefficient.ab c) i j K.obj.carrier δ ∈ distTriang _) :
    ∃ e : ((upperStar (WeilCoefficient.ab c)
          (D.geometricFrobenius X₀).hom).mapDerivedCategory).mapTriangle.obj
        (sfOpenClosedTriangle (WeilCoefficient.ab c) i j K.obj.carrier δ) ≅
          sfOpenClosedTriangle (WeilCoefficient.ab c) i j K.obj.carrier δ,
      e.hom.hom₂ = K.obj.str.hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
