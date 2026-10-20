/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.CategoryTheory.CompactSupportRoosCofinality
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.IntegralScalarExtensionWellDefined

/-!
# The specified quotient-cone pullback comparison

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), and Lemma 6.8.2(1);
the explicit quotient-cone model for the scalar comparison is agent-formulated
(blueprint: lem-weil-specified-pullback-comparison-alpha).

The level maps, their strict tower, both coordinates of the Roos map, and the
zero-shifted-coordinate completion map are the existing normalized constructions.
The theorem asserts their quasi-isomorphism and identifies the completed comparison
with their localization, including all representative comparison isomorphisms.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory

namespace WeilConjectures

/-- The concrete quotient-cone model for the canonical completed pullback comparison.
Here `scalarPullbackLevel`, `scalarPullbackTower`, and `scalarPullbackChain` are
respectively the specified maps d_m, their strict tower map, and delta_P.
`integralScalarCompletionChain` is chi_Y(P), with zero shifted coordinate and
quotient projections in its other coordinate. The isomorphism e identifies an
arbitrary good representative P with K; it is not an extra restriction on K.

Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1, Lemmas 6.5.9(4)
and 6.8.2(1); the explicit scalar-extension model is agent-formulated
(blueprint: lem-weil-specified-pullback-comparison-alpha).

Proof:
1. The finite-free completed scalar comparison makes S_W finite free over R_W.
   Choose a flat-term K-flat resolution P of K. Derived change of rings and
   K-flat change of rings show that Q = P tensor S_Y is good and represents C_Y K.
2. The same-index maps rho_m = iota_m pi_m give precisely the finite quotient
   complexes and their reductions in the scalar-extension construction. Tensor
   associativity identifies Q tensor B_L,m with P tensor B_L,m.
3. Integral-operations well-definedness identifies the two pullback Roos complexes
   A_E(P) and A_L(Q) with the corresponding derived pullbacks.
4. On local tensor generators d_m sends ((g^-1(p tensor a)) tensor b) tensor s
   to g^-1(p tensor iota_m(a)) tensor (iota_m(b) pi_L,m(s)). Balancing,
   differentials, and consecutive reductions commute, giving the strict tower map.
5. Finite freeness commutes with countable products and the shifted cone. The
   resulting delta_P applies the product of d_m to both Roos coordinates.
6. The completion map sends q to (0, (q mod varpi_L^m)_m). The finite-free
   comparison makes this chain map a quasi-isomorphism because K is complete.
7. If e is the ramification index, completed-constant-sheaf reduction identifies
   D_E,m(P) tensor S_X with D_L,em(Q). The same-index d_m is its composite
   with the transition em to m, so it need not be injective. Roos cofinality gives
   a quasi-isomorphism r_e in the other direction. With Y_n = D_L,n(Q), put
   h(y)_n = sum_{i=n}^{en-1} T_{n,i} y_i. Telescoping gives h(1-s) = 1-phi
   and (1-s)h = 1-psi for the selection and block coordinates of delta_P r_e.
   Thus delta_P r_e is homotopic to the identity, proving delta_P a quasi-isomorphism.
   Isomorphism pullback preserves integral constructibility, hence completeness.
   Conjugate the localized delta_P by chi_X inverse and Lg_L applied to chi_Y.
   Inserting the canonical representative comparisons gives the displayed equation.
8. All level maps, products, cones and completion maps are functorial. The
   well-definedness theorem identifies them under replacement of P, so the formula
   is resolution independent. Their naturality gives the last square for every
   derived morphism. This is the specified comparison of the integral scalar
   operations construction, rather than an arbitrary isomorphism of its endpoints.
-/
theorem specifiedPullbackComparisonAlpha
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    ∃ hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E g).obj K),
      (∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ K),
        integralOperationsGoodComplex l L Y
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj) ∧
        QuasiIso ((integralScalarCompletionChain l E L ι Y).app P.obj) ∧
        QuasiIso (scalarPullbackChain l E L ι g P.obj) ∧
        ((scalarCompletionIso l E L ι Y K hK.1).hom ≫
            (integralScalarExtension l E L ι Y).map e.inv ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryDerivedScalar l E L ι Y).map e.inv ≫
            (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj)) ∧
        (scalarPullbackCompleted l E L ι g K hK.1 hF).hom =
          (scalarCompletionIso l E L ι X _ hF).inv ≫
            (integralOrdinaryDerivedScalar l E L ι X).map
              ((integralDerivedPullback l E g).map e.inv) ≫
            (integralOrdinaryDerivedScalar l E L ι X).map
              ((integralDerivedPullbackComparison l E g).hom.app P) ≫
            (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
              ((integralOperationsPullbackComplexFunctor l E g).obj P.obj) ≫
            DerivedCategory.Q.map (scalarPullbackChain l E L ι g P.obj) ≫
            (integralDerivedPullbackComparison l L g).inv.app
              ⟨_, scalarGood l E L ι Y P⟩ ≫
            (integralDerivedPullback l L g).map
              ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.inv.app P.obj) ≫
            (integralDerivedPullback l L g).map
              ((integralOrdinaryDerivedScalar l E L ι Y).map e.hom) ≫
            (integralDerivedPullback l L g).map
              (scalarCompletionIso l E L ι Y K hK.1).hom) ∧
      ∀ (K' : DerivedCategory (integralTowerModules l E Y))
        (hK' : sfIntegralConstructible l E Y K')
        (hF' : IsSfDerivedComplete l E X ((integralDerivedPullback l E g).obj K'))
        (a : K ⟶ K'),
        (integralScalarExtension l E L ι X).map ((integralDerivedPullback l E g).map a) ≫
            (scalarPullbackCompleted l E L ι g K' hK'.1 hF').hom =
          (scalarPullbackCompleted l E L ι g K hK.1 hF).hom ≫
            (integralDerivedPullback l L g).map ((integralScalarExtension l E L ι Y).map a) := by
  sorry

end WeilConjectures
