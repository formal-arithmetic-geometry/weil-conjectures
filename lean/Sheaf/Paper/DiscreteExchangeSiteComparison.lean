/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageComparisonCoherence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageMateCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves

/-!
# Discrete-coefficient exchange under the etale/pro-etale comparison

Source: blueprint main-20261015, sk-thm-properbasechange, pro-etale site paragraph;
Stacks Project, Tag 07A7 (blueprint: lem-weil-pbc-discrete-exchange-site-comparison).

The existing natural isomorphisms `baseChangeSourceComparisonIso` and
`baseChangeTargetComparisonIso` are the displayed composites S and T. Their definitions
include the canonical compatibility of bounded-below functors with the full derived
categories. The equality is written after that fully faithful inclusion; the last four
clauses say that both ambient endpoints belong to D+ and have classical cohomology.
The coefficient category is modules over the discrete ring, with its canonical constant
ring identifications. No continuous-function or completed coefficient ring is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparisons identify the two specified exchange mates, and both
pro-etale endpoints are bounded below and classical, for any discrete commutative ring.

Source: blueprint main-20261015, sk-thm-properbasechange.proof.md, pro-etale site paragraph;
Stacks Project, Tag 07A7 (blueprint: lem-weil-pbc-discrete-exchange-site-comparison).

Proof (the seven steps of the node):
1. Apply sk-thm-pe-direct-image-comparison to all four inverse images and to the qcqs
   vertical direct images. By lem-pe-direct-image-mate-compatibility and the bijection
   def-weil-pbc-adjunction-mate, its beta is precisely the counit-normalized b. The
   existing source and target comparison isomorphisms are the prescribed S and T.
2. Apply lem-pe-inverse-image-comparison-coherence to the two paths around the square.
   Cancel the common composite comparison: theta_p followed by p_f'(a_g) and a_f'
   equals p_g'(a_f) followed by a_g' and A_X'(theta_e). Exact termwise descent and
   lem-weil-pbc-localization-universal-property preserve this specified equation.
3. The counit identity of lem-pe-direct-image-mate-compatibility says that
   p_u(b_u) followed by epsilon_p equals c_u followed by A_U(epsilon_e), c_u = a_u.inv.
4. Transpose A_Y'(e) followed by T under p_f' adjoint to s_f'. Naturality and Step 3
   for f' reduce it to c_f', then A_X'(theta_e), then A_X'(l_g'(epsilon_e)), then a_g'.
5. Transpose S followed by the ambient exchange of def-weil-pbc-ambient-ringed-exchange.
   Its definition is the unit--square--counit mate. Naturality of theta_p, Step 3 for f,
   Step 2, and naturality of a_g' reduce this transpose to exactly the same four factors.
6. Injectivity of the adjunction correspondence gives the displayed exchange equality.
   Whiskering the canonical natural comparisons gives naturality of S and T.
7. Exact comparison commutes with cohomology and preserves lower bounds by
   lem-weil-pbc-exact-functor-bounded-below. The module essential image of
   sk-thm-pe-classical-sheaves makes every cohomology sheaf classical. Apply this to
   l_g r_f L and r_f' l_g' L, and transport across S and T. Their invertibility, rather
   than invertibility of either exchange, gives the two endpoint assertions. -/
theorem discrete_exchange_site_comparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : ChosenCartesianSquare g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)) ≫
      (baseChangeTargetComparisonIso g' f' Λ).hom.app L =
        (baseChangeSourceComparisonIso f g Λ).hom.app L ≫
          (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj L)) ∧
    (∃ n : ℤ, DerivedCategory.IsGE
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) n) ∧
    IsClassicalComplexFor Y' Λ
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) ∧
    (∃ n : ℤ, DerivedCategory.IsGE
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) n) ∧
    IsClassicalComplexFor Y' Λ
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) := by
  sorry

end AlgebraicGeometry.ProEtale
