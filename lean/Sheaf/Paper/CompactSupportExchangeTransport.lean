/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.Paper.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.FixSiteOpenExchange
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Transport of the chosen compact-support exchange

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-composition.proof.md, final base-change sentence, expanded by
sk-prop-sf-cbc/thm-cbc-finite-level-proetale.proof.md, lines 4--22
(blueprint: lem-pur-co-smooth-exchange-transport).

The comparisons use the normalized proper counit mate and exact open extension.
All inputs are bounded below; the pro-etale operations are ordinary ambient derived
operations. The two comparison paths are natural isomorphisms, and witness transport
retains its actual etale representative and comparison isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The normalized proper/open comparison, with bounded-below etale source and ambient
pro-etale target. This only inserts the canonical bounded-below inclusions into the
existing compact-support site comparison; its proper factor is the counit mate.
Source: blueprint finite-level compact-support transport proof, lines 4--19
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} Λ) c) _ ≪≫
    Functor.associator _ _ _ ≪≫
    (compactSupportSiteComparison Λ c).symm

/-- The source path `S = v^* C_c ∘ a_v` as a natural isomorphism.
Source: blueprint finite-level compact-support transport proof, lines 4--20
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportSource (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus) ⋙
          DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory ≅
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) ⋙
            (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarComparisonIso g Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compactExchangeTransportComparison Λ c) _

/-- The target path `T = F_{u'}^p(a_w) ∘ C_{c'}` as a natural isomorphism.
Source: blueprint finite-level compact-support transport proof, lines 15--20
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportTarget (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f) :
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)) ⋙ DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory ≅
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor) ⋙
            rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
              (c.ofIsPullback sq) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (compactExchangeTransportComparison Λ (c.ofIsPullback sq)) ≪≫
    (Functor.associator
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq))).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComparisonIso g' Λ) _

/-- Transport the specified etale exchange through a retained etale-origin witness
`(L, alpha)` in the fixed-scalar module-sheaf presentation. Both endpoint paths are
canonical, so this definition contains no arbitrary exchange or comparison choice.
Source: blueprint finite-level compact-support transport proof, lines 21--22
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportAtWitness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (alpha : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj ≅ N) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor).obj N ⟶
      ((upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)).obj N :=
  ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) ⋙
      (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor).map alpha.inv ≫
    (compactExchangeTransportSource Λ g c).inv.app L ≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app L)) ≫
    (compactExchangeTransportTarget Λ sq c).hom.app L ≫
    ((upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)).map alpha.hom

/-- The normalized compact-support comparison identifies the specified etale and
ambient pro-etale exchanges, naturally in every bounded-below input. Transport through
any retained witness equals the ambient exchange at its target; hence it is unchanged
under isomorphisms of witnesses (indeed it is independent of the witness).
Source: blueprint main-20261015, lem-pur-co-smooth-composition.proof.md, final sentence;
thm-cbc-finite-level-proetale.proof.md, lines 4--22
(blueprint: lem-pur-co-smooth-exchange-transport).

Proof plan, following the node's four steps:
1. Put M = j_! L. Exact open extension preserves bounded-below objects. The proper
parts of c and its base change are qcqs. Apply lem-weil-pbc-transport-identifies-exchange
at M, using the normalized mate of lem-weil-pbc-comparison-direct-image-canonical-mate.
This gives the proper exchange square, without assuming its invertibility or any
separatedness of g.
2. The degreewise site/open comparisons are those of
lem-cbc-proetale-extension-zero-comparison. Apply lem-fix-site-open-exchange to the upper
open square, with rho = a^{-1}, and multiply by the two pullback comparisons. This says
beta^p A(L) composed with the pulled-back site/open comparison and a_bar equals
j'_!(a_w) composed with the base-changed site/open comparison and A(beta^e).
3. Expand both compact-support exchanges as the proper exchange followed by the image
of beta. Naturality of the pro-etale proper exchange moves the open comparison across
it. Substitute the proper square from step 1 and the open square from step 2. Naturality
of the base-changed proper mate then gives T A(E^e) = E^p S. All factors are natural;
thus the equation is an equality of natural transformations.
4. Conjugate the equation by S^{-1} and by the source and target images of alpha.
Naturality of E^p in alpha cancels these images, leaving precisely E^p(N). This right
side contains no witness, proving the stated invariance, including isomorphic witnesses.
The identity base change, identity open/proper factors, empty schemes and zero ring
are included. No completion is used. -/
theorem compactSupport_exchange_transport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (Functor.whiskerRight
        (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c)
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory) ≫
      (compactExchangeTransportTarget Λ sq c).hom =
    (compactExchangeTransportSource Λ g c).hom ≫
      Functor.whiskerLeft
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory)
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c)) ∧
    (∀ (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (alpha : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj ≅ N),
      compactExchangeTransportAtWitness Λ sq c L N alpha =
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c).app N) := by
  sorry

end AlgebraicGeometry.ProEtale
