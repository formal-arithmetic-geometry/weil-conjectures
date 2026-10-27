/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.ExchangeFunctoriality

/-! # Comparing the complete-subcategory mate with the strict datum exchange

Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (4), completed coefficient transport;
Stacks Tags 099N and 0D6D.
(blueprint: lem-sf-sbc-datum-exchange-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The specified mate on complete objects is the datum's ordered strict-tower
exchange under the canonical comparisons of the two operation presentations.
Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (4), completed coefficient transport;
Stacks Tags 099N and 0D6D.
(blueprint: lem-sf-sbc-datum-exchange-comparison).

Proof: compare the ordinary module pullbacks through their completed coefficient
isomorphisms. Their tensor formulas agree, and universal left-derived counits
therefore give the ordinary pullback comparison. Its adjoint mate identifies the
ordinary direct images. The strict tower pullback comparison is obtained from the
same module formula at every quotient, with the quotient transitions retained;
apply the derived inverse limit. These give the source and target comparisons
in the statement, evaluating the pullback comparison at the direct image for the
source, and mapping the pullback comparison by direct image for the target.

To check the exchange equation, precompose with the ordinary-to-completed unit.
The complete-subcategory adjunction and its normalized square compositor reduce
the left side to ordinary exchange followed by direct image of the target unit.
The datum's ordered strict-tower exchange satisfies the same unit equation.
The ordinary pullback comparisons respect composition by their resolving counits,
so the mate calculation identifies the two ordinary exchanges. The target is
complete, and the injective part of the completion reflector's Hom bijection
cancels the source unit. This proves the equation without inverting any exchange.
The argument applies to empty schemes and zero objects and uses neither properness,
smoothness, finite dimension nor constructible landing. -/
theorem sbcDatumExchangeComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) (K : PbcComplete l E X) :
    ∃ (source : ((sbcPull l E g).obj ((sbcPush l E f).obj K)).obj ≅
        ((pbcIntegralDatum l E).completedPull g).obj
          (((pbcIntegralDatum l E).push f).obj K.obj))
      (target : ((sbcPush l E f').obj ((sbcPull l E g').obj K)).obj ≅
        ((pbcIntegralDatum l E).push f').obj
          (((pbcIntegralDatum l E).completedPull g').obj K.obj)),
      (sbcExchangeApp l E (exchangeTransposeSquare sq) K).hom ≫ target.hom =
        source.hom ≫ (pbcIntegralDatum l E).completedExchange sq K.obj := by sorry

end WeilConjectures
