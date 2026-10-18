/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessComparison
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

/-!
# Base change of a trace transpose

Source: blueprint main-20261015, sk-thm-smooth-purity,
lem-pur-projection-purity-agreement, expanded trace comparison;
Stacks Project, Tag 0037 (blueprint: lem-pur-trace-transpose-base-change).

We use the canonical comparison coordinates of def-pur-co-smoothness. An arbitrary
bounded constructible pro-etale object L is retained, together with an etale
representative K and an isomorphism e : nu^* K ≅ L. The traces are written in these
coordinates. Full faithfulness of comparison on bounded-below objects identifies
all traces, not just selected ones, with these representatives. The transported
Hom bijection is exactly the normalization of thm-sf-ambient-adjoint-class.
The pullback-origin isomorphism transports the conclusion back to a^* L.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The canonical derived pullback comparison, with the etale side written as Lg^*.
Source: blueprint trace comparison and Tag 099R
(blueprint: lem-pur-trace-transpose-base-change). -/
noncomputable def purityTracePullbackComparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U X : Scheme.{u}} (g : U ⟶ X) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory ⋙
        sfFixedDerivedPullback P.Ring g ≅
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory :=
  sfDerivedComparisonPullbackIso P.Ring g ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) g).symm
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory

/-- The actual exceptional transpose in comparison coordinates, transported to L.
Source: blueprint trace comparison; thm-sf-ambient-adjoint-class, normalization of
its Hom bijection (blueprint: lem-pur-trace-transpose-base-change). -/
noncomputable def purityTraceTranspose
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K ≅ L)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K ⟶ 𝟙_ _) :
    L ⟶ comparedDualizing P f :=
  e.inv ≫ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
    ((Etale.rightDerivedUpperShriekAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).homEquiv K (𝟙_ _) t)

/-- The induced etale-origin witness of a^* L, using the canonical pullback comparison.
Source: blueprint trace comparison, pullback of the retained representative
(blueprint: lem-pur-trace-transpose-base-change). -/
noncomputable def purityTracePullbackOrigin
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U X : Scheme.{u}} (a : U ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K ≅ L) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.obj
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj K) ≅
      (sfFixedDerivedPullback P.Ring a).obj L :=
  (purityTracePullbackComparison P a).symm.app K ≪≫
    (sfFixedDerivedPullback P.Ring a).mapIso e

/-- B is the canonical counit mate of inverse compact-support exchange, with the unit
comparison included. This is the map used in def-pur-co-smoothness, with its source
identified by the canonical comparison square.
Source: blueprint trace comparison and def-pur-co-smoothness, clause 3
(blueprint: lem-pur-trace-transpose-base-change). -/
noncomputable def purityTraceDualizingBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {b : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f b) :
    (sfFixedDerivedPullback P.Ring a).obj (comparedDualizing P f) ⟶
      comparedDualizing P f' :=
  (purityTracePullbackComparison P a).hom.app
      (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
      (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)

/-- A unit-valued trace satisfying compact-support base change has transpose
P' = B composed with a^* P, on the original pro-etale input.
Source: blueprint main-20261015, lem-pur-projection-purity-agreement, expanded trace
comparison; Stacks Project, Tag 0037
(blueprint: lem-pur-trace-transpose-base-change).

Proof:
1. Work in the etale representatives, using the normalized Hom bijections of
thm-sf-ambient-adjoint-class. The inverse transpose is F(h) followed by the counit
(lem-weil-pbc-adjunct-counit-identity). Thus F(P) followed by epsilon is t; for B
it is inverse exchange followed by b^* epsilon and the canonical unit comparison.
2. The compact-support exchange is a natural transformation, by its unit, square,
counit and extension-by-zero formula (def-cbc-exchange-map). Its finite-level
transport is the exchange of thm-cbc-finite-level-proetale. Naturality at P and
invertibility of its components give F'(a^* P) followed by C_omega inverse
= C_L inverse followed by b^* F(P), in diagrammatic composition order.
3. Inverse-transpose B composed with a^* P. Substitute the counit formula for B,
then exchange naturality, then F(P) followed by epsilon = t. The result is
C_L inverse followed by b^* t and the unit comparison. The trace hypothesis
identifies this with t'.
4. Injectivity of the f' Hom bijection identifies this composite with P'. Apply
comparison pullback and naturality of purityTracePullbackComparison; conjugating
by e and its induced pullback witness gives the displayed equation on a^* L.
No step inverts B or uses smoothness, a Tate twist, or an ambient pro-etale adjunction. -/
theorem purityTraceTranspose_baseChange
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [a.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback a f' f b) :
    letI := (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
    letI := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    letI : QuasiCompact f' :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    ∀ (L : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (_hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) X L)
      (K : _root_.DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (e : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K ≅ L)
      (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K ⟶ 𝟙_ _)
      (t' : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f').obj
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj K) ⟶ 𝟙_ _),
      (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq).app K ≫ t' =
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map t ≫
          (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b).hom →
      purityTraceTranspose P f'
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj K)
          ((sfFixedDerivedPullback P.Ring a).obj L) (purityTracePullbackOrigin P a K L e) t' =
        (sfFixedDerivedPullback P.Ring a).map (purityTraceTranspose P f K L e t) ≫
          purityTraceDualizingBaseChange P sq := by
  sorry

end AlgebraicGeometry.ProEtale
