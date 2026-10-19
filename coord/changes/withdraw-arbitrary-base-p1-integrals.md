# AlgebraicGeometry.Etale.arbitraryBaseP1_integrals and its unused interface

## Reason

Withdraw the item module under brief step 8d. Its only direct importer is
Sheaf.Paper.NoetherianPrimePowerSmoothDuality (unclaimed). That module needs diagonal
integrals only over Noetherian schemes, already stated by projectiveLine_diagonal_integrals.
The existing det-sp-p1-adjunction route and the projective-line normalization stay.
No target signature uses the four deleted interface declarations or the theorem.
No theorem is claimed proved by this withdrawal. The arbitrary-base DAG statement remains
unchanged, without a Lean attachment; future tower work can realize it when required.

## Old

The complete withdrawn module, including the definitions and signature verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # Projective-line splitting and diagonal integrals over arbitrary bases

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-p1.proof.md, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals).

The ordered splitting has the twisted shifted unit first and the adjoint Kummer
hyperplane class second. Both diagonal projections use the canonical projective-line
charts, and the trace is always the inverse splitting followed by the second projection.

## Main definitions and statement

* `arbitraryBaseP1DiagonalTrace`: transport of the specified inverse-splitting trace.
* `ArbitraryBaseP1DiagonalIntegrals`: the normalized supported class and both integrals.
* `ArbitraryBaseP1Splitting`: the hyperplane class and specified two-component splitting.
* `ArbitraryBaseP1BaseChange`: its two canonical arbitrary-base pullback equations.
* `arbitraryBaseP1_integrals`: existence of this data over all N-invertible bases.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Transport the inverse-splitting trace along either canonical projective-line chart.
The comparisons are the chart adjunction unit, derived direct-image composition,
the chart's equation over P, and the normalized shifted twist comparison.
Source: blueprint main-20261015, sk-prop-sp-tower-geometric-p1.proof.md, finite diagonal
integrals (blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
@[irreducible]
def arbitraryBaseP1DiagonalTrace (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (b : ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧ ⊞
      ordinaryFiniteUnit A (ProjectiveLine S)) ≅
      (ordinaryFinitePushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧))
    (a : Bool) :
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  let L : DerivedCategoryModule A
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) :=
    (ordinaryFiniteLine A N hA
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  let e := (projectiveLineDiagonalChart S a).val.hom
  let M : DerivedCategoryModule A (ProjectiveLine (ProjectiveLine S)) :=
    (ordinaryFinitePullback A e).obj L
  (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e
      (projectiveLineDiagonalProjection S a)).hom.app M ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app M ≫
    (ordinaryFinitePushforward A
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
      (ordinaryFiniteShiftedLinePullback A N hA t (projectiveLineDiagonalChart S a).val.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom ≫
    b.inv ≫ biprod.snd

/-- The supported diagonal clause, using one and the same Kummer-boundary class
in its Chern normalization and both projection integrals. This packages the final
paragraph of the node without choosing a trace or a supported class.
Source: blueprint main-20261015, sk-prop-sp-tower-geometric-p1.proof.md, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
@[irreducible]
def ArbitraryBaseP1DiagonalIntegrals (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (b : ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧ ⊞
      ordinaryFiniteUnit A (ProjectiveLine S)) ≅
      (ordinaryFinitePushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)) : Prop :=
  let P : Scheme.{u} := ProjectiveLine S
  let q : P ⟶ S := ProjectiveLine S ↘ S
  let W : Scheme.{u} := pullback q q
  let d : P ⟶ W := pullback.diagonal q
  let w : W ⟶ S := pullback.fst q q ≫ q
  let hW : IsUnit (N : Γ(W, ⊤)) :=
    (map_natCast w.appTop.hom N) ▸ hS.map w.appTop.hom
  ∃ hI : d.ker.IsInvertible,
    ∃ κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) d).obj (ordinaryFiniteConstant A P))
      (Scheme.finiteEtaleTateLine W N A hA) 2,
      SupportedKummerBoundary A N hA d hI hW κ ∧
      let δ : (ordinaryFinitePushforward A d).obj (ordinaryFiniteUnit A P) ⟶
          (ordinaryFiniteLine A N hA W)⟦(2 : ℤ)⟧ :=
        supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) d)
          (ordinaryFiniteConstant A P) (Scheme.finiteEtaleTateLine W N A hA) κ
      ∃ c₁ : ordinaryFiniteUnit A W ⟶ (ordinaryFiniteLine A N hA W)⟦(2 : ℤ)⟧,
        ordinaryFiniteClass A W (Scheme.finiteEtaleTateLine W N A hA) 2 c₁ =
          supportedKummerChern A N hA d hI hW ∧
        (supportedDerivedUnit A d ≫ δ = c₁) ∧
        ∀ a : Bool,
          projectiveLineDiagonalAlpha A S a ≫
            (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
              δ ≫
            arbitraryBaseP1DiagonalTrace A N hA t S hS b a =
          𝟙 (ordinaryFiniteUnit A P)

/-- The specified two-component splitting at one arbitrary N-invertible base.
Only the Kummer hyperplane class, its exact realization, and the decomposition are
packaged here; no adjunction or Noetherian hypothesis is part of this datum.
Source: blueprint main-20261015, sk-prop-sp-tower-geometric-p1.proof.md, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
structure ArbitraryBaseP1Splitting (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) where
  chern : ordinaryFiniteUnit A (ProjectiveLine T) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧
  chern_spec : ordinaryFiniteP1ChernSpec A N hA T
    ((map_natCast (ProjectiveLine T ↘ T).appTop.hom N) ▸
      hT.map (ProjectiveLine T ↘ T).appTop.hom) chern
  decomposition :
    ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A T) ≅
      (ordinaryFinitePushforward A (ProjectiveLine T ↘ T)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧)
  decomposition_hom : decomposition.hom =
    biprod.desc (ordinaryFiniteP1Unit A N hA t T hT)
      (ordinaryFiniteP1ChernPushforward A N hA T chern)

/-- The two canonical arbitrary-base pullback equations for the splitting and its
inverse followed by the second projection. The exchange and coefficient maps are
exactly those of the recorded dependencies, without a new choice of comparison.
Source: blueprint main-20261015, sk-prop-sp-tower-geometric-p1.proof.md, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
@[irreducible]
def ArbitraryBaseP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseP1Splitting A N hA t T hT) : Prop :=
  ∀ {T' T : Scheme.{u}} (v : T' ⟶ T)
  (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))),
  ((ordinaryFinitePullback A v).map (d T hT).decomposition.hom ≫
    ordinaryFiniteP1Exchange A v
      ((ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward A (ProjectiveLine T' ↘ T')).map
      (ordinaryFiniteShiftedLinePullback A N hA t
        (ProjectiveSpace.map (ULift.{u} (Fin 2)) v)
        ((map_natCast (ProjectiveLine T ↘ T).appTop.hom N) ▸
          hT.map (ProjectiveLine T ↘ T).appTop.hom)).hom =
    ordinaryFiniteP1DecompositionSourceMap A N hA t v hT ≫ (d T' hT').decomposition.hom) ∧
  ((ordinaryFinitePullback A v).map ((d T hT).decomposition.inv ≫ biprod.snd) ≫
    (ordinaryFiniteUnitPullback A v).hom =
    ordinaryFiniteP1Exchange A v
      ((ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward A (ProjectiveLine T' ↘ T')).map
      (ordinaryFiniteShiftedLinePullback A N hA t
        (ProjectiveSpace.map (ULift.{u} (Fin 2)) v)
        ((map_natCast (ProjectiveLine T ↘ T).appTop.hom N) ▸
          hT.map (ProjectiveLine T ↘ T).appTop.hom)).hom ≫
    (d T' hT').decomposition.inv ≫ biprod.snd)

/-- The finite Kummer-normalized splitting, its arbitrary-base pullback equations,
and both supported diagonal integrals. All bases are arbitrary schemes. A scheme
T over a given S is obtained by specializing the universally quantified base T;
invertibility pulls back along T → S. No Noetherian or field hypothesis is imposed.
Source: blueprint main-20261015, sk-prop-sp-tower-geometric-p1.proof.md, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals).

Proof plan:
1. Use U = Spec Z[1/N]. Every N-invertible scheme maps canonically to U. Localization
of the principal ideal ring Z is Noetherian: an ideal is generated by the generator
of its contraction. Apply lem-asd-ordinary-finite-p1-adjunction to U and A.
2. Use lem-weil-pbc-projective-space-standard-charts and
lem-weil-pbc-fibre-product-affine-spectra. The diagonal equations are coordinate
differences and 1-tu. The former are monic; for the latter successive coefficient
comparison proves regularity over every ring. They define the diagonal, so its ideal
is effective Cartier. The hyperplane ideal's dual has exactly the O(1) transitions.
These equations and transitions remain unchanged under arbitrary base change.
3. Properness of projective space and lem-kun-proper-base-change-torsion-ring give
proper exchange. Expand its mate formula: the twisted unit component commutes by the
triangle identity. Write the hyperplane Chern class as supported Kummer after its
unit. Apply lem-asd-ordinary-supported-kummer and the Cartier calculation to see that
this component also commutes. The two component equations give the splitting square.
4. Pull the invertible splitting on U to any T. Its square shows b_T is invertible.
Invert the same square and compose with the second projection to get trace pullback.
5. Apply lem-amb-p1-diagonal-integrals over U. By def-amb-p1-trace its trace is exactly
the second projection of the inverse of the same two-component splitting. Its
supported class has the same Kummer sign and its alpha is the composition comparison.
6. Pull the diagonal and its supported Kummer class to any base. Naturality of proper
exchange gives the square for Rp_* delta. The direct-image composition comparison
and clauses (2) and (4) of lem-weil-pbc-mate-pasting identify the pulled-back alpha
with alpha: the composite p_i Delta is the identity, whose exchange is the identity.
7. Combine these squares with trace pullback. Each new integral is the inverse image
of the integral over U, hence of the identity. Apply this to both Boolean projections.
The argument includes N=1, the zero coefficient ring, and the empty scheme.
-/
theorem arbitraryBaseP1_integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
        ArbitraryBaseP1Splitting A N hA t T hT),
      ArbitraryBaseP1BaseChange A N hA t d ∧
      ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ArbitraryBaseP1DiagonalIntegrals A N hA t S hS
          (d (ProjectiveLine S)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)).decomposition := by
  sorry

end AlgebraicGeometry.Etale
```

## New

The withdrawn module will contain no declarations (deliver3.py writes the empty module).
No replacement theorem or definition is introduced. The sole direct consumer replaces
its proof-only ArbitraryBaseP1Integrals import with ProjectiveLineDiagonalIntegrals;
its Step 2 now cites the Noetherian diagonal-integral result. All its public imports,
signatures and theorem proof are identical. The separate recursion change record
`coord/changes/noetherian-line-append-recursion.md` documents the equivalent
`lineAppend` definition rewrite needed to compile this parent within 60 seconds.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Adapted proof import and Step 2 citation only; compiled |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | Transitive importer; no reference to withdrawn declarations |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Transitive importer; no reference to withdrawn declarations |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | Transitive importer; no reference to withdrawn declarations |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Transitive importer; no reference to withdrawn declarations |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | Transitive importer; no reference to withdrawn declarations |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | Transitive importer; no reference to withdrawn declarations |

A full Lean-source search finds no uses of any withdrawn declaration outside the item.
The import is private, so the withdrawal cannot alter any transitive consumer's visible API.
The remaining DAG citers lem-per-ordinary-smooth-orientation and det-sp-tower-p1-adjunction
have no Lean attachment. The former is likewise Noetherian; the latter really needs
arbitrary bases and its statement and plan remain untouched. No unit realization changes.

## Status

landed 20261019T154013-L-3026593 2026-10-19 (merge of deliver/J1/Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals)
