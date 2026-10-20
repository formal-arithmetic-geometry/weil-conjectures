/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Finite projective-line splitting and diagonal integrals over arbitrary bases

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-p1.proof.md, levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals).

The splitting contains exactly its two normalized components. Its trace is the second
projection of its inverse. No Noetherian hypothesis or adjunction datum is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The Kummer-normalized two-summand splitting at an arbitrary base. The Chern
specification is the actual scalar-extended Kummer class of the existing O(1).
Source: blueprint tower P1 adjunction, finite levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
structure ArbitraryBaseFiniteP1Splitting (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) where
  chern : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  chern_spec : ordinaryFiniteP1ChernSpec A N hA S
    (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) chern
  decomposition :
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
  decomposition_hom : decomposition.hom = biprod.desc
    (ordinaryFiniteP1Unit A N hA t S hS) (ordinaryFiniteP1ChernPushforward A N hA S chern)

/-- The trace is the second projection of the inverse of the normalized splitting.
Source: blueprint tower P1 adjunction, finite trace normalization
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def ArbitraryBaseFiniteP1Splitting.trace {A : Type (u + 1)} [CommRing A] {N : ℕ}
    {hA : (N : A) = 0} {t : OrdinaryFiniteTwistTransport A N hA}
    {S : Scheme.{u}} {hS : IsUnit (N : Γ(S, ⊤))}
    (d : ArbitraryBaseFiniteP1Splitting A N hA t S hS) :
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ⟶
        ordinaryFiniteUnit A S :=
  d.decomposition.inv ≫ biprod.snd

/-- The two arbitrary-base exchange squares, for the splitting and its trace.
All comparisons are the canonical arrows of the recorded dependency nodes.
Source: blueprint tower P1 adjunction, finite levelwise check and base-change normalization
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def ArbitraryBaseFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS) : Prop :=
  ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))),
    ((ordinaryFinitePullback A f).map (d S hS).decomposition.hom ≫
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
    ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫
      (d S' hS').decomposition.hom) ∧
    ((ordinaryFinitePullback A f).map (d S hS).trace ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom ≫
          (d S' hS').trace)

/-- Transport the specified trace on P1 over P along the canonical chart for either
projection of P times P. This uses the chart adjunction unit and derived composition,
followed by the normalized twist comparison and the given splitting's own trace.
Source: blueprint tower P1 adjunction, identification of the two projections with r_P
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def arbitraryBaseFiniteP1DiagonalTrace (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A r).map
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom (by
        simpa using hS.map
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom ≫
    (d (ProjectiveLine S)
      (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)).trace

/-- The finite Kummer splitting and both diagonal integrals over every N-invertible base.
The supported boundary fixes the sign through its canonical relative Kummer construction.
The maps alpha are the existing canonical composition identifications, explicitly isomorphisms.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-p1.proof.md, levelwise finite diagonal check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals).

Proof plan:
1. Set U = Spec Z[1/N]. Every N-invertible scheme has its canonical map to U, by
localizing on affine opens and gluing. An ideal of Z[1/N] is generated by the generator
of its contraction to Z, so U is Noetherian. Apply lem-asd-ordinary-finite-p1-adjunction
to U, obtaining precisely the splitting with twisted-unit and Kummer components.
2. The projective-space standard charts and affine fibre-product calculation give
diagonal equations x-y and 1-xy. Coefficient comparison makes both nonzerodivisors
over any ring. They cut out the diagonal, hence its ideal is effective Cartier.
The hyperplane's ideal dual has the O(1) transitions. All equations survive base change.
3. Properness of projective space and lem-kun-proper-base-change-torsion-ring give
proper exchange for arbitrary base maps. The mate formula respects the twisted unit.
Express the hyperplane Chern class as its supported Kummer map after the divisor unit;
lem-asd-ordinary-supported-kummer and the Cartier calculation identify its pullback.
Taking adjuncts therefore gives the Kummer component on the new base. The two
component equations are exactly the decomposition square, before assuming invertibility.
4. Pull back the splitting from U. Exchange and twist comparisons are isomorphisms,
so it is an isomorphism over every base. Invert the square and project to its second
summand to obtain the displayed trace square, for every morphism of bases.
5. Apply lem-amb-p1-diagonal-integrals on U. Its trace is pr2 of this same inverse
splitting by def-amb-p1-trace; its supported class has the same Kummer sign.
6. Pull the diagonal square to any base. Supported Kummer pullback and naturality
of proper exchange identify the pushed supported classes. Derived direct-image
composition identifies alpha with the unit for p_i Delta = id. Clauses 2 and 4 of
lem-weil-pbc-mate-pasting identify its composite exchange with the identity exchange,
so the alpha comparisons also commute, without an extra base-change assumption.
7. Combine the class, alpha and trace squares to pull back each of the two identities
from U. Inverse image preserves identity maps. This proves both Boolean-indexed
integrals with no Noetherian or finite-type assumption on S. -/
theorem exists_arbitraryBaseFiniteP1Integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ArbitraryBaseFiniteP1Splitting A N hA t S hS),
      ArbitraryBaseFiniteP1BaseChange A N hA t d ∧
      ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
          ∃ κ : Ext
            ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
              (ordinaryFiniteConstant A (ProjectiveLine S)))
            (Scheme.finiteEtaleTateLine
              (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
            SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
              (by
                simpa using hS.map
                  ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                    (ProjectiveLine S ↘ S)).appTop.hom) κ ∧
            ∀ a : Bool,
              IsIso (projectiveLineDiagonalAlpha A S a) ∧
              projectiveLineDiagonalAlpha A S a ≫
                (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
                  (supportedExactDerivedMap
                    (lowerStar (ModuleCat.{u + 1} A)
                      (pullback.diagonal (ProjectiveLine S ↘ S)))
                    (ordinaryFiniteConstant A (ProjectiveLine S))
                    (Scheme.finiteEtaleTateLine
                      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ) ≫
                arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a =
              𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)) := by
  sorry

end AlgebraicGeometry.Etale
