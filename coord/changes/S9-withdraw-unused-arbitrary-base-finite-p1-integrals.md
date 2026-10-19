# Sheaf.AlgebraicGeometry.ArbitraryBaseFiniteP1Integrals

## Reason

Withdraw the unused item under dispatched worker brief step 8d. A whole-library source
search finds no importer of this module and no reference to its seven declarations
outside itself. Thus it is outside the import closure of TargetsCheck and Challenge.
The former consumer Sheaf.Paper.NoetherianPrimePowerSmoothDuality already imports
ProjectiveLineDiagonalIntegrals directly and requires only Noetherian bases. That
consumer adaptation was delivered by J1 when the previous ArbitraryBaseP1Integrals
attachment was withdrawn. ND subsequently restated the arbitrary-base interface with
new names, but no current Lean module uses it.

The arbitrary-base mathematical statement and its complete seven-step proof plan are
preserved in lem-sp-tower-p1-arbitrary-base-integrals. Its lean field becomes null.
The unattached mathematical parent det-sp-tower-p1-adjunction still cites this result;
its statement and proof route are unchanged. Neither node realizes a unit statement
or step. No target signature or definition used by a target changes.

## Old

The complete withdrawn module, including all seven signatures and definition bodies:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite projective-line splitting and diagonal integrals over arbitrary bases

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-p1.proof.md, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals).

The family below ranges over every scheme on which N is invertible. Restricting it
along schemes over any fixed such base gives the family in the source statement.
No Noetherian, finite-type, or nonempty-base assumption occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Transport the trace of a specified splitting over P along the canonical chart of
one projection P ×_S P → P. This uses the adjunction unit, canonical derived composition,
and normalized twist pullback, with no finiteness assumption on the base. Its last
arrow is exactly the inverse splitting followed by the second projection.
Source: blueprint main-20261015, tower P1 proof, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
@[irreducible]
def arbitraryBaseFiniteP1DiagonalTrace (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool)
    (b : ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧ ⊞
        ordinaryFiniteUnit A (ProjectiveLine S)) ≅
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)) :
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
      (ordinaryFiniteShiftedLinePullback A N hA t
        e.hom (by
          simpa only [map_natCast] using hS.map
            ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom)).hom ≫
    b.inv ≫ biprod.snd

/-- Chern arrows on all bases with N invertible. This is just the function type of
arrows used in the splitting specification below.
Source: blueprint main-20261015, tower P1 proof, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
abbrev ArbitraryBaseFiniteP1ChernFamily (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) :=
  ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧

/-- Splitting isomorphisms on all bases with N invertible. Their two components
are constrained separately by ArbitraryBaseFiniteP1SplittingSpec.
Source: blueprint main-20261015, tower P1 proof, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
abbrev ArbitraryBaseFiniteP1SplittingFamily (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) :=
  ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The exact Kummer specification and ordered two-component equation for b.
This predicate contains no additional hypothesis or conclusion.
Source: blueprint main-20261015, tower P1 proof, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
@[irreducible]
def ArbitraryBaseFiniteP1SplittingSpec (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (c : ArbitraryBaseFiniteP1ChernFamily A N hA)
    (b : ArbitraryBaseFiniteP1SplittingFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
    ordinaryFiniteP1ChernSpec A N hA S
        (by
          simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom) (c S hS) ∧
      (b S hS).hom = biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
        (ordinaryFiniteP1ChernPushforward A N hA S (c S hS))

/-- The two canonical base-change equations, respectively for the specified
splitting and for its inverse followed by the second projection.
Source: blueprint main-20261015, tower P1 proof, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
@[irreducible]
def ArbitraryBaseFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (b : ArbitraryBaseFiniteP1SplittingFamily A N hA) : Prop :=
  ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
      (hS' : IsUnit (N : Γ(S', ⊤))),
    ((ordinaryFinitePullback A f).map (b S hS).hom ≫
      ordinaryFiniteP1Exchange A f
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          (by
            simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
    ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫ (b S' hS').hom) ∧
    ((ordinaryFinitePullback A f).map ((b S hS).inv ≫ biprod.snd) ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          (by
            simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom ≫
      (b S' hS').inv ≫ biprod.snd)

/-- The effective Cartier diagonal, its specified relative Kummer class, and
its two integrals, using precisely the traces of the splitting family b.
Source: blueprint main-20261015, tower P1 proof, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
@[irreducible]
def ArbitraryBaseFiniteP1DiagonalIntegrals (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (b : ArbitraryBaseFiniteP1SplittingFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
    ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
      ∃ κ : Ext
        ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
        SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
          (by
            simpa only [map_natCast] using hS.map
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
            arbitraryBaseFiniteP1DiagonalTrace A N hA t S hS a
              (b (ProjectiveLine S)
                (by
                  simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom)) =
          𝟙 (ordinaryFiniteUnit A (ProjectiveLine S))

/-- The canonical finite-coefficient splitting, its trace base-change equation, and
both supported diagonal integrals over every base on which N is invertible.
The Chern arrows are characterized by the actual scalar Kummer boundary of O(1).
Each decomposition is an isomorphism with precisely the specified two components;
its trace is its inverse followed by biprod.snd. The supported class is fixed by
SupportedKummerBoundary, including the positive Cartier/Chern sign convention.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-p1.proof.md, Levelwise check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals).

Proof plan from the DAG:

1. Put $U=\operatorname{Spec}\mathbf Z[1/N]$, $Q=\mathbf P^1_U$ and $r_U:Q\to U$. Every scheme on
   which $N$ is invertible has its canonical map to $U$: on affine opens the map sends $a/N^k$ to
   $a(N^{-1})^k$, and these maps agree on overlaps. The ring $\mathbf Z[1/N]$ is Noetherian: for
   an ideal $J$, choose a generator $d$ of $J\cap\mathbf Z$; since $a/N^k\in J$ implies $a\in
   J\cap\mathbf Z$, one has $J=(d)$. Any ascending chain stabilizes because its union has one
   generator, already in some member. Thus [lem-asd-ordinary-finite-p1-adjunction] applies to $U$,
   $N$ and the given finite ring $A$. Its displayed $b_{r_U}$ has exactly the two components
   specified here, so $b_U$ is an isomorphism and $t_U=\operatorname{pr}_2 b_U^{-1}$.

2. Over an affine open $\operatorname{Spec}R$ of any base $T$, [lem-weil-pbc-projective-space-
   standard-charts] gives the two charts $\operatorname{Spec}R[t]$, $\operatorname{Spec}R[s]$,
   with $s=t^{-1}$ on the overlap. By [lem-weil-pbc-fibre-product-affine-spectra], their product
   charts have polynomial coordinate rings in two variables. The equation $x_0y_1-x_1y_0=0$
   restricts to a difference of the two coordinates on equal charts and to $1-tu$ up to a unit on
   mixed charts. Its zero subscheme is the diagonal: on equal charts it identifies the
   coordinates; on mixed charts the relation $tu=1$ identifies the two overlap coordinates. A
   monic difference is a non-zero-divisor by its leading coefficient. If $(1-tu)\sum a_k(u)t^k=0$,
   comparison of the constant coefficient and then successive coefficients gives
   $a_0=a_1=\cdots=0$. Thus the diagonal is effective Cartier by [def-nagata-effective-cartier-
   ideal]. The hyperplane $H=(x_1=0)$ has equation $t$ on the $x_0$ chart and is empty on the
   $x_1$ chart. Its ideal dual [def-pc-divisor-line-bundle] has bases with transition
   $e_0=t^{-1}e_1$, precisely $\mathcal O(1)$ in the chart statement. All these equations and
   transitions remain the same over every new base ring, so diagonal and hyperplane pullbacks are
   still effective Cartier and $\mathcal O(H)$ pulls back to $\mathcal O(1)$.

3. For $v:T'\to T$ over $U$, let $v_P:P_{T'}\to P_T$ be the induced map. The morphism $r_T$ is
   proper by [lemma-nagata-projective-space-base-change-proper]. Since $NA=0$, [lem-kun-proper-
   base-change-torsion-ring] gives the canonical exchange isomorphism
   $B_v:v^{-1}Rr_{T,*}A_{P_T}(1)[2]\xrightarrow{\sim}Rr_{T',*}A_{P_{T'}}(1)[2]$. Use [lem-asd-
   etale-finite-twist-pullback] to identify coefficients and let $\sigma_v:v^{-1}(A_T(1)[2]\oplus
   A_T)\xrightarrow{\sim}A_{T'}(1)[2]\oplus A_{T'}$. Then $$B_v\,v^{-1}b_T=b_{T'}\sigma_v.$$ For
   the first component this is the unit identity for the exchange mate [def-kun-unbounded-
   exchange], obtained by inserting its unit-counit formula and cancelling the adjacent counit-
   unit pair. For the second component, express $c_1(\mathcal O(1))$ as $c_{H,A}u_H$. By Step 2
   the pulled-back hyperplane is effective Cartier with line bundle $\mathcal O(1)$, so [lem-asd-
   ordinary-supported-kummer] identifies the pulled-back supported morphism with $c_{H',A}$. The
   divisor unit satisfies the same mate identity, so the composite pulls back to $c_{H',A}u_{H'}$.
   Taking adjoints gives precisely $h_{T'}$. The two component equations prove the displayed
   equality without assuming that $b_T$ is already invertible.

4. Apply Step 3 to the canonical $a:T\to U$. The equality $b_T=B_a\,a^{-1}b_U\,\sigma_a^{-1}$
   shows that $b_T$ is an isomorphism, since all three factors are isomorphisms by Steps 1 and 3.
   Define $t_T=\operatorname{pr}_2 b_T^{-1}$. Invert the equality of Step 3 and use
   $\operatorname{pr}_2\sigma_v=v^{-1}\operatorname{pr}_2$ to get $$t_{T'}B_v=v^{-1}t_T.$$ This
   proves both the arbitrary-base splitting and the asserted trace compatibility for every $v$.

5. Apply [lem-amb-p1-diagonal-integrals] with Noetherian base $U$, the same $N$ and the same
   finite ring $A$. For $W_U=Q\times_UQ$ it gives
   $$t_{p_{i,U}}R(p_{i,U})_*(\delta_{A,U})\alpha_{i,U}=1_{A_Q}\quad(i=1,2).$$ The trace used there
   is defined in [def-amb-p1-trace] as $\operatorname{pr}_2 b^{-1}$ for the splitting with
   components the twisted unit and the Kummer hyperplane class. Hence its trace is exactly the
   $t_Q$ already constructed in Step 4 for either projection $p_{i,U}$. The supported class has
   the same sign normalization $c_{\Delta,A}u_\Delta=c_1(\mathcal O(\Delta))$, and $\alpha_{i,U}$
   is the canonical composition identification, as required. No trace or integral theorem has been
   applied to a non-Noetherian base in this step.

6. For a scheme $T\to U$, write $w:P_T\to Q$ and $z:W_T\to W_U$ for the base-change maps, and fix
   $i$. Let $B_E:w^{-1}R(p_{i,U})_*E\xrightarrow{\sim}R(p_{i,T})_*z^{-1}E$ be proper exchange,
   available by [lemma-nagata-projective-space-base-change-proper] and [lem-kun-proper-base-
   change-torsion-ring]. Step 2 makes the pulled-back diagonal effective Cartier, so [lem-asd-
   ordinary-supported-kummer] identifies $z^{-1}\delta_{A,U}$ with $\delta_{A,T}$ under the
   closed-immersion exchange $D:z^{-1}R\Delta_{U,*}A_Q\xrightarrow{\sim}R\Delta_{T,*}A_{P_T}$. Put
   $C=R(p_{i,T})_*D\circ B_{R\Delta_{U,*}A_Q}$. Naturality of $B$ gives
   $$B_{A_{W_U}(1)[2]}\,w^{-1}(R(p_{i,U})_*\delta_{A,U})=R(p_{i,T})_*\delta_{A,T}\,C.$$ Also
   $C\,w^{-1}\alpha_{i,U}=\alpha_{i,T}$. To check this last equality, use [lem-weil-pbc-ringed-
   topoi-derived-pushforward-composition] to identify the two successive direct images with the
   direct image of $p_i\Delta=1$. Clause (2) of [lem-weil-pbc-mate-pasting] identifies the
   composite exchange $C$ with the exchange for that composite, and clause (4) identifies the
   exchange for the identity with the identity. Thus the equation is a formal consequence of the
   canonical mate formulas, rather than an extra base-change assertion attributed to the
   composition node.

7. Combining the two equations of Step 6 with the trace equation of Step 4 gives
   $$t_{P_T}R(p_{i,T})_*\delta_{A,T}\,\alpha_{i,T}=w^{-1}\bigl(t_Q
   R(p_{i,U})_*\delta_{A,U}\,\alpha_{i,U}\bigr)=w^{-1}1_{A_Q}=1_{A_{P_T}}.$$ The middle equality
   is Step 5, and inverse image preserves identities. This applies separately to $i=1,2$; take
   $T=S$ to obtain both integrals in the statement. All changes of base in Steps 3, 4 and 6 were
   arbitrary.
-/
theorem exists_arbitraryBaseFiniteP1Integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (c : ArbitraryBaseFiniteP1ChernFamily A N hA)
      (b : ArbitraryBaseFiniteP1SplittingFamily A N hA),
      ArbitraryBaseFiniteP1SplittingSpec A N hA t c b ∧
      ArbitraryBaseFiniteP1BaseChange A N hA t b ∧
      ArbitraryBaseFiniteP1DiagonalIntegrals A N hA t b := by
  sorry

end AlgebraicGeometry.Etale
```

## New

The delivery tool writes an empty module in place of the withdrawn file:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

No replacement declaration is introduced. The DAG node's Lean attachment is null;
its mathematical statement, proof, proof dependencies and unit record remain intact.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| none | none | No direct or transitive Lean importer and no external declaration use. |

downstream.py reports 0 downstream modules and no external use of the theorem.
Source searches cover lean/WeilConjectures, lean/Sheaf, TargetsCheck and Challenge.
The NoetherianPrimePowerSmoothDuality module is not an importer of this item and
needs no adaptation. No other module is delivered or changed.

## Status

landed 20261019T231346-L-577687 2026-10-19 (merge of deliver/S9/Sheaf.AlgebraicGeometry.ArbitraryBaseFiniteP1Integrals)
