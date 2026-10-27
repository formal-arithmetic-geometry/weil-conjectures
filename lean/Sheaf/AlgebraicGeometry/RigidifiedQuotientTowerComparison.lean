/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.FunctorialFanDesingularization
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSStrictLogMorphism
public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.GabberModificationData

import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.CompletionRegularLocal

/-! # Strict inert comparison of rigidified quotient resolution towers

Source: ILO VIII Proposition 5.4.2, Corollary 5.4.4 and 5.4.5, pp.126--127;
normalized-tower interpretation 5.3.10--5.3.11
(blueprint: lem-per-rigidified-quotient-tower-comparison).

The enlarged boundary is only normal crossings, in the etale-local SNC sense
of Stacks 0BI9. Strictness of its log morphism is an explicit input.
All comparison maps are normalized by their quotient square and blowup squares;
centers are actual ideals, and a proper principal center is never contracted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace RigidifiedQuotient

/-- Package a lifted fan tower without changing any level, arrow or center.
Source: ILO VIII 3.3.13 (blueprint: lem-per-rigidified-quotient-tower-comparison). -/
def liftedTower {n : ℕ} {T : FineFan.Tower.{u} n} (L : LogFanTower T)
    (X : FineSaturatedLogScheme.{u}) (h : L.level 0 = X) : LogBlowupTowerOver X where
  tower :=
    { length := n
      level := L.level
      arrow := L.arrow
      center := fun i ↦ (L.chart i.castSucc).pullbackIdeal (T.center i)
      isBlowup := L.blowup }
  initial := h

/-- The fixed rule is induced by ONE fan resolution: on every global fan chart
its tower is the contraction of the lift of that fan resolution. The already
recorded strict-etale procedure includes descent and all its comparison laws.
Source: ILO VIII 3.3.13--3.3.15 and 5.3.8
(blueprint: lem-per-rigidified-quotient-tower-comparison). -/
def IsFanInduced (R : FineFan.SmoothFunctorialDesingularization.{u})
    (P : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u}) : Prop :=
  ∀ (X : FineSaturatedLogScheme.{u}) (hX : IsLogBlowupInput X)
    (F : FineFan.ResolutionInput.{u})
    (c : LogFanChart X ((R.resolution F).tower.level 0)),
    ∃ (L : LogFanTower (R.resolution F).tower) (h : L.level 0 = X),
      HEq (L.chart 0) c ∧
        Nonempty (LogBlowupComparison (EtaleLogHom.id X)
          (liftedTower L X h) (P.tower X hX))

/-- A rigidified pair, allowing disconnected schemes and non-strict NC enlarged
boundaries. The structural-compatible divisorial isomorphism excludes an unrelated
fs log structure with the same boundary support. No excellence assumption occurs.
Source: ILO VIII 4.1, 5.3.3--5.3.4 and 5.4.3; Stacks 0BI9
(blueprint: lem-per-rigidified-quotient-tower-comparison). -/
structure Pair (G : Type v) [Group G] [Finite G] where
  logScheme : FineSaturatedLogScheme.{u}
  noetherian : IsNoetherian logScheme.scheme
  regular : IsRegularScheme logScheme.scheme
  separated : logScheme.scheme.IsSeparated
  action : FSLogGroupAction G logScheme
  tame : action.IsTame
  genericallyFree : action.IsGenericallyFree
  admissible : ∀ x : logScheme.scheme, ∃ U : logScheme.scheme.Opens,
    x ∈ U ∧ IsAffineOpen U ∧
      ∀ (g : G) (z : logScheme.scheme), (action.baseAction g).hom z ∈ U ↔ z ∈ U
  abelianInertia : GabberModification.AbelianInertia action
  boundary : logScheme.scheme.IdealSheafData
  snc : IsStrictNormalCrossingsBoundary boundary
  groupStrict : GabberModification.GStrict action.baseAction boundary
  freeOutside : GabberModification.FreeOpen action boundary.support.compl
  boundaryInvariant : ∀ g : G, boundary.comap (action.baseAction g).hom = boundary
  enlargedBoundary : logScheme.scheme.IdealSheafData
  contains : boundary.support ≤ enlargedBoundary.support
  normalCrossings : ∀ x : logScheme.scheme,
    ∃ (W : Scheme.{u}) (e : W ⟶ logScheme.scheme), Etale e ∧
      ∃ w : W, e w = x ∧ IsStrictNormalCrossingsBoundary (enlargedBoundary.comap e)
  enlargedInvariant : ∀ g : G,
    enlargedBoundary.comap (action.baseAction g).hom = enlargedBoundary
  divisorial : ∃ e : logScheme.logStructure.monoidSheaf.obj ≅
      divisorialLogPresheaf (Scheme.Opens.ι (X := logScheme.scheme)
        enlargedBoundary.support.compl),
    e.hom ≫ divisorialStructuralMap (Scheme.Opens.ι (X := logScheme.scheme)
        enlargedBoundary.support.compl) =
      logScheme.logStructure.alpha
  veryTame : action.IsVeryTame

/-- The strict inert equivariant maps in the statement. Both inverse images are
reduced. Inertness includes equivariance and bijectivity on geometric stabilizers.
Strictness is imposed on the enlarged divisorial log pairs, independently of the
boundary-support equalities. Source: ILO VIII 5.3.6 and 5.4.2--5.4.4
(blueprint: lem-per-rigidified-quotient-tower-comparison). -/
structure Hom {H G : Type v} [Group H] [Finite H] [Group G] [Finite G]
    (Y : Pair.{u, v} H) (X : Pair.{u, v} G) where
  groupMap : H →* G
  logMap : EtaleLogHom Y.logScheme X.logScheme
  inert : GabberModification.Inert Y.action X.action groupMap logMap
  boundary : Y.boundary = (X.boundary.comap logMap.base).radical
  enlargedBoundary : Y.enlargedBoundary = (X.enlargedBoundary.comap logMap.base).radical
  strict : logMap.IsStrict

/-- A presentation of the prescribed rigidified construction: the invariant log
quotient, its resolution by the fixed rule, and the FULL recursive fs pullback.
The bijective count says that pulling to the finite quotient cover deletes no stage.
Ring centers are algebraizations of these log centers, characterized in geometric
strict local rings; the underlying steps are normalized blowups of those ideals.
Source: ILO VIII 5.3.8--5.3.11
(blueprint: lem-per-rigidified-quotient-tower-comparison). -/
structure Construction (P : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u})
    {G : Type v} [Group G] [Finite G] (X : Pair.{u, v} G) where
  quotient : FineSaturatedLogScheme.{u}
  quotientMap : EtaleLogHom X.logScheme quotient
  invariantQuotient : X.action.IsQuotient quotientMap
  input : IsLogBlowupInput quotient
  tower : LogBlowupTowerOver X.logScheme
  pullback : LogBlowupComparison quotientMap (P.tower quotient input) tower
  fullPullback : Function.Bijective pullback.count
  center : ∀ i : Fin tower.tower.length, (tower.tower.level i.castSucc).scheme.IdealSheafData
  normalized : ∀ i, Monoscheme.IsNormalizedBlowup (tower.tower.arrow i).base (center i)
  algebraized : ∀ (i : Fin tower.tower.length)
    (V : (tower.tower.level i.castSucc).scheme.affineOpens)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ (tower.tower.level i.castSucc).scheme)
    (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.1.ι)),
    ((center i).ideal V).map
        ((strictLocalGerm _ t (Scheme.Etale.mk V.1.ι) w).hom.comp V.1.topIso.inv.hom) =
      Ideal.span ((tower.tower.level i.castSucc).logStructure.toEtalePrelogStructure.stalkAlpha t ''
        (tower.tower.level i.castSucc).logStructure.idealStalk (tower.tower.center i) t)

/-- The quotient comparison and the contracted SCHEME pullback of its pulled-back
normalized towers. Every square is also an fs pullback and preserves the log centers.
`unitCenter` deletes precisely unit ring ideals; `strictTransform` says that the
canonical strict-transform inclusion in the ordinary fibre product is an isomorphism.
Source: ILO VIII Proposition 5.4.2 and Corollary 5.4.4
(blueprint: lem-per-rigidified-quotient-tower-comparison). -/
structure Comparison {P : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u}}
    {H G : Type v} [Group H] [Finite H] [Group G] [Finite G]
    {Y : Pair.{u, v} H} {X : Pair.{u, v} G} (f : Hom Y X)
    (A : Construction P X) (B : Construction P Y) where
  quotientMap : EtaleLogHom B.quotient A.quotient
  quotientSquare : B.quotientMap.Square quotientMap f.logMap A.quotientMap
  quotientStrict : quotientMap.IsStrict
  logComparison : LogBlowupComparison f.logMap A.tower B.tower
  schemeCartesian : ∀ i, IsPullback (logComparison.step i).base
    (logComparison.map i.succ).base (logComparison.map i.castSucc).base
    (A.tower.tower.arrow i).base
  centers : ∀ k, HEq
    ((A.center (logComparison.retained k)).comap
      (logComparison.map (logComparison.retained k).castSucc).base) (B.center k)
  unitCenter : ∀ i, i ∉ Set.range logComparison.retained ↔
    (A.center i).comap (logComparison.map i.castSucc).base = ⊤
  strictTransform : ∀ i, IsIso (strictTransformι (logComparison.map i.castSucc).base
    (A.tower.tower.arrow i).base (A.center i).support.compl)

set_option linter.checkUnivs false in
/-- One choice of presentations and their canonical comparisons, with actual equations
on quotient maps, retained indices and relative log maps. Universality in `Hom` includes
localizations, strict localizations, completions with induced divisorial structures
and stabilizer actions, and component inclusions of finite disjoint unions whenever
they are in the indicated class. No finite-type restriction is imposed on these maps.
Source: ILO VIII 5.4.2--5.4.5
(blueprint: lem-per-rigidified-quotient-tower-comparison). -/
structure ComparisonSystem (P : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u}) where
  construction : ∀ (G : Type v) [Group G] [Finite G] (X : Pair.{u, v} G), Construction P X
  comparison : ∀ {H G : Type v} [Group H] [Finite H] [Group G] [Finite G]
    {Y : Pair.{u, v} H} {X : Pair.{u, v} G} (f : Hom Y X),
    Comparison f (construction G X) (construction H Y)
  identity : ∀ (G : Type v) [Group G] [Finite G] (X : Pair.{u, v} G)
    (f : Hom X X), f.groupMap = MonoidHom.id G → f.logMap.IsIdentity →
    (comparison f).quotientMap.IsIdentity ∧
      ∀ i, (comparison f).logComparison.count i = i ∧
        HEq ((comparison f).logComparison.map i)
          (EtaleLogHom.id ((construction G X).tower.tower.level i))
  composition : ∀ {G H K : Type v}
    [Group G] [Finite G] [Group H] [Finite H] [Group K] [Finite K]
    {X : Pair.{u, v} G} {Y : Pair.{u, v} H} {Z : Pair.{u, v} K}
    (f : Hom Y X) (g : Hom Z Y) (h : Hom Z X),
    h.groupMap = f.groupMap.comp g.groupMap → g.logMap.CompEq f.logMap h.logMap →
    (comparison g).quotientMap.CompEq (comparison f).quotientMap (comparison h).quotientMap ∧
      ∀ i, (comparison h).logComparison.count i =
        (comparison g).logComparison.count ((comparison f).logComparison.count i) ∧
        HEq ((comparison h).logComparison.map i)
          (((comparison g).logComparison.map ((comparison f).logComparison.count i)).comp
            ((comparison f).logComparison.map i))

end RigidifiedQuotient

/-- A strict inert equivariant morphism of rigidified pairs induces a strict map of
invariant log quotients. The resolved towers are contracted scheme pullbacks, equal
to their strict-transform towers, with ordered centers and coherent comparisons.

Source: ILO VIII Proposition 5.4.2, Corollary 5.4.4 and 5.4.5, printed pp.126--127;
normalized towers 5.3.10--5.3.11
(blueprint: lem-per-rigidified-quotient-tower-comparison).

Proof (the seven steps of the live, Q17-corrected DAG node):
1. Give $X,Y$ their enlarged divisorial log structures $M_X,M_Y$. By the meaning of normal
crossings in the statement, every point has an etale neighbourhood on which the boundary is
strict normal crossings; the divisorial log structure restricts to the divisorial log structure
there, and fs log regularity is etale local. On it the regular-boundary chart theorem gives the
chart by those regular parameters, its regular stratum and the logarithmic dimension equality.
Thus both pairs are fs log regular. Apply the very-tame log-quotient theorem separately to the
two admissible generically free actions. Write $q_X:X\to Q_X$, $q_Y:Y\to Q_Y$. Their invariant
log structures are fs log regular, their quotient maps are finite surjective Kummer etale, and
their geometric fibres are orbits. The finite-quotient strict-local lemma also gives that
$Q_X,Q_Y$ are Noetherian. Equivariance and the invariant quotient property induce
$\bar\phi:Q_Y\to Q_X$.
Uses: lem-per-regular-boundary-divisorial-chart, lem-per-very-tame-log-quotient,
lem-per-finite-quotient-strict-local-invariants, def-per-fs-log-group-action,
def-trf-strict-normal-crossings-boundary.
Source: VI 1.7, 3.2; VIII 5.3.8 and 5.4.1.

2. Fix a geometric point $y$ and $x=\phi(y)$. Identify the two inertia groups using $\lambda$,
and call this group $K$. By strict-local invariants the log stalks on the quotients are
$M_{X,x}^K$ and $M_{Y,y}^K$. Choose the equivariant sharp chart $a:Q\to M_{X,x}$, with pairing
$\chi:K_{\rm ab}\otimes Q^{\rm gp}\to\mu_{|K|}$. Strictness pulls this chart back to a chart of
$M_{Y,y}$ with the same sharp monoid. Equivariance gives exactly the transported pairing:
$k(\phi^*a(q))=\phi^*(\chi_q(k))\phi^*a(q)$. The local quotient-chart lemma identifies both
quotient characteristics with $P=Q\cap\ker\chi$. Its hypotheses follow from very tameness
(invertible inertia order, fixed characteristic and stratum), and the finite strict-local
invariant rings from step 1; roots of unity and their fixedness come with the equivariant chart.
The map between quotient characteristics is the identity of $P$, since $a(p)$ pulls back to
$\phi^*a(p)$. Both quotient log stalks are logifications of this same chart, with their
respective unit groups. Their chart pushout formulas therefore identify the pulled-back target
log structure with the source log structure. This proves strictness of $\bar\phi$ at every
geometric point. In particular this uses the added strictness hypothesis, not just equality of
boundary supports.
Uses: lem-per-finite-quotient-strict-local-invariants,
lem-per-very-tame-equivariant-sharp-chart, lem-per-very-tame-local-kummer-quotient,
def-trf-fs-log-blowup, def-per-strict-log-morphism.
Source: VIII proof of Proposition 5.4.2; VI 3.5(a),(b) and 3.7.

3. Record the one-stage scheme calculation used below. For a strict map $(V,N)\to(W,M)$ and a
coherent log center generated by $E\subset P$ in a chart of $W$, use that same chart on $V$. On
affine charts with rings $A\to B$, the saturated blowup charts of the coherent-log-ideal
construction are $A\otimes_{\mathbf Z[P]}\mathbf Z[Q_e^{\rm sat}]$ and $B\otimes_{\mathbf
Z[P]}\mathbf Z[Q_e^{\rm sat}]$. The isomorphism $B\otimes_A(A\otimes_{\mathbf Z[P]}\mathbf
Z[Q_e^{\rm sat}])\simeq B\otimes_{\mathbf Z[P]}\mathbf Z[Q_e^{\rm sat}]$, $b\otimes(a\otimes
z^q)\mapsto ba\otimes z^q$, has inverse $b\otimes z^q\mapsto b\otimes(1\otimes z^q)$. It agrees
on all common monomial localizations, so identifies the underlying scheme square with an
ordinary Cartesian square. The algebraized center is extended from $(\alpha(e):e\in E)$ to
$(\phi^*\alpha(e):e\in E)$. This is a calculation from the cited chart statement, requiring no
flatness or assertion that normalization commutes with arbitrary base change.
Uses: lem-trf-coherent-log-ideal-chart-construction.
Source: VIII 3.3.8--3.3.10 and the chart calculation in Lemma 3.4.6(ii).

4. Apply the fixed regularization rule to the quotient log schemes. Its strict-pullback
comparison gives $\mathcal R(Q_Y)=C(\bar\phi^*\mathcal R(Q_X))$, with actual ordered centers.
This assertion may be checked on affine open neighborhoods in both quotients: each is Noetherian
separated fs log regular, so the regularization theorem applies, and the quotient map is strict
by step 2. This avoids assuming separatedness of a quotient merely from finiteness. On overlaps
the comparisons agree because the local theorem respects composition and is the same fixed
fan-induced rule. The existing etale-descent theorem constructs its global tower and the
contraction-descent theorem, applied with its strict etale map equal to the identity of $Q_Y$
and its tower $B=\bar\phi^*\mathcal R(Q_X)$, descends these local contracted comparisons along a
surjective strict etale cover of $Q_Y$. Finite covers suffice by Noetherianity. Thus the
comparison holds globally, and its retained indices delete exactly whole-log-monoid centers.
Uses: lem-per-gabber-log-blowup-regularization, lem-trf-functorial-log-blowup-etale-descent,
lem-trf-log-tower-contraction-descent.
Source: VIII 3.3.15; first paragraph of proof of Corollary 5.4.4.

5. Pull this ordered comparison back to $Y$. The commutative square $q_X\phi=\bar\phi q_Y$
identifies its uncontracted tower with the recursive fs pullback to $Y$ of the tower on $X$: a
saturated blowup of a pulled-back ideal has exactly the universal property of the fs fibre
product, so the two orders of pullback have the same unique factorization maps. At each level
the log center is the ideal generated by the image of the original center. Kummer-cover
base-change stability makes the pulled-back tower log regular, since the quotient stages are log
regular. The normalized-blowup comparison identifies its underlying morphism with the normalized
blowup of that algebraized ideal, and ensures log regularity for the next level. It applies on
integral components: a log regular scheme has normal-domain local rings by the
divisorial-structure theorem, so the finitely many irreducible components of a Noetherian such
scheme are disjoint open-and-closed integral schemes. Step 3 applied successively to the strict
map $Y\to X$ identifies this recursive tower with the ordinary scheme pullback. Its centers are
extended ideal sheaves, so this is also the normalized strict-transform tower. Hence the
quotient comparison gives precisely the claimed contracted scheme-pullback comparison on $Y$.
Uses: def-trf-fs-log-blowup, lem-trf-log-blowup-normalization,
lem-trf-log-regular-divisorial-structure, lem-trf-coherent-log-ideal-chart-construction,
lem-per-kummer-boundary-restriction.
Source: VIII 3.4.6, 3.4.8; 5.3.10--5.3.11 and proof of Corollary 5.4.4.

6. Contraction deletes a stage exactly when its log ideal is the whole monoid sheaf. This is
equivalent to its algebraized ideal being the unit ideal: at a local ring an ideal generated
entirely by nonunits is contained in the maximal ideal, whereas a unit generator is a unit log
section. The finite surjective $q_Y$ detects this unit condition: if a ring ideal were proper at
a point, its extension is contained in the maximal ideal at every point above it. Thus pulling
the quotient comparison to $Y$ introduces no further deleted indices, and no proper principal
center is deleted. The chart maps of step 3 and the unique universal-property maps of step 5 are
identities for an identity map and compose to the direct comparison. Deleting unit stages does
not change later extended ideals; successive deletions retain exactly the same ordered indices
as direct deletion. Together with the composition law of the fixed rule, this gives the stated
identity and composition laws. A component inclusion into a finite disjoint union is strict, so
this also gives componentwise compatibility without choosing separate resolution rules.
Uses: def-trf-fs-log-blowup, lem-per-gabber-log-blowup-regularization.
Source: VIII 3.3.10, 5.3.10; Corollary 5.4.4.

7. Apply the comparison to localization, strict localization and completion, with the induced
divisorial charts and the stabilizer action. These charts are pulled back as log charts, so
these are strict maps; on geometric stabilizers they give the indicated inertia isomorphisms.
Localizations of the regular scheme have its regular local rings. Strict henselization is
Noetherian and regular by the two cited strict-henselization results; completion of a Noetherian
regular local ring is Noetherian regular by the completion result. Thus these operations stay in
the indicated class whenever equipped with the boundary and action data in the statement, and
the preceding argument applies directly, without any finite-type or excellence assumption. In
particular one obtains the formulas of 5.4.5; finite disjoint unions are covered by step 6.
Uses: lem-sc-strict-henselization-noetherian, lem-sc-strict-henselization-regular,
lem-weil-pbc-completion-regular-local.
Source: VIII 5.4.5; strict-local version of 5.4.4. -/
theorem rigidifiedQuotient_tower_comparison
    (R : FineFan.SmoothFunctorialDesingularization.{u})
    (P : StrictEtaleLogBlowupProcedure IsLogBlowupInput.{u})
    (hP : RigidifiedQuotient.IsFanInduced R P) :
    Nonempty (RigidifiedQuotient.ComparisonSystem.{u, v} P) := by
  sorry

end AlgebraicGeometry
