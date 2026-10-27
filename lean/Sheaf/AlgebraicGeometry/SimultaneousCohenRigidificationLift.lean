/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.AlgebraicGeometry.GabberModificationData
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.VeryTameDivisorialAction
public import Sheaf.AlgebraicGeometry.FSStrictLogMorphism
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Connected.Basic

import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CohenRingModPowFormallySmooth
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.KrullDimension.Regular
import Sheaf.RingTheory.StrictHenselizationPresentationIn

/-! # Simultaneous Cohen lifts of two rigidifications

Source: ILO, Travaux de Gabber, VIII Lemma 5.5.2, proof, printed pp.127--128;
inertia induction VIII 5.3.6--5.3.7, pp.124--125
(blueprint: lem-per-simultaneous-cohen-rigidification-lift).

The auxiliary structures only unpack the witnesses of this lemma. Boundary models
are identified with the actual divisorial presheaves, including their structural maps.
The local coordinate witnesses retain the coefficient ring, both coordinate systems,
their common prefix, their eigencharacters, and the actual surjection to the original ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace SimultaneousCohenRigidification

/-- A divisorial fs log structure on a specified boundary, with its prescribed
structural map. Source: ILO VIII 5.5.2, pp.127--128; VI 1.1--1.2
(blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
structure BoundaryModel {X : Scheme.{u}} (D : X.IdealSheafData) where
  locallyNoetherian : IsLocallyNoetherian X
  logStructure : EtaleLogStructure X
  fineSaturated : logStructure.IsFineSaturated
  identification : logStructure.monoidSheaf.obj ≅
    divisorialLogPresheaf (Scheme.Opens.ι (X := X) D.support.compl)
  structural : identification.hom ≫
    divisorialStructuralMap (Scheme.Opens.ι (X := X) D.support.compl) = logStructure.alpha

/-- The fs log scheme of a boundary model, retaining its underlying scheme literally.
Source: ILO VIII 5.5.2 (blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
def BoundaryModel.logScheme {X : Scheme.{u}} {D : X.IdealSheafData}
    (M : BoundaryModel D) : FineSaturatedLogScheme.{u} :=
  ⟨X, M.locallyNoetherian, M.logStructure, M.fineSaturated⟩

/-- The canonical closed geometric point used to specify the inertia subgroup of a
complete local component. Source: ILO VIII 5.5.2 and 5.3.6
(blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
def closedGeometricPoint (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec (.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp
      (IsLocalRing.residue A)))

/-- The rank locus used in the conclusion, defined using all geometric lifts of an
ordinary point. Generic points of its connected components are taken in the subspace
topology, not in the ambient space. Source: ILO VIII 5.5.2, last paragraph of p.128
(blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
def rankLocus {X : Scheme.{u}} (M : EtaleLogStructure X) (n : ℕ∞) : Set X :=
  {x | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    t default = x → M.characteristicRank t = n}

/-- The two boundary-adapted coordinate systems in a positive-characteristic local
ambient piece. Coefficient compatibility fixes the SAME Cohen coefficient map in both
systems; the displayed eigencharacters are valued in that coefficient ring.
Source: ILO VIII 5.5.2, p.128 (blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
structure Coordinates (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (R : CommRingCat.{u}) (H : Type v) [Group H] (b : H →* RingAut R)
    (f : R →+* A) (p : ℕ) where
  coefficientRing : CommRingCat.{u}
  [coefficientLocal : IsLocalRing coefficientRing]
  cohen : IsCohenRing p coefficientRing
  residue : IsLocalRing.ResidueField coefficientRing ≃+* IsLocalRing.ResidueField A
  dimension : ℕ
  first : MvPowerSeries (Fin dimension) coefficientRing ≃+* R
  second : MvPowerSeries (Fin dimension) coefficientRing ≃+* R
  sameCoefficients : ∀ c : coefficientRing,
    second (MvPowerSeries.C c) = first (MvPowerSeries.C c)
  residueCompatibility : ∀ c : coefficientRing,
    IsLocalRing.residue A (f (first (MvPowerSeries.C c))) =
      residue (IsLocalRing.residue coefficientRing c)
  fixedCoefficients : ∀ (g : H) (c : coefficientRing),
    b g (first (MvPowerSeries.C c)) = first (MvPowerSeries.C c)
  character : Fin dimension → H →* coefficientRingˣ
  secondCharacter : Fin dimension → H →* coefficientRingˣ
  eigen : ∀ (g : H) (i : Fin dimension),
    b g (first (MvPowerSeries.X i)) =
      first (MvPowerSeries.C (character i g).val) * first (MvPowerSeries.X i)
  secondEigen : ∀ (g : H) (i : Fin dimension),
    b g (second (MvPowerSeries.X i)) =
      first (MvPowerSeries.C (secondCharacter i g).val) * second (MvPowerSeries.X i)
  parameters : IsLocalRing.IsRegularSystemOfParameters
    (List.ofFn (fun i ↦ f (first (MvPowerSeries.X i))))
  secondParameters : IsLocalRing.IsRegularSystemOfParameters
    (List.ofFn (fun i ↦ f (second (MvPowerSeries.X i))))
  originalBoundaryLength : ℕ
  firstBoundaryLength : ℕ
  secondBoundaryLength : ℕ
  original_le_first : originalBoundaryLength ≤ firstBoundaryLength
  original_le_second : originalBoundaryLength ≤ secondBoundaryLength
  first_le : firstBoundaryLength ≤ dimension
  second_le : secondBoundaryLength ≤ dimension
  commonPrefix : ∀ i : Fin dimension, i.val < originalBoundaryLength →
    second (MvPowerSeries.X i) = first (MvPowerSeries.X i)

/-- The three coordinate boundary ideals, in the order old boundary, first enlarged
boundary, second enlarged boundary. Empty products are one, hence give empty divisors.
Source: ILO VIII 5.5.2, p.128 (blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
def Coordinates.boundaryIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {R : CommRingCat.{u}} {H : Type v} [Group H]
    {b : H →* RingAut R} {f : R →+* A} {p : ℕ}
    (c : Coordinates A R H b f p) (r : Fin 3) : Ideal R :=
  Ideal.span {if r = 0 then
    ((List.ofFn (fun i ↦ c.first (MvPowerSeries.X i))).take c.originalBoundaryLength).prod
  else if r = 1 then
    ((List.ofFn (fun i ↦ c.first (MvPowerSeries.X i))).take c.firstBoundaryLength).prod
  else
    ((List.ofFn (fun i ↦ c.second (MvPowerSeries.X i))).take c.secondBoundaryLength).prod}

/-- One local ambient lift. In characteristic zero the surjection is an isomorphism;
in positive characteristic it has the two specified Cohen coordinate systems. The
subgroup is identified with closed geometric inertia in the global witness below.
Source: ILO VIII 5.5.2, pp.127--128 and 5.3.7
(blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
structure Piece (G : Type v) [Group G] (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] where
  inertia : Subgroup G
  ring : CommRingCat.{u}
  sourceAction : inertia →* RingAut A
  ambientAction : inertia →* RingAut ring
  projection : ring →+* A
  surjective : Function.Surjective projection
  equivariant : ∀ (g : inertia) (r : ring),
    projection (ambientAction g r) = sourceAction g (projection r)
  characteristicZero : ringChar (IsLocalRing.ResidueField A) = 0 →
    Function.Bijective projection
  positiveCharacteristic : ∀ (p : ℕ), p.Prime → CharP (IsLocalRing.ResidueField A) p →
    Coordinates A ring inertia ambientAction projection p

/-- A simultaneous ambient witness, including the finite cover by copies of the
original components, all three strict boundary maps, the common scheme quotient, and
its two invariant fs log regular structures. The final fields normalize the local
Cohen coordinates against the actual maps and boundary ideals.
Source: ILO VIII 5.5.2, pp.127--128; induction VIII 5.3.6--5.3.7
(blueprint: lem-per-simultaneous-cohen-rigidification-lift). -/
structure Lift (G : Type v) [Group G] [Finite G]
    (m : ℕ) (A : Fin m → Type u) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, IsNoetherianRing (A i)] (X : Scheme.{u})
    (components : X ≅ ∐ fun i ↦ Spec (.of (A i)))
    (D : Fin 3 → X.IdealSheafData) (M : BoundaryModel (D 1))
    (a : FSLogGroupAction G M.logScheme) where
  U : Scheme.{u}
  Y : Scheme.{u}
  h : U ⟶ X
  j : U ⟶ Y
  etale : Etale h
  surjective : Surjective h
  closed : IsClosedImmersion j
  boundary : Fin 3 → Y.IdealSheafData
  snc : ∀ r, IsStrictNormalCrossingsBoundary (boundary r)
  contains : ∀ r : Fin 2, (boundary 0).support ≤ (boundary r.succ).support
  pullbackBoundary : ∀ r, (boundary r).comap j = (D r).comap h
  sourceModel : ∀ r, BoundaryModel ((D r).comap h)
  ambientModel : ∀ r, BoundaryModel (boundary r)
  sourceAction : FSLogGroupAction G (sourceModel 1).logScheme
  ambientAction : ∀ r, FSLogGroupAction G (ambientModel r).logScheme
  sameAmbientAction : ∀ r, (ambientAction r).baseAction = (ambientAction 1).baseAction
  hLog : EtaleLogHom (sourceModel 1).logScheme M.logScheme
  hBase : hLog.base = h
  hInert : GabberModification.Inert sourceAction a (MonoidHom.id G) hLog
  jLog : ∀ r, EtaleLogHom (sourceModel r).logScheme (ambientModel r).logScheme
  jBase : ∀ r, (jLog r).base = j
  jStrict : ∀ r, (jLog r).IsStrict
  jInert : GabberModification.Inert sourceAction (ambientAction 1) (MonoidHom.id G) (jLog 1)
  noetherian : IsNoetherian Y
  regular : IsRegularScheme Y
  separated : Y.IsSeparated
  tame : (ambientAction 1).IsTame
  abelianInertia : GabberModification.AbelianInertia (ambientAction 1)
  groupStrict : GabberModification.GStrict (ambientAction 1).baseAction (boundary 0)
  freeOutside : GabberModification.FreeOpen (ambientAction 1) (boundary 0).support.compl
  invariant : ∀ (r : Fin 3) (g : G),
    (boundary r).comap ((ambientAction 1).baseAction g).hom = boundary r
  veryTame : ∀ r : Fin 2, (ambientAction r.succ).IsVeryTame
  logRegular : ∀ r : Fin 2, (ambientModel r.succ).logScheme.IsLogRegular
  Q : Scheme.{u}
  quotientNoetherian : IsLocallyNoetherian Q
  quotientLog : Fin 2 → EtaleLogStructure Q
  quotientFS : ∀ r, (quotientLog r).IsFineSaturated
  q : Y ⟶ Q
  quotientMap : ∀ r : Fin 2,
    EtaleLogHom (ambientModel r.succ).logScheme
      ⟨Q, quotientNoetherian, quotientLog r, quotientFS r⟩
  quotientBase : ∀ r, (quotientMap r).base = q
  invariantQuotient : ∀ r, (ambientAction r.succ).IsQuotient (quotientMap r)
  quotientLogRegular : ∀ r,
    FineSaturatedLogScheme.IsLogRegular ⟨Q, quotientNoetherian, quotientLog r, quotientFS r⟩
  integralAffineQuotient : ∃ (s : ℕ) (R : Fin s → CommRingCat.{u}),
    (∀ i, IsDomain (R i)) ∧ Nonempty (Q ≅ ∐ fun i ↦ Spec (R i))
  strataCharacteristicZero : ∀ (r : Fin 2) (n : ℕ∞) (x : Q),
    x ∈ rankLocus (quotientLog r) n →
      ∀ η : connectedComponentIn (rankLocus (quotientLog r) n) x,
        IsGenericPoint η Set.univ → CharZero (Q.residueField η.val)
  numberOfPieces : ℕ
  componentIndex : Fin numberOfPieces → Fin m
  piece : ∀ i, Piece G (A (componentIndex i))
  sourceComponents : U ≅ ∐ fun i ↦ Spec (.of (A (componentIndex i)))
  ambientComponents : Y ≅ ∐ fun i ↦ Spec (piece i).ring
  integralPieces : ∀ i, IsIntegral (Spec (piece i).ring)
  coverOnComponents : ∀ i,
    Sigma.ι (fun k ↦ Spec (.of (A (componentIndex k)))) i ≫ sourceComponents.inv ≫ h =
      Sigma.ι (fun k ↦ Spec (.of (A k))) (componentIndex i) ≫ components.inv
  immersionOnComponents : ∀ i,
    Sigma.ι (fun k ↦ Spec (.of (A (componentIndex k)))) i ≫ sourceComponents.inv ≫ j =
      Spec.map (CommRingCat.ofHom (piece i).projection) ≫
        Sigma.ι (fun k ↦ Spec (piece k).ring) i ≫ ambientComponents.inv
  closedInertia : ∀ (i : Fin numberOfPieces) (g : G), g ∈ (piece i).inertia ↔
    closedGeometricPoint (A (componentIndex i)) ≫
        Sigma.ι (fun k ↦ Spec (.of (A k))) (componentIndex i) ≫ components.inv ≫
          (a.baseAction g).hom =
      closedGeometricPoint (A (componentIndex i)) ≫
        Sigma.ι (fun k ↦ Spec (.of (A k))) (componentIndex i) ≫ components.inv
  sourceActionOnComponents : ∀ (i : Fin numberOfPieces) (g : (piece i).inertia),
    Spec.map (CommRingCat.ofHom ((piece i).sourceAction g).symm.toRingHom) ≫
        Sigma.ι (fun k ↦ Spec (.of (A k))) (componentIndex i) ≫ components.inv =
      Sigma.ι (fun k ↦ Spec (.of (A k))) (componentIndex i) ≫ components.inv ≫
        (a.baseAction g.val).hom
  ambientActionOnComponents : ∀ (i : Fin numberOfPieces) (g : (piece i).inertia),
    Spec.map (CommRingCat.ofHom ((piece i).ambientAction g).symm.toRingHom) ≫
        Sigma.ι (fun k ↦ Spec (piece k).ring) i ≫ ambientComponents.inv =
      Sigma.ι (fun k ↦ Spec (piece k).ring) i ≫ ambientComponents.inv ≫
        ((ambientAction 1).baseAction g.val).hom
  coordinateBoundaries : ∀ (i : Fin numberOfPieces) (p : ℕ) (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (A (componentIndex i))) p) (r : Fin 3),
    (((boundary r).comap
      (Sigma.ι (fun k ↦ Spec (piece k).ring) i ≫ ambientComponents.inv)).ideal
        ⟨⊤, isAffineOpen_top (Spec (piece i).ring)⟩).map
          (Scheme.ΓSpecIso (piece i).ring).hom.hom =
      ((piece i).positiveCharacteristic p hp hchar).boundaryIdeal r

end SimultaneousCohenRigidification

/-- Simultaneously lift two very tame rigidifications to a common characteristic-zero
ambient model, after the specified strict inert cover by copies of the local components.

Source: ILO VIII Lemma 5.5.2, proof, pp.127--128; VIII 5.3.6--5.3.7
(blueprint: lem-per-simultaneous-cohen-rigidification-lift).

Proof (the eleven steps of the accepted DAG split):

1. Reduce to closed geometric inertia, keeping track of the eventual cover. Choose one component
$X_i=\operatorname{Spec}A$ in each $G$-orbit of components, its closed point $x$, and $H\leq G$
the stabilizer of a geometric point over $x$. Any geometric inertia at a point of $X_i$ is
contained in $H$: an element fixing that geometric point preserves the component, and $g(a)-a$
lies in its prime ideal for all $a\in A$, hence lies in the maximal ideal, so $g$ is trivial on
the closed residue field. Thus $H$ is abelian, fixes $k$, and $N=|H|$ is a unit in $A$. We
construct an $H$-equivariant closed embedding of $X_i$ into a local ambient piece. At the end we
induce each such piece from $H$ to $G$. For residue characteristic zero take the ambient piece to
be $X_i$ itself. Regular local rings and all their localizations are regular domains by the cited
statements, so these pieces are integral and regular.
Uses: lem-sc-regular-local-domain, lem-weil-pbc-regular-local-localization.

2. $A$ is henselian by the complete-pair theorem, hence strictly henselian. Take an affine pointed
etale chart $(V,v)\to X_i$ at the closed point where $D_a$ is a product of distinct regular
parameters of $\mathcal O_{V,v}$. Its residue field is finite separable over $k$, hence $k$, so
the henselian retraction gives a section $s:X_i\to V$ through $v$, a clopen immersion as $V$ is
separated; thus $A=\mathcal O_{V,v}$ and $D_a=V(w_1\cdots w_n)$ with $w_1,\ldots,w_n$ part of a
regular system of parameters of $A$. Check the strict-normal-crossings definition: for
$J\subseteq\{1,\ldots,n\}$, $(w_j)_{j\in J}$ is a regular sequence and $A/(w_j:j\in J)$ is regular
local of dimension $\dim A-|J|$, hence a domain with regular localizations, so each $C_J$ is
integral and regular. At a prime $\mathfrak p\supseteq(w_J)$ the localized sequence stays regular
and the dimension formula gives $\dim A_{\mathfrak p}=\dim\mathcal O_{C_J,\mathfrak p}+|J|$. The
product is a nonzerodivisor, and $(w_1\cdots w_n)=\bigcap_j(w_j)$ by induction: if $c=w_1b$ lies
in every $(w_j)$, then for $j\ge2$ the prime $(w_j)$ does not contain $w_1$ (independent cotangent
classes), so $b\in\bigcap_{j\ge2}(w_j)=(w_2\cdots w_n)$. So $D_a$ is a strict normal crossings
boundary, and each component of $B$, an integral codimension-one closed subset of $|D_a|$, is one
of its branches. The regular-boundary chart statement then gives the chart $\mathbf N^n$ at $x$,
with branch equations having independent cotangent lines. Inertia $H$ fixes each branch of $D_a$
since it fixes the characteristic monoid. Its branches belonging to $B$ are the same for the two
divisors.
Uses: lem-weil-pbc-complete-pair-henselian, lem-weil-pbc-henselian-etale-retraction, lem-weil-pbc-
etale-section-clopen-immersion, lem-weil-pbc-regular-local-generators-regular-sequence, lem-sc-
regular-local-domain, lem-weil-pbc-regular-local-localization, lem-weil-pbc-weakly-regular-
sequence-localization-prime, lem-trf-regular-sequence-dimension-formula, def-trf-strict-normal-
crossings-boundary, lem-per-regular-boundary-divisorial-chart.

3. Now suppose $\operatorname{char}k=p>0$. Choose a Cohen ring $C$ with residue field $k$.
Construct a map $C\to A^H$ without assuming an invariant coefficient section in advance. Put
$R_n=(A/\mathfrak m^n)^H$. Averaging with $N^{-1}\sum_hh$ shows $R_n\to R_{n-1}$ is surjective;
its kernel is square-zero for $n\geq2$, and $p^nR_n=0$. Starting with $C/p\simeq R_1=k$, formal
smoothness of $C/p^n$ over $\mathbf Z/p^n$ lifts the composite $C/p^n\to C/p^{n-1}\to R_{n-1}$ to
$R_n$ compatibly for every $n$. Completeness $A=\varprojlim A/\mathfrak m^n$ gives the required
invariant local map $C\to A$. Both $C$ and $A$ are henselian. Apply the cyclotomic finite etale
cover and the henselian retraction to $C$: separable closedness of $k$ supplies a point with
residue $k$, so $C$ contains an $H$-fixed primitive $N$th root $\zeta$ with every $1-\zeta^a$ a
unit. Its image has the same properties in $A$.
Uses: lem-weil-pbc-cohen-rings-exist, lem-weil-pbc-cohen-ring-mod-pn-formally-smooth, def-weil-
pbc-adic-completion, lem-weil-pbc-complete-pair-henselian, lem-per-cyclotomic-finite-etale-cover,
lem-weil-pbc-henselian-etale-retraction.

4. Choose equations for the branches of $B$ and apply the character projector to each. Its
principal ideal is $H$-stable, so the projector stays in that ideal and preserves its nonzero
cotangent class; the new equation is therefore a unit multiple of the old one. Keep these same
equations $z_1,\ldots,z_l$ for both divisors. For each $D_a$, do the same with its other branch
equations, and extend their independent cotangent eigenvectors to an eigenbasis. Lift and project
the remaining basis vectors. Nakayama applied to the finitely generated maximal ideal, and the
regular cotangent-dimension statement, show that these lists are regular parameter systems
$z=(z_1,\ldots,z_d)$ and $z'=(z'_1,\ldots,z'_d)$, with common first $l$ entries, and
$D_1=V(\prod_{i\leq n_1}z_i)$, $D_2=V(\prod_{i\leq n_2}z'_i)$. All characters take values in
$\langle\zeta\rangle$. The projector formula is applied to the semilinear modules $A$ and
$\mathfrak m$, not to an assumed linear action on $A$ over $k$.
Uses: lem-per-semilinear-character-projector-lifting, lem-weil-pbc-nakayama-local-generators, lem-
weil-pbc-regular-local-cotangent-dimension.

5. Set $R=C[[t_1,\ldots,t_d]]$ and let $f:R\to A$ send $t_i$ to $z_i$ and use the invariant
coefficient map of Step 3. The power-series evaluation theorem constructs $f$. It is local,
induces the identity on $k$, and is surjective on cotangent spaces because the $z_i$ generate
$\mathfrak m$. The complete-local cotangent-surjectivity theorem therefore makes $f$ surjective.
Give $R$ the continuous diagonal $H$-action fixing $C$ and sending $t_i$ to $\chi_i(h)t_i$;
evaluating a monomial shows $f$ is equivariant, hence evaluating the convergent degree truncations
shows the same for every series. The ambient local ring $R$ is Noetherian, complete, regular and
integral by the field/Cohen power-series theorem. Its spectrum is regular by regular-local
localization. Apply the relative-coordinate-lift node to obtain $t'_i$ lifting $z'_i$, with
$t'_i=t_i$ for $i\leq l$, and $R=C[[t'_1,\ldots,t'_d]]$ over the same $C$, equivariantly.
Uses: lem-weil-pbc-power-series-universal-property-complete, lem-sfb-complete-local-cotangent-
graded-rigidity, lem-weil-pbc-power-series-field-cohen-regular-complete, lem-weil-pbc-regular-
local-localization, lem-per-equivariant-relative-coordinate-lift.

6. On $Y_i=\operatorname{Spec}R$ put $E=V(\prod_{i\leq l}t_i)$, $E_1=V(\prod_{i\leq n_1}t_i)$ and
$E_2=V(\prod_{i\leq n_2}t'_i)$. Each coordinate intersection is a Cohen power-series ring by the
variable-quotient theorem, also for the primed system by its $C$-algebra coordinate isomorphism.
These rings are regular domains, and their localizations are regular. A coordinate sublist is a
regular sequence; its localization at a prime containing it remains regular, and the regular-
sequence dimension formula gives the codimension equal to its length at every point. The product
of distinct coordinate variables is a nonzerodivisor and its ideal is the intersection of their
prime ideals: coefficientwise, divisibility by each variable means divisibility by their product.
Thus the finite coordinate components and intersections satisfy precisely the strict-normal-
crossings definition. Invariance follows from their eigenvector equations; each component is
individually $H$-stable. The regular-boundary chart statement makes both enlarged pairs fs log
regular. Scheme-theoretic inverse images are the indicated original products. The charts $\mathbf
N^l$ and $\mathbf N^{n_a}$ pull back by the very same equations, proving strictness of
$j_i:\operatorname{Spec}A\hookrightarrow Y_i$ for all three structures.
Uses: lem-weil-pbc-power-series-quotient-variables, lem-weil-pbc-power-series-field-cohen-regular-
complete, lem-weil-pbc-regular-local-localization, lem-weil-pbc-regular-local-generators-regular-
sequence, lem-weil-pbc-weakly-regular-sequence-localization-prime, lem-trf-regular-sequence-
dimension-formula, def-trf-strict-normal-crossings-boundary, lem-per-regular-boundary-divisorial-
chart, def-trf-fs-log-blowup, def-weil-closed-immersion.

7. For each nonidentity $g\in H$, let $I_g=\{i:\chi_i(g)\ne1\}$. The ideal of differences $g(a)-a$
in $A$ is exactly $J_g=(z_i:i\in I_g)$: one inclusion uses the generators, whose nontrivial
character differences are units, and the other follows by setting the same variables equal to zero
in a power series preimage under $f$. The quotient $A/J_g$ is a regular local domain, by the
parameter-quotient and regular-domain results. Consequently $J_g$ is prime, and $g$ fixes every
geometric point of its spectrum. Freeness on $X_i\setminus B$ forces $\prod_{i\leq l}z_i\in J_g$.
Primality, and independence of the parameter classes, give an index $i\leq l$ in $I_g$. On $R$, a
geometric fixed point of $g$ must have $t_i=0$ for this index. Thus $H$ acts freely on
$Y_i\setminus E$. Its geometric inertia groups are subgroups of the abelian group $H$, and their
orders are units since $N$ is a unit in $C$. The map $j_i$ is inert: if $g j_i(\bar u)=j_i(\bar
u)$, equivariance and the monomorphism $j_i$ give $g\bar u=\bar u$; the reverse implication is
immediate.
Uses: lem-weil-pbc-regular-local-generators-regular-sequence, lem-sc-regular-local-domain, lem-
weil-pbc-power-series-quotient-variables.

8. The two lifted actions are very tame. For the unprimed system, very tameness on $A$ says $H$
fixes $A/(z_1,\ldots,z_{n_1})$. Each remaining $z_i$ has nonzero cotangent class in this quotient,
so its character must be trivial (a nontrivial root minus $1$ is a unit). Hence $H$ fixes
$R/(t_1,\ldots,t_{n_1})=C[[t_{n_1+1},\ldots,t_d]]$ pointwise. It also fixes the characteristic
monoid at the closed point since each coordinate divisor is invariant, and is tame there. The
closed residue field of $R$ is separably closed and $R$ is complete henselian, so each pointed
affine etale neighborhood admits the unique residue-preserving retraction. These retractions
identify their colimit, the strict local ring, with $R$. This proves very tameness at its closed
point. The affine scheme $Y_i=\operatorname{Spec}R$ is separated over $\operatorname{Spec}\mathbf
Z$: its diagonal is the closed immersion induced by the surjective multiplication map
$R\otimes_{\mathbf Z}R\to R$. Thus the separatedness hypothesis of the very-tame-locus theorem
holds; its other hypotheses are the Noetherian fs log regularity from Steps 5--6 and the finite
log action from the invariant divisors. The very-tame locus is therefore open; an open subset
containing the closed point of a local spectrum is the whole spectrum. Repeat with $t'$ and $n_2$
for $E_2$. In characteristic zero the chosen ambient scheme and its two log structures were the
original ones, already very tame.
Uses: lem-weil-pbc-power-series-quotient-variables, lem-per-very-tame-locus-open, lem-weil-pbc-
complete-pair-henselian, lem-weil-pbc-henselian-etale-retraction, def-sc-ring-strict-
henselization.

9. Each local ambient scheme is affine and integral. Apply the very-tame log-quotient theorem
separately to its two fs log regular structures; its admissibility hypothesis holds since it is
affine, and generic freeness holds by Step 7 (or the original free complement in characteristic
zero). Both applications have the same underlying categorical scheme quotient $Q_i=Y_i/H$, with
invariant log structures and finite surjective quotient map having orbit geometric fibres. Both
log structures are fs log regular and both quotient maps are Kummer etale. The affine-quotient
statement identifies $Q_i$ with $\operatorname{Spec}(R^H)$ (with $R=A$ in characteristic zero). A
subring of a domain is a domain, so $Q_i$ is integral.
Uses: lem-per-very-tame-log-quotient, lem-per-admissible-quotient-affine-integral-charts.

10. Verify the characteristic of every quotient stratum, for either coordinate system $v=t$ or
$t'$. Its source rank-$r$ locus is the disjoint union, over $|S|=r$ with
$S\subseteq\{1,\ldots,n_a\}$, of $V(v_i:i\in S)\setminus\bigcup_{j\notin S,\ j\leq n_a}V(v_j)$.
Each is nonempty integral: its ring is the localization of $C[[v_j:j\notin S]]$ obtained by
inverting the other boundary variables. It is closed in the rank-$r$ locus, and with finitely many
such pieces it is also open there. Its generic point has characteristic zero, since this domain
contains the Cohen ring $C$, which has characteristic zero. Kummer characteristic maps have equal
group ranks (injectivity and a positive multiple of every target element in the image give equal
rational spans), so quotient rank loci have exactly these inverse images. Diagonal $H$ preserves
each coordinate pattern. Orbit fibres make their images disjoint, and finiteness makes each image
closed in the quotient rank locus. Thus these integral images are precisely its connected
components. A source generic point maps to the generic point of its integral image; the injection
of residue fields preserves characteristic, proving the claim for every quotient stratum. For
residue characteristic zero, $\mathbf Q\subset A$ and hence $\mathbf Q\subset A^H$, so every
quotient point has characteristic zero directly.
Uses: lem-weil-pbc-power-series-quotient-variables, lem-weil-pbc-power-series-field-cohen-regular-
complete, lem-per-very-tame-log-quotient.

11. Finish the induction promised in Step 1. For each chosen component define $U_i=G\times^H X_i$
and $Y_i^{\rm ind}=G\times^H Y_i$ as copies indexed by $G/H$: $[g,x]\mapsto g x$ defines $h_i$,
and $[g,x]\mapsto[g,j_i(x)]$ defines $j_i^{\rm ind}$. This is well-defined since $(gh,x)$ is
identified with $(g,hx)$ and $j_i$ is $H$-equivariant. A geometric stabilizer of $[g,x]$ is
$gH_xg^{-1}$; the corresponding stabilizer in $X$ is $gG_xg^{-1}=gH_xg^{-1}$ by Step 1. The same
computation, with inertness of $j_i$, treats the other map. Each copy of $X_i$ maps isomorphically
to a component of $X$ and the chosen orbit representatives make $h=\coprod h_i$ surjective etale.
Finite coproducts of affine spectra are affine and separated (the affine diagonal is the closed
immersion induced by the surjective multiplication map); $j=\coprod j_i^{\rm ind}$ is a closed
immersion of finite coproducts. Transport the three divisors to every copy. Their pullback
equations, strictness, regularity, very tameness, free complement and abelian tame inertia are
checked on the copies. Distinct translates of an $E$ component either coincide or lie in disjoint
copies, proving $G$-strictness. Finally $(G\times^H Y_i)/G=Y_i/H$: on invariant functions an
invariant tuple is determined by its identity-coset entry in $R^H$. The same statement for
invariant log sections identifies both induced log quotients with the local quotients of Steps 9--
10. Their finite disjoint union has every claimed property. For $m=0$ all schemes and divisors are
empty; for $d=0$ the positive-characteristic piece is $\operatorname{Spec}C$, and all empty
products and parameter lists used above have their stated meanings.
Uses: lem-weil-pbc-finite-affine-coproduct-spectrum.
-/
theorem exists_simultaneousCohenRigidificationLift
    (G : Type v) [Group G] [Finite G]
    (m : ℕ) (A : Fin m → Type u) [∀ i, CommRing (A i)]
    [∀ i, IsRegularLocalRing (A i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i)]
    [∀ i, IsSepClosed (IsLocalRing.ResidueField (A i))]
    (X : Scheme.{u}) (components : X ≅ ∐ fun i ↦ Spec (.of (A i)))
    (D : Fin 3 → X.IdealSheafData)
    (M : SimultaneousCohenRigidification.BoundaryModel (D 1))
    (a : FSLogGroupAction G M.logScheme)
    (hB : IsStrictNormalCrossingsBoundary (D 0))
    (hBstrict : GabberModification.GStrict a.baseAction (D 0))
    (hInvariant : ∀ (r : Fin 3) (g : G), (D r).comap (a.baseAction g).hom = D r)
    (hContains : ∀ r : Fin 2, (D 0).support ≤ (D r.succ).support)
    (hNC : ∀ r : Fin 2, (D r.succ).IsNormalCrossingsDivisor)
    (hTame : a.IsTame) (hAbelian : GabberModification.AbelianInertia a)
    (hFree : GabberModification.FreeOpen a (D 0).support.compl)
    (hVeryTame : a.IsVeryTame)
    (hSecondVeryTame : IsVeryTameDivisorialAction (D 2).support.compl a.baseAction) :
    Nonempty (SimultaneousCohenRigidification.Lift G m A X components D M a) := by
  sorry

end AlgebraicGeometry
