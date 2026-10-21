/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SupportedCup
public import Sheaf.Paper.LocalizedFlagProduct
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.SupportedCohomologyHom
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.Paper.SupportedCupFunctoriality
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.ProjectionMateExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.CartierClassAgreement
import Sheaf.Paper.PurityDivisorClass
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coordinate Gysin composition and supported Kummer products

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
localized-top-Chern proof, Step 3 (blueprint: lem-pur-flag-local-comparison).

The coordinate tower is actual affine space over an arbitrary base. Its nested
classes use localizedFlagCompose; the other side is the published left-associated
frameBoundaryProduct on the full ambient space, multiplied by (-1)^r. All support
comparisons are over
that space and normalized by the coordinate zero section.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate affine space, with the size convention of def-sbc-affine-space.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
abbrev flagCoordinateSpace (S : Scheme.{u}) (r : ℕ) :=
  AffineSpace (ULift.{u} (Fin r)) S

/-- Ordered coordinates on the full ambient affine space.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinates (S : Scheme.{u}) (r : ℕ) :
    Fin r → Γ(flagCoordinateSpace S r, ⊤) :=
  fun j ↦ AffineSpace.coord S (ULift.up j)

/-- The actual zero section, defined by the all-zero coordinate vector.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinateZero (S : Scheme.{u}) (r : ℕ) : S ⟶ flagCoordinateSpace S r :=
  AffineSpace.homOfVector (𝟙 S) (fun _ ↦ 0)

/-- Append the zero final coordinate; the preceding coordinates remain unchanged.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinateInclusion (S : Scheme.{u}) (r : ℕ) :
    flagCoordinateSpace S r ⟶ flagCoordinateSpace S (r + 1) :=
  AffineSpace.homOfVector (flagCoordinateSpace S r ↘ S)
    (fun j ↦ Fin.lastCases 0 (fun i ↦ flagCoordinates S r i) j.down)

/-- Coordinate inclusions are closed Cartier divisors, even over nonreduced bases;
the zero section is closed. The zero sections compose along the tower.
Source: blueprint Step 3, proof Step 1 (blueprint: lem-pur-flag-local-comparison).
Proof: on each affine chart the inclusion is the quotient of a polynomial ring
by its final variable. Coefficient comparison proves that variable is regular.
The zero section is the quotient by all variables. These chart descriptions glue;
the composition equation follows by its base map and all coordinate functions. -/
theorem flagCoordinateGeometry (S : Scheme.{u}) (r : ℕ) :
    IsClosedImmersion (flagCoordinateZero S r) ∧
      IsClosedImmersion (flagCoordinateInclusion S r) ∧
      (flagCoordinateInclusion S r).ker.IsInvertible ∧
      flagCoordinateZero S r ≫ flagCoordinateInclusion S r =
        flagCoordinateZero S (r + 1) := by
  sorry

/-- Closedness of the coordinate zero section.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
instance flagCoordinateZero_closed (S : Scheme.{u}) (r : ℕ) :
    IsClosedImmersion (flagCoordinateZero S r) := (flagCoordinateGeometry S r).1

/-- Closedness of each successive coordinate divisor.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
instance flagCoordinateInclusion_closed (S : Scheme.{u}) (r : ℕ) :
    IsClosedImmersion (flagCoordinateInclusion S r) := (flagCoordinateGeometry S r).2.1

/-- At rank zero the supported coefficient restriction is invertible.
Source: blueprint Step 3, empty flag (blueprint: lem-pur-flag-local-comparison).
Proof: affine zero-space projects isomorphically to S, and its zero section is
its inverse. Restriction of constants along an isomorphism is an isomorphism. -/
theorem flagCoordinateEmptyRestriction (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    IsIso (P.localizedFlagRestriction (flagCoordinateZero S 0)) := by
  sorry

/-- The unique family specified by the identity at zero and the published nested
Cartier composition at each successor. HEq only identifies equal endpoint
presentations using the zero-section composition equation.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def FlagCoordinateThetaNormalization (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    (θ : ∀ r : ℕ, P.LocalizedFlagH (flagCoordinateZero S r) (2 * (r : ℤ)) (r : ℤ)) :
    Prop :=
  HEq (θ 0) (localizedFlagInitialModel
    (P.localizedFlagRestriction (flagCoordinateZero S 0)) (P.flagCoordinateEmptyRestriction S)) ∧
    ∀ r : ℕ, HEq (θ (r + 1))
      (P.localizedFlagCompose (flagCoordinateZero S r) (flagCoordinateInclusion S r)
        (flagCoordinateGeometry S r).2.2.1 (flagCoordinateSpace S (r + 1) ↘ S ≫ aS) r (θ r))

/-- The normalized nested Cartier family exists uniquely.
Source: blueprint Step 3, definition of Theta (blueprint: lem-pur-flag-local-comparison).
Proof: start with localizedFlagInitialModel and recursively apply localizedFlagCompose.
Transport each source by flagCoordinateGeometry's composition equation. This constructs
a family with the stated normalization. Nat induction proves uniqueness, since each
successor is fixed by the previous map and the specified Cartier composition. -/
theorem flagCoordinateTheta_existsUnique (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k)) :
    ∃! θ : ∀ r : ℕ, P.LocalizedFlagH (flagCoordinateZero S r) (2 * (r : ℤ)) (r : ℤ),
      P.FlagCoordinateThetaNormalization aS θ := by
  sorry

/-- The actual nested family, chosen from a unique normalization, never from mere existence.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinateThetaEtale (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k)) :=
  (P.flagCoordinateTheta_existsUnique aS).exists.choose

/-- The same nested class on the pro-etale site, with the published supported comparison.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinateTheta (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k)) (r : ℕ) :
    P.FunctorialCupH true (flagCoordinateZero S r) (2 * (r : ℤ)) (r : ℤ) :=
  P.functorialCupCompare (flagCoordinateZero S r) (2 * (r : ℤ)) (r : ℤ)
    (P.flagCoordinateThetaEtale aS r)

/-- The simultaneous coordinate zero scheme is canonically S over affine r-space.
Source: blueprint Step 3, coordinate frame (blueprint: lem-pur-flag-local-comparison).
Proof: on affine charts, quotienting R[x_1,...,x_r] by all variables gives R,
with inverse the constants map. These quotient isomorphisms agree on overlaps.
An isomorphism over the ambient scheme is unique since its zero section is monic. -/
theorem flagCoordinateSupport_existsUnique (S : Scheme.{u}) (r : ℕ) :
    ∃! e : (flagCoordinateSpace S r).zeroLocusSubscheme
        (Set.range (flagCoordinates S r)) ≅ S,
      e.hom ≫ flagCoordinateZero S r =
        (flagCoordinateSpace S r).zeroLocusSubschemeι (Set.range (flagCoordinates S r)) := by
  sorry

/-- The quotient-normalized support isomorphism.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinateSupportIso (S : Scheme.{u}) (r : ℕ) :=
  (flagCoordinateSupport_existsUnique S r).exists.choose

/-- The support isomorphism lies over the full ambient affine space.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison).
Proof: this is the defining property of flagCoordinateSupport_existsUnique. -/
theorem flagCoordinateSupportIso_over (S : Scheme.{u}) (r : ℕ) :
    (flagCoordinateSupportIso S r).hom ≫ flagCoordinateZero S r =
      (flagCoordinateSpace S r).zeroLocusSubschemeι (Set.range (flagCoordinates S r)) := by
  sorry

/-- The ordered frame product in the full ambient space, with support transported
by the coordinate quotient isomorphism. Each factor is the individual boundary
for V(x_j) in affine r-space, not a boundary on a smaller coordinate subspace.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinateCup (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k)) (r : ℕ) :
    P.FunctorialCupH true (flagCoordinateZero S r) (2 * (r : ℤ)) (r : ℤ) :=
  (cupSingle P (flagCoordinateSpace S r)).map
    (P.frameClosedCoefficientIso
      ((flagCoordinateSpace S r).zeroLocusSubschemeι (Set.range (flagCoordinates S r)))
      (flagCoordinateZero S r) (flagCoordinateSupportIso S r)
      (flagCoordinateSupportIso_over S r)).inv ≫
    P.frameBoundaryProduct (flagCoordinateSpace S r)
      (flagCoordinateSpace S r ↘ S ≫ aS) r (flagCoordinates S r)

/-- The zero-section square for any base morphism is Cartesian.
Source: blueprint Step 3, restriction (blueprint: lem-pur-flag-local-comparison).
Proof: base change of affine space is affine space by AffineSpace.isPullback_map.
Its all-zero section pulls back to the all-zero section, as is checked on coordinates;
pasting this square with the affine-space square proves it is Cartesian. -/
theorem flagCoordinateBaseChange_cartesian {T S : Scheme.{u}} (f : T ⟶ S) (r : ℕ) :
    IsPullback f (flagCoordinateZero T r) (flagCoordinateZero S r)
      (AffineSpace.map (ULift.{u} (Fin r)) f) := by
  sorry

/-- The canonical chosen square from the actual coordinate Cartesian square.
Source: blueprint Step 3 (blueprint: lem-pur-flag-local-comparison). -/
def flagCoordinateBaseChange {T S : Scheme.{u}} (f : T ⟶ S) (r : ℕ) :
    ChosenCartesianSquare f (flagCoordinateZero T r) (flagCoordinateZero S r)
      (AffineSpace.map (ULift.{u} (Fin r)) f) where
  w := (flagCoordinateBaseChange_cartesian f r).w
  isoPullback := (flagCoordinateBaseChange_cartesian f r).isoPullback
  hom_fst := (flagCoordinateBaseChange_cartesian f r).isoPullback_hom_fst
  hom_snd := (flagCoordinateBaseChange_cartesian f r).isoPullback_hom_snd

/-- The coordinate pair satisfies the frame hypotheses with geometric rank r,
independently of the positive coefficient level P.level.
Source: blueprint Step 3, proof Step 7 (blueprint: lem-pur-flag-local-comparison).
Proof: affine r-space is smooth of relative dimension r over S; the zero section
followed by projection is the identity. Finite type over the field implies
Noetherianity. At a zero-section point, successively quotient the local polynomial
ring by its coordinate regular sequence. Each nonzerodivisor quotient decreases
Krull dimension by one, giving the asserted codimension, including r=0. -/
theorem flagCoordinateSmoothPair (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS] (r : ℕ) :
    SmoothOfRelativeDimension r (flagCoordinateSpace S r ↘ S) ∧
      Smooth (flagCoordinateZero S r ≫ flagCoordinateSpace S r ↘ S) ∧
      ∀ z : S, ringKrullDim ((flagCoordinateSpace S r).presheaf.stalk
        (flagCoordinateZero S r z)) =
        ringKrullDim (S.presheaf.stalk z) + (r : WithBot ℕ∞) := by
  sorry

/-- The pro-etale supported coefficient restriction in rank zero is invertible.
Source: blueprint Step 3, empty flag (blueprint: lem-pur-flag-local-comparison).
Proof: the zero section is an isomorphism in rank zero. Pullback of constants
and the isomorphism adjunction identify its restriction map with an isomorphism. -/
theorem flagCoordinateEmptyProRestriction (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    IsIso (cupCoefficientRestriction P (flagCoordinateZero S 0)) := by
  sorry

/-- Coordinate comparison, its restriction compatibility, and the empty-flag identity.
Source: blueprint main-20261015, localized-top-Chern proof, Step 3
(blueprint: lem-pur-flag-local-comparison).

Proof:
1. For each $j\geq1$ and $1\leq l\leq j$, put $D_{j,l}=V(x_l)\subset E_j$. On an affine chart
these are polynomial coordinate divisors: multiplication by $x_l$ is injective by comparison of
polynomial coefficients, even over a nonreduced ring. Their intersections are defined by the sums
of their coordinate ideals. Write $\beta_{j,l}=-\partial\kappa(x_l)\in H^2_{D_{j,l}}(E_j,A(1))$.
The corrected local-equation formula in [lem-pur-divisor-class], followed by
[lem-pur-cartier-class-agreement], says that the negative boundary has supported-Hom
representative $c_{D_{j,l},A}$. In particular $D_{j,j}=E_{j-1}$ and this representative is $d_j$
of [lem-pur-flag-localized-product]. These schemes are separated finite type, and coordinate
divisors and their successive coordinate pullbacks remain Cartier, so the base-change assertion of
[lem-amb-cartier-kummer-map] applies whenever used below. Uses: def-sbc-affine-space,
lem-pur-divisor-class, lem-pur-cartier-class-agreement, lem-pur-flag-localized-product,
lem-amb-cartier-kummer-map.

2. Define $Q_j=\beta_{j,1}\cup\cdots\cup\beta_{j,j}\in H^{2j}_{E_0}(E_j,A(j))$, with $Q_0=1$ on
$E_0=S$. Let $p_j:E_j\to E_{j-1}$ forget $x_j$, so $p_ja_j=\operatorname{id}$. Put
$C_j=V(x_1,\ldots,x_{j-1})\subset E_j$ and $R_j=p_j^*Q_{j-1}$. By
[lem-pur-supported-cup-functoriality] and Step 1, $R_j$ is the product of the first $j-1$
coordinate classes in $E_j$, and $a_j^*R_j=Q_{j-1}$. The supports here are $p_j^{-1}(E_0)=C_j$ and
$C_j\times_{E_j}E_{j-1}=E_0$. By [lem-pur-supported-hom], write its representative as
$\gamma_j:P_{C_j}\to L_j$, where $P_C=(C\hookrightarrow E_j)_*A_C$ and $L_j=A_{E_j}(j-1)[2j-2]$.
Thus $Q_j=R_j\cup\beta_{j,j}$. We will prove $Q_j=\Theta_j$ by induction, with both sides
interpreted as morphisms on the same $E_j$. Uses: def-pur-supported-cup,
lem-pur-supported-cup-functoriality, lem-pur-supported-hom, lem-pur-flag-localized-product.

3. Fix $j\geq1$ and abbreviate $X=E_j$, $D=E_{j-1}$, $a=a_j$, $P_D=a_*A_D$. Let $u:X\setminus
D\hookrightarrow X$. On each affine chart $u$ is the principal open $D(x_j)$, hence is
quasi-compact. The functor $a^*$ is exact by [prop-weil-pbc-proetale-constant-exact]; $a_*$ is
exact, $a^*a_*\cong1$, and $u^*a_*=0$ by [lem-weil-pbc-proetale-ringed-open-closed]. Let
$$\rho_K:K\otimes_A^LP_D\longrightarrow a_*a^*K$$ be the symmetry-ordered projection mate
$\pi_{a;A_D,K}$ of [lem-weil-pbc-ringed-projection-mate-exact]. This is an isomorphism for the
objects used here. Indeed $P_D$ is flat by [def-pur-supported-cup], so the source is the termwise
tensor $K^t\otimes P_D$. Its restriction to $X\setminus D$ is zero. The unit $K^t\otimes P_D\to
a_*a^*(K^t\otimes P_D)$ is therefore an isomorphism by [lem-exc-proetale-closed-essential-image].
Identifying $a^*P_D=A_D$ gives the displayed target termwise. This unit composite is exactly
$\rho_K$: its adjunct is the tensor comparison followed by the closed counit $a^*P_D\to A_D$,
which is the defining adjunct of the projection mate. Exactness lets these termwise
identifications pass to derived categories. Uses: lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-ringed-projection-mate-exact, def-pur-supported-cup,
lem-exc-proetale-closed-essential-image, prop-weil-pbc-proetale-constant-exact.

4. For $C=C_j$, let $\mu:P_C\otimes_A^LP_D\xrightarrow{\sim}(z_j)_*A_S$ be the specified
multiplication isomorphism of [def-pur-supported-cup]. Its section formula is restriction to
$E_0=C\cap D$ followed by multiplication. The same formula is the projection mate on these
coefficients: its adjunct restricts the first factor to $D$ and multiplies by the second factor in
$A_D$. Applying $a^*$ and using $a^*a_*\cong1$ identifies $a^*P_C$ with $(z_{j-1})_*A_S$; the
resulting $\rho_{P_C}\mu^{-1}$ is the identity on $a_*(z_{j-1})_*A_S=(z_j)_*A_S$. This fixes the
supported-source comparison by its quotient generators, rather than by an unspecified isomorphism.
On $K=L_j$ the same projection formula is
$$\rho_{L_j}:L_j\otimes_A^LP_D\xrightarrow{\sim}a_*\bigl(A_D(j-1)[2j-2]\bigr).$$ It is the twist
comparison used in [lem-pur-flag-localized-product]: locally a twist is a free rank-one
degree-zero sheaf by [lem-pur-twist-sheaf-locally-free], and both maps send $l\otimes b$ to
$b\,a^*l$. Shifts use the projection mate's shift comparison; these degree-zero sheaf maps agree
on local generators and under change of basis, so sheaf gluing gives equality before shifting.
Uses: def-pur-supported-cup, lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-ringed-projection-mate-exact, lem-pur-flag-localized-product,
lem-pur-twist-sheaf-locally-free.

5. Naturality of the projection mate in $K$, applied to $\gamma_j:P_C\to L_j$, gives the typed
identity $$\rho_{L_j}(\gamma_j\otimes1_{P_D})\mu^{-1}=(a_j)_*(a_j^*\gamma_j):
(z_j)_*A_S\longrightarrow(a_j)_*a_j^*L_j.$$ Here the source comparison is exactly Step 4.
Functoriality of tensor [lem-weil-derived-tensor-functorial] factors $\gamma_j\otimes d_j$ as
$(1_{L_j}\otimes d_j)(\gamma_j\otimes1_{P_D})$. Consequently the defining tensor formula in
[def-pur-supported-cup] represents $Q_j=R_j\cup\beta_{j,j}$ by $$\sigma\,(1_{L_j}\otimes
d_j)\rho_{L_j}^{-1}(a_j)_*(a_j^*\gamma_j).$$ The map $\sigma$ is the specified shift comparison
followed by twist multiplication. By Step 4 the first three factors are precisely
$d_j(j-1)[2j-2]$. To order the factors as in that notation use tensor symmetry: its sign is
$(-1)^{(2j-2)2}=1$, and the shift comparisons are those of
[lem-pur-shifted-tensor-morphism-calculus]. We have therefore proved the actual nested-composition
formula $$[Q_j]=d_j(j-1)[2j-2]\circ(a_j)_*(a_j^*\gamma_j).$$ Uses:
lem-weil-pbc-ringed-projection-mate-exact, lem-weil-derived-tensor-functorial,
def-pur-supported-cup, lem-pur-shifted-tensor-morphism-calculus, lem-pur-flag-localized-product.

6. For $j=0$, $Q_0$ and $\Theta_0$ are both $\operatorname{id}_{A_S}$. Suppose
$[Q_{j-1}]=\Theta_{j-1}$ as morphisms on $E_{j-1}$. Pulling the tensor-morphism representative of
$R_j$ back along $a_j$ gives the representative of $a_j^*R_j=Q_{j-1}$: inverse image is exact by
[prop-weil-pbc-proetale-constant-exact] and commutes with tensor and shifts by
[lem-weil-pbc-ringed-projection-mate-exact], and the source multiplication comparison is the one
checked in Step 4. Equivalently this follows factor by factor from
[lem-pur-supported-cup-functoriality] and the explicit cup definition. Thus
$a_j^*\gamma_j=\Theta_{j-1}$, as an equality on $E_{j-1}$. Apply the exact functor $(a_j)_*$ to
this equality. Step 5 now gives $$[Q_j]=d_j(j-1)[2j-2]\circ(a_j)_*\Theta_{j-1}=\Theta_j,$$ where
the last equality is the recurrence in [lem-pur-flag-localized-product]. No equality is inferred
on $E_j$ merely from an equality after restriction to $E_{j-1}$: the specified pushforward and
then $d_j$ are applied to both sides. At $j=r$, $Q_r$ is the product of the negatives of the full
ambient coordinate boundaries. Bilinearity of the supported cup product gives
$Q_r=(-1)^r\,\partial\kappa(x_1)\cup\cdots\cup\partial\kappa(x_r)$; [lem-pur-supported-hom] gives
the asserted cohomology equality. Uses: def-pur-supported-cup,
lem-weil-pbc-ringed-projection-mate-exact, lem-pur-supported-cup-functoriality,
lem-pur-flag-localized-product, lem-pur-supported-hom, prop-weil-pbc-proetale-constant-exact.

7. For the frame interpretation, $E_r\to S$ is smooth of relative dimension $r$ by
[sbc-lem-affine-space-smooth], and $E_0=S\to S$ is smooth of relative dimension zero. These
schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] applied over the field $k$.
At $z\in E_0$ the successive coordinate quotients of $\mathcal O_{E_r,z}$ are the corresponding
local rings of the coordinate subspaces. Each coordinate lies in the maximal ideal and is a
nonzerodivisor, since the same is true in the polynomial ring before localization and after
quotienting by any preceding coordinates. Applying
[lem-weil-pbc-dimension-quotient-nonzerodivisor] at each quotient gives $\dim\mathcal
O_{E_r,z}=\dim\mathcal O_{S,z}+r$. Hence the pure-codimension hypothesis in [def-pur-frame-class]
holds. With its geometric rank parameter named $r$, independently of the coefficient index, the
ordered coordinate frame defines the product of the positive boundaries by that definition, so
$Q_r$ is $(-1)^r$ times that frame class. The empty frame for $r=0$ gives the identity, as does
the nested construction. Uses: sbc-lem-affine-space-smooth,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-dimension-quotient-nonzerodivisor,
def-pur-frame-class, lem-pur-flag-localized-product.

8. Let $S'\to S$ be a morphism as in the statement and $v:E'_r\to E_r$ its affine-space base
change. The coordinate divisor $D_{r,l}$ pulls back to $D'_{r,l}$, again Cartier. By
[lem-amb-cartier-kummer-map] and [lem-pur-cartier-class-agreement], $v^*\beta_{r,l}=\beta'_{r,l}$.
The pullback and cup identities of [lem-pur-supported-cup-functoriality] give $v^*Q_r=Q'_r$. Apply
the already established equality both over $S$ and over $S'$ to obtain
$v^*\Theta_r=v^*Q_r=Q'_r=\Theta'_r$ under the same supported-source and twist comparisons. This
proves restriction compatibility without assuming that restriction from a closed subspace detects
a morphism. Uses: lem-amb-cartier-kummer-map, lem-pur-cartier-class-agreement,
lem-pur-supported-cup-functoriality.

The displayed equality is stated in the supported-Hom model of
lem-pur-supported-hom. The right side is frameBoundaryProduct, hence is exactly
the ordered coordinate frame class; the corrected divisor local equation contributes
one minus sign for each of the r Cartier factors. Thus the comparison has the scalar
factor (-1)^r. flagCoordinateSmoothPair records its geometric hypotheses without
identifying the rank with P.level. The two final HEq clauses express identity after
the canonical rank-zero source and zero-shift identifications. -/
theorem flag_local_comparison (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS] :
    (∀ r : ℕ, P.flagCoordinateTheta aS r = ((-1 : ℤ) ^ r) • P.flagCoordinateCup aS r) ∧
      (∀ (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
        [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
        (f : T ⟶ S) (_hf : f ≫ aS = aT) (r : ℕ),
        P.functorialCupPullback true (flagCoordinateZero S r) (flagCoordinateZero T r)
          (AffineSpace.map (ULift.{u} (Fin r)) f) f (flagCoordinateBaseChange f r)
          (flagCoordinateSpace S r ↘ S ≫ aS) (2 * (r : ℤ)) (r : ℤ)
          (P.flagCoordinateTheta aS r) = P.flagCoordinateTheta aT r ∧
        P.functorialCupPullback true (flagCoordinateZero S r) (flagCoordinateZero T r)
          (AffineSpace.map (ULift.{u} (Fin r)) f) f (flagCoordinateBaseChange f r)
          (flagCoordinateSpace S r ↘ S ≫ aS) (2 * (r : ℤ)) (r : ℤ)
          (P.flagCoordinateCup aS r) = P.flagCoordinateCup aT r) ∧
      HEq (P.flagCoordinateTheta aS 0)
        (localizedFlagInitialModel (cupCoefficientRestriction P (flagCoordinateZero S 0))
          (P.flagCoordinateEmptyProRestriction S)) ∧
      HEq (P.flagCoordinateCup aS 0)
        (localizedFlagInitialModel (cupCoefficientRestriction P (flagCoordinateZero S 0))
          (P.flagCoordinateEmptyProRestriction S)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
