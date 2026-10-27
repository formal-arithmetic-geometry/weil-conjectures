/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.RingTheory.RegularRingNormal
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing

/-! # Local properties of a smooth relative curve over a trait

Source: Stacks Project, Algebra, Tags 07NF, 00ON and 0AFS; Morphisms, Tags 01V5 and 02H6.
(blueprint: lem-sfb-smooth-trait-curve-local-properties).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth pure relative curve over a DVR has regular normal stalks of dimension at most two,
with dimension two at closed special-fibre points and the base-plus-fibre dimension formula.
`IsRegularScheme X` includes local Noetherianity and regularity of every stalk. The residue
field and fraction field in the source are the canonical ones; the special fibre is the fibre
at `IsLocalRing.closedPoint R`. The fibre condition permits empty fibres.

Source: Stacks Project, Algebra, Tags 00PD, 0AFS, 07NF, 0567, 00ON, 00P1, 00OU;
Schemes, Tags 0HA1, 01I4, 01JQ; Varieties, Tag 0A21; Morphisms, Tags 01V5, 02H6.
(blueprint: lem-sfb-smooth-trait-curve-local-properties)

Proof plan from the reviewed DAG:

1. Every ideal of $R$ is principal, hence finitely generated, so $R$ is Noetherian. By
   [lem-sc-dvr-dimension-one], $\dim R=1$. Its maximal ideal is $(\pi)$, so the definition of
   regular local ring makes $R$ regular local. By [lem-weil-pbc-regular-local-localization], $R$
   is a regular ring. Its primes are exactly $(0)$ and $(\pi)$: a nonzero prime strictly below the
   maximal ideal would give a chain of length two. Thus every nonempty open of
   $\operatorname{Spec}R$ is either the whole spectrum or its generic point
   $\operatorname{Spec}K$; an open containing the closed point contains a basic open $D(a)$ with
   $a$ a unit. The coordinate rings of these two opens are regular: $R$ as above and the field $K$
   by the dimension-zero definition.

2. By [lem-pc-smooth-flat], $f$ is flat and locally of finite presentation. Use the affine-local
   smooth-ring-map convention explicitly included in [def-sbc-smooth-morphisms]: around every $x$
   choose $U=\operatorname{Spec}B$ mapping into an affine open $V=\operatorname{Spec}A$ of the
   base with $A\to B$ smooth. Step 1 makes $A$ regular, so
   [lem-weil-pbc-regular-ring-smooth-ascent] makes $B$ regular, in particular Noetherian. These
   $U$ cover $X$, proving local Noetherianity and regularity by [def-weil-regular-scheme] and
   [pqf-def-locnoeth]. This also supplies finite-presentation affine charts whenever they are used
   below.

3. For a point $x$ in one of these $U$, let $\mathfrak q$ be its prime of $B$. The affine-stalk
   isomorphism [lem-weil-pbc-affine-open-stalk-localization] identifies $\mathcal O_{X,x}$ with
   $B_{\mathfrak q}$. This is regular local by regularity of $B$. By
   [lem-weil-pbc-regular-ring-normal], $B$ is normal, which means precisely that each
   $B_{\mathfrak q}$ is an integrally closed domain [def-weil-pbc-normal-ring]. This proves both
   stalk assertions without claiming that a disconnected $X$ is integral.

4. Fix $x$ over $s$, and write $A=R_s$, $T=\mathcal O_{X,x}$. Both are Noetherian local rings by
   Steps 1--3. The map $A\to T$ is local and flat by [def-weil-flat-morphism]. Apply the
   local-ring form of [lem-weil-pbc-flat-height-formula] at their maximal ideals: since
   localization of a local ring at its maximal ideal is itself, it gives $\dim T=\dim
   A+\dim(T/\mathfrak m_AT)$. By [lem-sbc-scheme-fibre-stalk-quotient], the last quotient is
   canonically $\mathcal O_{X_s,x}$. This proves the claimed equality for every point, not just
   closed points.

5. Each fibre is locally of finite type over $\kappa(s)$. Indeed, in a finite-presentation chart
   $A_0\to B=A_0[t_1,\ldots,t_n]/(g_1,\ldots,g_m)$ from Step 2, the fibre chart is
   $\operatorname{Spec}C$ with $C=B\otimes_{A_0}\kappa(s)=\kappa(s)[t_1,\ldots,t_n]/(\bar
   g_1,\ldots,\bar g_m)$ by [lem-weil-pbc-fibre-product-affine-spectra]. Here
   $\operatorname{Spec}\kappa(s)\to\operatorname{Spec}R$ factors through the open
   $V=\operatorname{Spec}A_0$ containing $s$, and by [lem-weil-pbc-open-preimage-fibre-product]
   (applied to the first projection $X_s\to X$ and the open $U=\operatorname{Spec}B$, and to $U\to
   V$) together with the pasting of fibre-product squares, the preimage of $U$ in
   $X_s=X\times_{\operatorname{Spec}R}\operatorname{Spec}\kappa(s)$ [def-pc-scheme-fibre] is the
   open subscheme $U\times_V\operatorname{Spec}\kappa(s)\cong\operatorname{Spec}C$. As the $U$
   cover $X$, these affine opens cover the fibre. Since this nonempty fibre is pure of dimension
   one by hypothesis, apply [lem-sbc-equidimensional-open-local-dimension] with $Y=X_s$, $O=Y$,
   $n=1$: its local topological dimension is one at every point. On a fibre chart containing $x$,
   [lem-weil-pbc-dimension-at-point-local-ring-trdeg] and
   [lem-weil-pbc-affine-open-stalk-localization] give $1=\dim\mathcal
   O_{X_s,x}+\operatorname{trdeg}_{\kappa(s)}\kappa(x)$. Nonnegativity of transcendence degree
   therefore gives $\dim\mathcal O_{X_s,x}\le1$. Local topological dimension is unchanged by
   taking an open neighbourhood, directly from its neighbourhood definition.

6. If $x$ is closed in $X_s$, it is closed in each affine fibre chart containing it, so its prime
   in that finite-type $\kappa(s)$-algebra is maximal. By
   [lem-weil-pbc-closed-point-dimension-local-ring], the local-ring dimension equals the local
   topological dimension, already one in Step 5. Step 1 gives $\dim R_s=0$ at the generic point (a
   field) and $\dim R_s=1$ at the closed point. Combining these values with Steps 4--5 bounds
   every $\dim\mathcal O_{X,x}$ by two. At a closed point of the special fibre, Step 4 gives
   exactly $1+1=2$. At a closed point of the generic fibre, its fibre local-ring dimension is one,
   as asserted.

7. All arguments are on neighbourhoods of a specified point. If $X$ or a fibre is empty, it has no
   such points and the corresponding universal assertions are vacuous. Neither affine charts nor
   any ring lemma above assumes global quasi-compactness, separatedness, excellence, or perfection
   of the residue field.
-/
theorem smooth_trait_curve_local_properties
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (_hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (_hpure : ∀ s : Spec (.of R), (f.fiber s).IsPureDimension 1) :
    Flat f ∧ LocallyOfFinitePresentation f ∧ IsRegularScheme X ∧
      (∀ x : X, IsDomain (X.presheaf.stalk x) ∧
        IsIntegrallyClosed (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) ≤ 2) ∧
      (∀ z : f.fiber (IsLocalRing.closedPoint R), IsClosed ({z} : Set _) →
        ringKrullDim (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) z)) = 2) ∧
      (∀ (s : Spec (.of R)) (z : f.fiber s),
        ringKrullDim (X.presheaf.stalk (f.fiberι s z)) =
          ringKrullDim ((Spec (.of R)).presheaf.stalk s) +
            ringKrullDim ((f.fiber s).presheaf.stalk z) ∧
        ringKrullDim ((f.fiber s).presheaf.stalk z) ≤ 1 ∧
        (IsClosed ({z} : Set (f.fiber s)) →
          ringKrullDim ((f.fiber s).presheaf.stalk z) = 1)) := by
  sorry

end AlgebraicGeometry
