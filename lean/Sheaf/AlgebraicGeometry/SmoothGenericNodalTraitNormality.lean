/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings
public import Sheaf.AlgebraicGeometry.PureDimension
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.SerreCriterionNormal
import WeilConjectures.RingTheory.SerreCriterionReduced
import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.SerreConditions

/-! # Normality of a nodal trait family with smooth generic fibre

Source: Stacks Project, curves.tex, Tag 0CBY; models.tex, Tags 0CDD and 0CDE;
algebra.tex, Tags 031R, 031S, 00ON and 0337; morphisms.tex, Tag 01UA
(blueprint: lem-sfb-smooth-generic-nodal-trait-normality).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat finitely presented nodal curve family over a DVR with smooth generic fibre
has integrally closed domain stalks and dense generic fibre. If the generic fibre is
integral, the total space is integral. Empty and disconnected fibres are allowed.

Source: Stacks Project, curves.tex, Tag 0CBY and models.tex, Tags 0CDD and 0CDE,
with algebra.tex, Tags 031R, 031S, 00ON, 0337 and morphisms.tex, Tag 01UA.
(blueprint: lem-sfb-smooth-generic-nodal-trait-normality).

Proof:
1. Apply [lem-sfb-nodal-trait-finite-singular-charts] with $R=A$: its flatness, finite
   presentation, smooth generic fibre and geometric nodal-fibre hypotheses are exactly ours,
   including empty or disconnected fibres. Thus $X$ is Noetherian and the nonsmooth locus $Z$ is
   a finite set of closed special-fibre points. Every point outside $Z$ has a regular total-
   space local ring, and every $z\in Z$ has $\dim\mathcal O_{X,z}=2$. Consequently every point
   with local dimension at most one lies outside $Z$ and is regular. We use the nonsmooth locus
   here, not the potentially smaller nonregular locus: a node with chart exponent $n=1$ can
   already be regular. These conclusions are clauses of the cited statement; no completion or
   excellence assertion is needed.
   Uses: lem-sfb-nodal-trait-finite-singular-charts.
2. The ordinary special fibre $X_k$ is reduced: apply [lem-trf-geometric-reducedness-algebraic-
   closure-test] to $X_k/k$, whose base change to an algebraic closure is reduced by hypothesis,
   and then take the identity field extension $k/k$. This includes the empty special fibre. By
   [def-pc-reduced-scheme], every local ring of $X_k$ is reduced.
   Uses: lem-trf-geometric-reducedness-algebraic-closure-test, def-pc-reduced-scheme.
3. Put $W=X\setminus Z$. It is locally Noetherian and all its local rings are regular by step 1;
   [def-weil-regular-scheme] therefore makes $W$ regular. At $x\in W$, choose a regular
   Noetherian affine neighbourhood $V=\operatorname{Spec}C\subset W$, as that definition
   permits. By [lem-weil-pbc-regular-ring-normal], $C$ is normal, so [lem-weil-pbc-serre-
   criterion-normal] gives $(S_2)$ for $C$. The identification $C_{\mathfrak p_x}\simeq\mathcal
   O_{X,x}$ of [lem-weil-pbc-affine-open-stalk-localization] transfers its depth bound:
   $\operatorname{depth}\mathcal O_{X,x}\ge\min(2,\dim\mathcal O_{X,x})$. Here the stalk is
   unchanged on the open neighbourhood $V$, directly from restriction of the structure sheaf.
   Uses: def-weil-regular-scheme, lem-weil-pbc-regular-ring-normal, lem-weil-pbc-serre-
   criterion-normal, lem-weil-pbc-affine-open-stalk-localization.
4. Fix $z\in Z$ and set $S=\mathcal O_{X,z}$ and $Q=S/\pi S$. Flatness [def-weil-flat-morphism]
   gives a flat local map $A\to S$; both rings are Noetherian. By [lem-sbc-scheme-fibre-stalk-
   quotient], $Q$ is the actual local ring of $X_k$ at $z$, so is reduced by step 2. Apply the
   local form of [lem-weil-pbc-flat-height-formula] to $A\to S$ at their maximal ideals. Since
   $\dim A=1$ [def-sc-discrete-valuation-ring] and $\dim S=2$ by step 1, it gives $\dim Q=1$. By
   [lem-weil-pbc-serre-criterion-reduced], the reduced Noetherian local ring $Q$ satisfies
   $(S_1)$ and hence has depth at least one. The uniformizer $\pi$ is a nonzerodivisor in the
   domain $A$ and $A/\pi A=k\ne0$, so it is a regular sequence of length one and
   $\operatorname{depth}A\ge1$ [def-weil-pbc-depth, def-weil-pbc-regular-sequence]. Now [lem-
   weil-pbc-flat-local-depth-formula] yields
   $\operatorname{depth}S=\operatorname{depth}A+\operatorname{depth}Q\ge2$. This treats every
   point not covered by step 3.
   Uses: def-weil-flat-morphism, lem-sbc-scheme-fibre-stalk-quotient, lem-weil-pbc-flat-height-
   formula, def-sc-discrete-valuation-ring, lem-weil-pbc-serre-criterion-reduced, def-weil-pbc-
   depth, def-weil-pbc-regular-sequence, lem-weil-pbc-flat-local-depth-formula.
5. Choose any affine open $U=\operatorname{Spec}B$ in a Noetherian affine cover of $X$. Under
   [lem-weil-pbc-affine-open-stalk-localization], all $B_{\mathfrak p}$ are the corresponding
   local rings of $X$. Step 1 makes them regular whenever $\dim B_{\mathfrak p}\le1$, and steps
   3--4 give their depth bounds $\operatorname{depth}B_{\mathfrak p}\ge\min(2,\dim B_{\mathfrak
   p})$. These are exactly $(R_1)$ and $(S_2)$ [def-weil-pbc-serre-conditions-rk-sk]. Apply
   [lem-weil-pbc-serre-criterion-normal] to the Noetherian ring $B$: every $B_{\mathfrak p}$ is
   an integrally closed domain. The affine cover and its stalk identifications prove the first
   conclusion for every point of $X$.
   Uses: lem-weil-pbc-affine-open-stalk-localization, def-weil-pbc-serre-conditions-rk-sk, lem-
   weil-pbc-serre-criterion-normal.
6. By [lem-weil-pbc-flat-lfp-open], $f$ is open. If $O\subset X$ is any nonempty open, then
   $f(O)$ is a nonempty open of $\operatorname{Spec}A$. Such an open contains its generic point:
   the only points of the spectrum of a DVR are $(0)$ and $(\pi)$, and every open containing
   $(\pi)$ contains $(0)$. Thus $O$ meets the generic fibre. Since
   $\operatorname{Spec}F=D(\pi)\subset\operatorname{Spec}A$, its inverse image is exactly the
   open subscheme $X_F$, and we have proved that $X_F$ is dense. If $X$ is empty the density
   assertion is immediate.
   Uses: lem-weil-pbc-flat-lfp-open, def-sc-discrete-valuation-ring.
7. Finally assume $X_F$ is integral. It is nonempty and irreducible by [def-pc-integral-scheme].
   For closed subsets $C,D\subset X$ with $X=C\cup D$, the intersections with $X_F$ give a
   closed cover of $X_F$, so irreducibility gives $X_F\subset C$ or $X_F\subset D$. Density from
   step 6 then gives $X=C$ or $X=D$, proving that $X$ is irreducible and nonempty. Every local
   ring of $X$ is a domain by step 5, hence reduced: a nilpotent element in a domain is zero.
   Thus $X$ is reduced [def-pc-reduced-scheme], and the equivalence in [def-pc-integral-scheme]
   proves that $X$ is integral. No connectedness or projectivity has entered the argument.
   Uses: def-pc-integral-scheme, def-pc-reduced-scheme.
-/
theorem normal_dense_integral_of_smooth_generic_nodal_trait
    (A : CommRingCat.{u}) [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]
    {X : Scheme.{u}} (f : X ⟶ Spec A)
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hgeneric : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A F)))))
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec A),
      IsReduced (pullback (C := Scheme) f g) ∧
        (pullback (C := Scheme) f g).IsPureDimension 1 ∧
        ∀ z : pullback (C := Scheme) f g,
          IsClosed ({z} : Set (pullback (C := Scheme) f g)) →
          ¬ ((NodalFiber.projection f Ω g).stalkMap z).hom.FormallySmooth →
          Nonempty (NodalFiber.completedLocalRing z ≃+* NodalFiber.powerSeriesQuotient Ω)) :
    (∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      DenseRange (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A F)))) ∧
      (IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A F)))) →
        IsIntegral X) := by
  sorry

end AlgebraicGeometry
