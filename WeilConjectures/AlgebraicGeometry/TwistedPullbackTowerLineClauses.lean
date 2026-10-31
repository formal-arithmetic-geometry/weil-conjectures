/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackTowerDomainDefinitions

/-! # Signed Tate-line and ordered tensor clauses

The following declaration isolates a proper subset of the five bounds clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

/-- Signed Tate-line constructibility and ordered tensor bounds.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2).
(blueprint: lem-stage3-twisted-pullback-line-clauses).

Proof:

Apply [lem-stage3-twisted-pullback-pullback-clause] to obtain the uniform bounds on B. These
are used only in the final tensor-interval argument.

For any finite derived object with Tor interval [c,e], apply its Tor-amplitude condition to the
degree-zero coefficient unit. The derived tensor right unitor identifies this tensor test with
the original object. Hence its cohomology vanishes outside [c,e]. Transport this vanishing
through homology isomorphisms whenever an evaluation comparison is used.

By [lem-pur-twist-sheaf-locally-free](3), the reduction of the integral degree-one Tate line to
$A_{E,e(n+1)}$ is locally free of rank one and finite locally constant. This is precisely
$L_{n,1}$: [def-sp-ell-twist-quotient-data] uses the ordinary scalar extension to the same
$\ell$-power quotient. A local basis $t$ of that line gives the basis $t^{\otimes r}$ of its
$r$-th nonnegative tensor power, whose local coefficient module is $R_n$ and hence finite. The
defining recursion for signed powers [def-coefficient-twists-detailed] therefore proves local
rank one and finite local constancy for every $L_{n,r}$. In particular the one stratum $X$
witnesses intrinsic constructibility [def-weil-proetale-constructible-sheaf]; restriction to
each quasi-compact open has the same locally constant finite model. At $r=0$ the definition is
the coefficient unit, yielding the required isomorphism. Tensor with a locally free line is
exact: on its trivializing cover it is tensor with $R_{n,X}$, namely the identity, and
exactness of a sequence of sheaves is local. Thus each $L_{n,r}$ is flat.

The coefficient unit in degree zero has Tor interval $[0,0]$, since tensoring it with a degree-
zero test module returns that module by the finite derived unitor. The flat degree-one line has
the same Tor interval: [lem-pur-flat-single-derived-normalization] identifies tensor with
$L_{n,1}[0]$ with exact termwise tensor. For any test sheaf $M$, its value on $M[0]$ is
$(M\otimes L_{n,1})[0]$; the finite derived symmetry in [lem-sf-ringed-derived-closed-
symmetric-monoidal] gives the other order. The cochain shift comparisons of [lem-weil-pbc-
total-tensor-integer-shifts] identify $(L_{n,1}[2])\otimes^L M[0]$ with $(L_{n,1}[0]\otimes^L
M[0])[2]$. Its sole possible cohomology degree is $-2$, because $\mathcal H^i(C[2])=\mathcal
H^{i+2}(C)$ [def-weil-abstract-derived-category]. Consequently $L_{n,1}[2]$ is bounded
constructible with Tor interval $[-2,-2]$, using the local-freeness argument for its one
cohomology sheaf. This is a calculation in the finite constant-ring category; small skeletons
may be taken in the module universe [def-weil-size-convention].

Fix $n$ and induct on $r$ to prove that the actual finite evaluation $(O_r)_n$ is bounded
constructible finite-Tor of Tor amplitude $[-2r,-2r]$. At $r=0$, evaluation of the coefficient
unit is $R_{n,X}[0]$, a finite locally constant sheaf (hence constructible by the one-stratum
definition of the local-freeness argument), so the shifted-line calculation proves the claim.
In the successor, [lem-coef-semilinear-derived-sections] evaluates the defining ordered tensor
to $(O_r)_n\otimes^L L_{n,1}[2]$, using the level isomorphism of the given datum $w$ [def-sp-
chart-tate-tower-data] and evaluation's shift comparison. The induction hypothesis and the
shifted-line calculation satisfy both finite-Tor hypotheses of [lem-sf-tensor-ctf](ii). Its sum
interval is $[-2r-2,-2r-2]=[-2(r+1),-2(r+1)]$, and it also supplies bounded constructibility.
The unit test of paragraph two supplies the same cohomological interval. Taking $r=d$ for every
$n$ proves conclusion 4 with bounds independent of $n$. The induction is on the literal ordered
tensor, not on an orientation or a comparison to an exceptional image.

For each $n$, evaluate $P=B\otimes_b^L O_d$ using [lem-coef-semilinear-derived-sections]. The
pullback clause and ordered-line induction give its factors bounded constructible finite-Tor
with intervals $[a,z]$ and $[-2d,-2d]$. Apply [lem-sf-tensor-ctf](ii) to these factors to
obtain bounded constructibility and the sum Tor interval $[a-2d,z-2d]$. The unit test gives the
same cohomological interval. For the last conclusion apply that same theorem with first factor
$(O_d)_n$ and second factor $B_n$; both hypotheses still hold, and its interval $[-2d+a,-2d+z]$
is the required one. Thus no braiding on the abstract tower tensor is used. The predicates in
[def-sp-chart-tate-tower-data] are precisely these three levelwise assertions, so the uniform
intervals give conclusions 3 and 5 and finish the conjunction. No reduction-isomorphism
hypothesis on $K$ or compatibility between independent finite tests has been used. -/
theorem twisted_pullback_line_clauses
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X Y : Over (Spec (CommRingCat.of D.k))) [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    [IsSeparated f.left] (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (w : SpChartAdmissibility.Twists l E X.left)
    (K : SpTowerCalculus.C l E b q Y.left) (a z : ℤ) (haz : a ≤ z)
    (hTor : ∀ n : ℕ, HasProEtaleTorAmplitude Y.left (SpTowerShriek.R l E n)
      ((SpTowerShriek.Ev l E Y.left n).obj
        ((SpTowerGamma.realization l E b q Y.left).obj K)) a z) :
    (∀ n : ℕ,
      IsConstructibleProEtaleModuleSheaf X.left (SpTowerShriek.R l E n)
        (spEllTwistLine l E X.left n (d : ℤ)) ∧
      (spEllTwistLine l E X.left n (d : ℤ)).IsFiniteLocallyFreeOfRank 1 ∧
      (d = 0 → Nonempty (spEllTwistLine l E X.left n (d : ℤ) ≅
        SheafOfModules.unit ((sheafCompose (ProEt.topology X.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (SpTowerShriek.B l E X.left n))))) ∧
    SpChartAdmissibility.bounds l E X.left (P l E b o q f.left w d K)
      (a - 2 * d) (z - 2 * d) (a - 2 * d) (z - 2 * d) ∧
    SpChartAdmissibility.bounds l E X.left (SpTowerGamma.orderedLine l E b X.left w d)
      (-2 * d) (-2 * d) (-2 * d) (-2 * d) ∧
    SpChartAdmissibility.bounds l E X.left
      ((SpTowerShriek.tensor l E b X.left).obj
        (SpTowerGamma.orderedLine l E b X.left w d, B l E b o q f.left K))
      (a - 2 * d) (z - 2 * d) (a - 2 * d) (z - 2 * d) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTwistedTowerDomain
