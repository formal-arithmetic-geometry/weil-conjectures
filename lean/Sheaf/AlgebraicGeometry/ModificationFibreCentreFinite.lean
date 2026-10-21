/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.ModificationFibreValuationSets
public import Sheaf.TraceFormula.ValuationHorizontalCurveModels
public import Sheaf.TraceFormula.Modification
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import Mathlib.RingTheory.Valuation.LocalSubring
import Sheaf.AlgebraicGeometry.BirationalRiemannZariskiNeighbourhoods
import Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization
import Sheaf.TraceFormula.FlatFibreGenericGeneralization
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.TraceFormula.FlatFibreComponentClosureDimension
import Sheaf.RingTheory.ValuationDomainFibreDimensions
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Finite closed-centre fibre valuations of modifications

Source: Temkin, Stable modification of relative curves, §4.2, Lemmas 4.2.1(ii) and
4.2.2, pp. 26--27; §4.1 for finite normalization
(blueprint: lem-trf-modification-fibre-centre-finite).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RiemannZariski

/-- The Gamma-zero finiteness, residual degree, generalization formula, centre correspondence
and quasi-finite modification locus for a normal relative curve over a finite-height valuation
base. Source: Temkin §4.2, Lemmas 4.2.1(ii) and 4.2.2, pp. 26--27, with the reduced-source
extension by finite normalization in §4.1
(blueprint: lem-trf-modification-fibre-centre-finite).

Proof following the eleven steps of the node:
1. Apply [lem-trf-valuation-horizontal-curve-models] with empty marking. Thus $Y$ is a flat
finitely presented $T$-curve of pure relative dimension one, and $q_\eta$ is an isomorphism. Work
on one component of $C$. Its finitely many components are disjoint and open: on an affine
neighbourhood of an intersection two distinct minimal primes would survive in the local ring,
contrary to its being a domain. A finite disjoint closed decomposition is open. The inverse image
in $Y$ is integral: its reduced dense open is integral, so its closure is the whole space and the
reduced space is irreducible. At the end take the finite disjoint union. By
[lem-weil-pbc-finite-type-over-noetherian] and [lem-sc-locnoeth-components-locally-finite], each
fibre of any of these curves has finitely many components: the fibre is quasi-compact and
Noetherian, and a finite subcover of the locally finite component neighbourhoods meets all
components.
2. For any reduced modification $h:X\to C$ and a fibre-generic $c\in C_t$, every point $x\in
h^{-1}(c)$ is fibre-generic in $X_t$. Indeed [lem-sc-closed-irreducible-dimension-trdeg]
identifies the residue transcendence degrees over $\kappa(t)$ of $c$ and of a fibre-generic point
with $1$; all points of a pure one-dimensional finite-type fibre have transcendence degree at
most $1$, since their closures lie in a one-dimensional component. The embedding
$\kappa(c)\hookrightarrow\kappa(x)$ and [lem-kun-transcendence-degree-tower] force the latter
degree to be $1$. The closure of $x$ therefore has dimension $1$ and must be a whole component.
Hence $h^{-1}(c)$ is finite. By [lem-trf-proper-finite-fibre-finite-near], $h$ is finite over a
neighbourhood of $c$; shrink to an affine open of the integral normal $C$. The restriction
remains integral and birational, so [lem-trf-finite-birational-normal-iso] makes it an
isomorphism.
3. Let $Z\subseteq C$ be the reduced closed complement of the largest isomorphism open of $q$.
Step 2 shows that $Z_t$ contains no generic point of any component of $C_t$. Since $C_t$ is a
Noetherian pure curve, a proper closed subset of each of its finitely many one-dimensional
components has dimension at most zero (a positive chain could otherwise be extended by that
component to a chain of length at least two). Thus every nonempty $Z_t$ has dimension zero. The
closed subscheme $Z$ is of finite type over $T$, because its affine rings are quotients of those
of $C$. Now [lem-trf-locally-quasi-finite-relative-dimension-zero] makes $Z\to T$ locally
quasi-finite; finite type and the zero-dimensional finite-type fibres give quasi-finiteness in
[pqf-def-quasifinite].
4. Let $X$ now be any normal curve occurring as a modification, and let $x\in X$ be
fibre-generic. A valuation ring $O$ of its component function field $L$ dominating $\mathcal
O_{X,x}$ exists by [lemma-nagata-local-domain-valuation-dominates], and gives a centred
valuation. Step 2, with $X$ as normal target, says that every integral proper birational model
$X^{\prime}\to X$ is an isomorphism near $x$. Its centre $x^{\prime}$ therefore has local ring
exactly $\mathcal O_{X,x}\subseteq L$. Apply
[lem-trf-birational-riemann-zariski-neighbourhoods](iii): every $a\in O$ belongs to an affine
neighbourhood ring of such a centre, hence belongs to $\mathcal
O_{X^{\prime},x^{\prime}}=\mathcal O_{X,x}$. The reverse inclusion is domination. Thus
$O=\mathcal O_{X,x}$, and this proves both existence and uniqueness of a centred valuation above
every fibre-generic point of a normal modification.
5. For this unique valuation ring $O=\mathcal O_{X,x}$, put $t=f(x)$ and $\mathfrak p\subset V$
its corresponding prime. The local structural map $V_{\mathfrak p}\to\mathcal O_{X,x}$ has
maximal-ideal contraction $\mathfrak pV_{\mathfrak p}$. In fact $O\cap K=V_{\mathfrak p}$: if
$a\in K\setminus V_{\mathfrak p}$, the valuation property of $V_{\mathfrak p}$ gives
$a^{-1}\in\mathfrak pV_{\mathfrak p}$, so $a^{-1}$ is a nonunit of $O$ and $a\notin O$.
Consequently $\kappa(O\cap K)=\kappa(t)$ and $\kappa(O)=\kappa(x)$. By
[lem-sc-closed-irreducible-dimension-trdeg] the latter has transcendence degree one over
$\kappa(t)$. This proves the residue assertion for every normal modification, including $C$.
6. Normalize the integral $Y$ by [lem-trf-valuation-curve-finite-normalization], obtaining a
finite surjective $n:M\to Y$ with $M$ a normal $T$-curve and with the same generic fibre. The
composite $M\to C$ is proper by [lem-weil-pbc-finite-proper] and
[lem-weil-pbc-proper-fp-permanence], and is a modification. The proper lifts of each centred
valuation through $Y$ and $M$ agree by uniqueness in
[lem-trf-birational-riemann-zariski-neighbourhoods]. A point $m$ and its image $y$ have a finite
residue-field extension: on a fibre of a finite map the coordinate algebra is finite-dimensional
over $\kappa(y)$, and its residue fields are finite-dimensional quotients. Thus
[lem-kun-transcendence-degree-tower] and [lem-sc-closed-irreducible-dimension-trdeg] show that
$m$ is fibre-generic exactly when $y$ is. Hence $\Gamma(M)=\Gamma(Y)$ and
$\Gamma_0(M)=\Gamma_0(Y)$. Steps 4--5 for $M$ give the residual transcendence degree assertion
for $Y$. For every fibre-generic $y\in Y$, choose a point of its nonempty finite inverse image in
$M$ and use step 4; this also proves the asserted surjectivity of centres for reduced $Y$.
7. There are finitely many $t\in T$, and each $M_t$ has finitely many components by step 1. Step
4 bijects their generic points with $\Gamma(M)$. It follows that $\Gamma(M)$, and therefore its
subset $\Gamma_0(M)=\Gamma_0(Y)$, is finite. By [lem-trf-flat-fibre-generic-generalization] the
fibre-generic locus of $M$ is stable under generalization. Its inverse image under the continuous
centre map is $\Gamma(M)=\Gamma(Y)$, so this set is also stable under generalization. Step 2
gives $\Gamma(C)\subseteq\Gamma(Y)$, since every valuation with fibre-generic centre on $C$ lifts
through an isomorphism neighbourhood. Therefore
$\operatorname{gen}(\Gamma_0(Y))\cup\Gamma(C)\subseteq\Gamma(Y)$.
8. For the converse let $\nu\in\Gamma(Y)\setminus\Gamma(C)$, with centre $x\in M_t$, and put $c=q
n(x)$. Then $c$ is closed in $C_t$: otherwise it would be a generic point of the pure curve, by
[lem-kun-closed-point-field] and [lem-sc-closed-irreducible-dimension-trdeg]. Let
$H=\overline{\{x\}}\subseteq M$ and $B=\overline{\{c\}}\subseteq C$, with reduced
closed-subscheme structures. The closed map $qn$ gives $(qn)(H)=B$: continuity gives containment
in $B$, and closedness gives the reverse containment. By
[lem-trf-flat-fibre-component-closure-dimension], every nonempty fibre of $H$ is pure of
dimension one.
9. Every nonempty fibre of $B$ has dimension zero. To check this at $s$ in its image, use an
affine open $W\subseteq C$ meeting $B_s$. It contains $c$, since $c$ is the generic point of $B$.
If $\mathfrak p\subset V$ is the prime of $t$, the domain $D=\Gamma(B\cap W,\mathcal O_B)$ is a
finite-type algebra containing $V/\mathfrak p$, and its generic fibre over this valuation domain
is the single point $c$ with field $\kappa(c)$, finite over $\kappa(t)$ by
[lem-kun-closed-point-field]. Localize $V/\mathfrak p$ at the prime of $s$. Apply
[lem-trf-valuation-domain-fibre-dimensions] to the resulting finite-type domain: its generic
fibre has dimension zero, so its nonempty closed fibre does too. These affine opens cover $B_s$.
This applies the existing dimension theorem to a quotient and a localization of the valuation
ring; no Noetherian assumption on $V$ is used.
10. Choose the most specialized point $s$ in the nonempty image of $H\to T$; it exists because
$T$ is a finite chain. Its inverse image $H_s$ is closed in $H$: the inverse image of
$\overline{\{s\}}$ equals $H_s$ because no stricter specialization occurs in that image. Pick a
component $D$ of $H_s$ with generic point $y$. Step 8 gives $\dim D=1$. Since $D$ is a closed
irreducible subset of the pure curve $M_s$, it is also a component of $M_s$. Step 9 says that the
image of this irreducible $D$ in $B_s$ is a single point, as a zero-dimensional Noetherian space
has only singleton irreducible subsets. Moreover $D$ is closed in $M$, and $qn$ is closed, so
this image point is closed in all of $C$. Step 4 now gives a valuation $\mu=\mathcal O_{M,y}$ in
$\Gamma_0(Y)$.
11. The point $x$ generalizes $y$ in $M$, and the two corresponding valuation rings satisfy
$\mathcal O_{M,y}\subseteq\mathcal O_{M,x}$; the latter is the localization of the former at the
prime corresponding to $x$. The map $\operatorname{Spec}\mathcal O_{M,y}\to M$ therefore
restricts on this localization to the centred map for $\nu$. Lift it to any proper birational
model over $C$ using [lem-trf-birational-riemann-zariski-neighbourhoods]. Its restriction is the
unique lift of $\nu$, while its closed point is the centre of $\mu$. Continuity makes the former
centre a generalization of the latter on every model. Since inverse images of opens under these
centre maps generate the topology, every neighbourhood of $\mu$ contains $\nu$. Thus
$\nu\in\operatorname{gen}(\Gamma_0(Y))$. Together with step 7 this proves the stated equality.
The finite disjoint component reduction of step 1 preserves every set and specialization relation
used above, completing all clauses.
-/
theorem modification_fibre_centre_finite (B : HorizontalValuationBase.{u})
    {C Y : Scheme.{u}} (c : C ⟶ B.T) (hcurve : RelativeCurve c)
    (hnormal : ∀ x : C, IsDomain (C.presheaf.stalk x) ∧
      IsIntegrallyClosed (C.presheaf.stalk x))
    (hsmooth : Smooth (pullback.snd c B.genericMap))
    (hcomponents : (irreducibleComponents C).Finite)
    (q : Y ⟶ C) (hq : SchemeModification q) (hY : IsReduced Y) :
    (modificationGammaZero c q).Finite ∧
    (∀ ν ∈ modificationGamma c q,
      @Algebra.trdeg
        (B.T.residueField ((ν.2.centre ≫ c) (IsLocalRing.closedPoint ν.2.V)))
        ((Spec (.of ν.2.V)).residueField (IsLocalRing.closedPoint ν.2.V)) _ _
        ((ν.2.centre ≫ c).residueFieldMap (IsLocalRing.closedPoint ν.2.V)).hom.toAlgebra = 1) ∧
    modificationGamma c q =
      {ν | ∃ μ ∈ modificationGammaZero c q,
        μ ∈ @closure (ComponentValuationSpace C) (componentValuationTopology C) {ν}} ∪
          modificationGamma c (𝟙 C) ∧
    (∀ ν ∈ modificationGamma c q, ∀ μ : ComponentValuationSpace C,
      ν ∈ @closure (ComponentValuationSpace C) (componentValuationTopology C) {μ} →
        μ ∈ modificationGamma c q) ∧
    (∀ (s : B.T) (z : (q ≫ c).fiber s), z ∈ genericPoints ((q ≫ c).fiber s) →
      ∃ (ν : ComponentValuationSpace C) (l : Spec (.of ν.2.V) ⟶ Y),
        l ≫ q = ν.2.centre ∧ (q ≫ c).fiberι s z = l (IsLocalRing.closedPoint ν.2.V)) ∧
    ((∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y.presheaf.stalk y)) →
      ∀ (s : B.T) (z : (q ≫ c).fiber s), z ∈ genericPoints ((q ≫ c).fiber s) →
        ∃! ν : ComponentValuationSpace C, ∃ l : Spec (.of ν.2.V) ⟶ Y,
          l ≫ q = ν.2.centre ∧ (q ≫ c).fiberι s z = l (IsLocalRing.closedPoint ν.2.V)) ∧
    Scheme.Hom.IsQuasiFinite ((modificationLocusIdeal q).subschemeι ≫ c) := by
  sorry

end AlgebraicGeometry.RiemannZariski
