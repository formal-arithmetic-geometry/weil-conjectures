/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense

/-! # Graph-normalized calculus in fixed coefficient coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md,
Local pairs, Uniformity and Levels (blueprint: lem-sp-global-chart-fixed-calculus).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

/-- Existence of the calculus for the supplied section-normalized coordinates, with its
own etale comparison pinned to the actual derived graph-extension transformation.
The Tate family ranges over all schemes on which the integer l is invertible, independently
of the ground field. The former unrestricted statement is false in mixed characteristic.
Source: blueprint det-sp-tower-gluing, Local pairs, Uniformity and Levels
(blueprint: lem-sp-global-chart-fixed-calculus).

Proof plan (the accepted DAG proof, with its prerequisites):

1. Keep the supplied $b,o,q$ throughout. Choose $z$ by the attached finite_coordinates_exists
theorem and choose $g$ by the ordinary graph-coordinate lemma. All derived coordinate changes used
below are the specific graphForward, graphPullCoordinates, graphOpenCoordinates, graphDerivedSum and
graphSupportCoordinates of the gluing interface: their ordinary adjunction comparisons and
localization maps are definitions, not independently chosen isomorphisms. These choices require
neither OpenExchange nor Laws.
Uses: lem-sp-global-finite-coordinates, lem-sp-global-graph-coordinates,
def-sp-tower-gluing-interfaces.

2. For $K\in\mathcal C_T$, finite-ring constructible comparison gives an origin $L_n\in
D^b_c(T_{et},R_n)$ for each level $K_n$. Comparison preserves cohomological intervals and reflects
the finite Tor interval, so each $L_n$ is bounded constructible finite-Tor. No equation between
different origins is needed. Construct finiteData.evaluation by the explicit composite in
Evaluation.normalization: inverse target levelComparison, realization counit, the supplied
Fcomparison, and source levelComparison. Every factor is already an isomorphism for the given
$b,o,q$, and composing these factors proves the normalization equation by definition. Together with
the origins these are precisely FiniteNormalization. At level $n$, $R_n$ is finite by Base and is
killed by $\ell^{n+1}$, since that power lies in the quotient ideal.
Uses: lem-weil-pbc-finite-ring-constructible-derived-origin, lem-exc-comparison-tor-interval,
def-sp-coefficient-tower-shriek-interfaces, def-sp-tower-shriek-data.

3. Choose $h$ from fixed preservation, applied to the given $b,o,q$. Its assertion is simultaneous
for every compactification of every separated finite-type map in the standing class over $k$; its
cohomological and Tor bounds are uniform in the coefficient index. This gives the required
Preservation witness without replacing the chosen compact-support functors.
Uses: lem-sp-global-fixed-preservation.

4. For constructing composition, work first on $D_T^{lev}$, the full ambient subcategory whose
individual levels are bounded constructible finite-Tor, with no requirement of uniform intervals.
The origins from step 2 and the finite compact-support domain theorem, with $A=B=R_n$, show that
proper direct image and open extension preserve $D^{lev}$, using their trivial compactifications.
The middle scheme of any compactification is separated finite-type over $k$, since it is proper over
the target; the intermediate opens in compatible towers are again in this class. Thus all
intermediate inputs below satisfy the finite-domain hypotheses. At the end restrict to $\mathcal C$,
using $h$.
Uses: lem-sp-finite-compact-support-domains, lem-weil-pbc-finite-ring-constructible-derived-origin.

5. In graph coordinates, for $pk=ir$ form $W_S=W\times_T S$ with projections $b,q$ and clopen lift
$s=(k,r)$. Define $\pi_s$ by first-factor projection on the section decomposition of the
clopen-projector theorem. Let $\beta:p^*i_!\simeq b_!q^*$ be the cartesian open comparison whose
inverse is the open-adjunction transpose of the pullback compositor and open unit. Put
$a_Q=(b_!\pi_s q^*)\beta$, with the open/pullback compositors to $k_!r^*$. Each coefficient
transition preserves both components, zero and the open unit; hence these level formulas are
compatible system maps. Evaluation retains these formulas and compositors: the latter are the unique
open-adjunction transposes of the pullback composition maps. Apply clopen alpha-pasting for module
sheaves at each $C_n$; componentwise equality gives its vertical and horizontal equations on
ordinary systems. Identity squares have $s=1$ and identity projection. Exact-derived pasting carries
these equations to the derived categories. Take the proper-adjunction mate
$\gamma_Q=(Rp_*k_!\varepsilon_r)(Rp_*a_QRr_*)\eta_p$. Mate-pasting gives its two pasting laws and
identity law before evaluation. The system section theorem evaluates this specified mate to the
single-$C_n$ mate of the displayed clopen arrow. Apply that same theorem to constant strict towers
over $C_n$: their mate evaluates to this identical single-ring word. On the constant tower of a
level input from $D^{lev}$, the strict-tower proper/open theorem applies with $B=\Lambda_j=C_n\cong
R_n$ and the bounded etale origin of step 2 at every $j$. Its mate, hence the single-ring mate, is
invertible and has the stated finite normalization. Joint conservativity now makes $\gamma_Q$
invertible. Transport through $g,q$ with their fixed adjunction comparisons.
Uses: lem-cbc-proper-open-clopen-projector, lem-cbc-proper-open-alpha-pasting,
lem-sp-exact-derived-transformation-pasting, lem-weil-pbc-mate-pasting,
lem-coef-semilinear-derived-sections, lem-cbc-strict-tower-proper-open-calculus,
def-sp-tower-gluing-interfaces, lem-pur-site-restriction-module-adjunction-exact.

6. Every field under construction is indexed by supplied compactifications, not merely by maps: for
composition these are $c_f,c_g,c_{gf}$. Thus the compactification categories used in that field are
already nonempty. Apply compactifiable cofilteredness to them. Apply compatible-tower existence to
$c_g,c_{gf}$; this produces a compactification of $if$ over the ambient scheme of $c_g$, a binary
tower, and common refining towers. Compare its induced compactification of $f$ with $c_f$ by
cofilteredness. For three maps $X\xrightarrow fY\xrightarrow gZ\xrightarrow hW$, use the supplied
compactifications of $h,hg,hgf$: first build a tower for $(g,h)$, giving an ambient compactification
$\bar Y\to\bar Z$; build one for $(gf,h)$, giving an ambient compactification $\bar X_0\to\bar Z$;
then apply the same compatible-tower theorem to $X\to Y\hookrightarrow\bar Y$ over $\bar Z$, using
$Y\hookrightarrow\bar Y$ and $X\hookrightarrow\bar X_0$ as the two supplied compactifications.
Pulling back along the successive opens gives a three-map staircase. Binary common refining towers
and cofilteredness accommodate the other compactifications in the associativity field. These furnish
the geometric hypotheses of compactification coherence in each indexed diagram. No assertion of
compactifiability of an unprovided map, or separate compactification-existence theorem, is used.
Uses: lem-cbc-compactifiable-cofiltered, lem-cbc-compactifiable-compatible-tower,
lem-sp-compactification-refinement-coherence, def-sp-coefficient-tower-shriek-interfaces.

7. Apply compactification coherence on $D^{lev}$ with $P_p=Rp_{*,\bullet}$, $J_j=j_{!,\bullet}$ and
the specific mates of step 5. Proper compositors are adjunction conjugates of pullback composition;
open compositors are the ordinary adjunction-preserving ones, descended termwise. For a refinement
use $P_p\gamma_v$ followed by proper composition, and compare two compactifications through a common
refinement. For a binary tower use $P_qJ_iP_rJ_j\xrightarrow{P_q\gamma_QJ_j}P_qP_pJ_bJ_j\simeq
P_{qp}J_a$. Conjugate by the refinement comparisons for arbitrary input compactifications. These
explicit words, transported through $g,q$, define composition, refinement and identity isomorphisms
for the fixed functors.
Uses: lem-sp-compactification-refinement-coherence, lem-coef-semilinear-derived-sections,
lem-cbc-extension-zero-composition, lem-sp-exact-derived-transformation-pasting,
def-sp-coefficient-tower-shriek-interfaces.

8. The formal compactification theorem gives refinement identity and cocycle, independence of
common-refinement choices, compatibility with simultaneous refinements, staircase associativity and
both identity laws for these words. Adjacent realization units and counits cancel by the triangle
identities, so all are equations before finite evaluation. With $h$, restrict intermediate outputs
to $\mathcal C$; its inclusions are full, hence the same equations give the coherence fields on the
required subcategories.
Uses: lem-sp-compactification-refinement-coherence, def-sp-coefficient-tower-shriek-interfaces.

9. Evaluate the proper/open words of steps 5-8 with their ordinary adjunction comparisons. The
componentwise clopen formula and open-unit transposes of step 5, exact localization and the system
section theorem evaluate the units, counits and projections to the single-ring mate; the
strict-tower theorem identifies it on each bounded-below finite origin with the normalized finite
comparison, including refinements. The direct-image site comparison is the specified counit mate;
open site comparison respects open composition. Transpose the two direct-image composition words,
use the pullback site comparison's compatibility with composites, and cancel unit/counit pairs.
Mate-pasting identifies their site transports. The same calculation, with projection identity on the
graph and zero on its complement, identifies the proper/open cells. Substitute these cells into the
refinement and binary-tower words of step 7: their site transports are the normalized finite
refinement and composition words. The interface defines fixedRefinement by the unique preimage of
the normalized etale comparison under the finite-origin equivalence, and finiteCanonicalComposition
by conjugating the canonical compositor with these refinements, using the supplied
compactifications. The finite-origin theorem is an equivalence, hence fully faithful on bounded
constructible origins, and the finite-domain theorem keeps every intermediate input in that class.
These evaluated words are therefore exactly fixedRefinement and finiteCanonicalComposition for
finiteData from step 2. This proves the finite fields of CompositionCoherence from specified mate
words and the finite-origin equivalence; it never detects equality of tower maps from their levels.
Uses: lem-cbc-strict-tower-proper-open-calculus,
lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison,
lem-weil-pbc-comparison-pullback, lem-weil-pbc-mate-pasting,
def-sp-coefficient-tower-shriek-interfaces, lem-weil-pbc-finite-ring-constructible-derived-origin,
lem-sp-finite-compact-support-domains, lem-sp-exact-derived-transformation-pasting,
lem-coef-semilinear-derived-sections, lem-cbc-proper-open-clopen-projector.

10. For an etale $e:U\to T$, localization of the pro-etale site identifies the ordinary restriction
with geometric pullback. In graph coordinates form the sheafified sum $\Sigma_e M$ of the modules
$M_n(W,s)$ over lifts $s:W\to U$. A coefficient transition sends a lift summand to the same lift by
the transition of $M$. The localization adjunction on each component therefore gives an adjunction
on compatible systems: the unit inserts the structural-lift summand and the counit folds by
restriction. The sum-exact theorem makes the left adjoint additive and exact. Transport this
adjunction along $g$ and the specified graphPullCoordinates to the recorded ordinary pullback,
giving EtaleOperation.extension and ordinaryAdjunction. At each level use the same finite sum and
the adjunction-unique right comparison; the supplied push-evaluation pin, section-preserving $z$,
and normalized geometric adjunction comparisons identify it with finiteEtaleAdjunction, including
its units and counits. The ordinary horizontal unit normalization of Geometry makes these
comparisons commute with the semilinear transitions.
Uses: lem-weil-proetale-weakly-etale-localization, lem-pur-site-restriction-module-adjunction-exact,
lem-route-sum-exact, lem-coef-semilinear-derived-sections,
lem-sp-tower-geometry-adjunction-evaluation, def-sp-tower-shriek-data,
def-sp-tower-gluing-interfaces, def-sp-coefficient-tower-shriek-interfaces.

11. Apply that additive exact adjunction degreewise to unbounded complexes and homotopy categories,
then localize its unit and counit. Exactness preserves quasi-isomorphisms, and the termwise triangle
identities descend with the standard exact-composition comparisons. This supplies the specified
unbounded derived adjunction in EtaleOperation; its unit and counit are precisely the required
localized ordinary words. The exact-derived pasting theorem preserves all ordinary comparison
equations under this localization.
Uses: lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-exact-functor-derived-factorization,
lem-sp-exact-derived-transformation-pasting, def-sp-coefficient-tower-shriek-interfaces.

12. In graph coordinates use the unique ordinary transformation $\gamma_e:\Sigma_e\to
g_{c,*}i_{c,!}$ that equals the open unit on each clopen lift graph and zero on its complement.
Follow its degreewise descent by the total right-derived direct-image unit to obtain the actual
$\theta_c$ of the graph-comparison definition. Transport this particular map back using
graphDerivedSum and graphSupportCoordinates and then $q$; call the resulting natural transformation
$\Theta_c:e_{!,\bullet}\to F_c$. On homotopy representatives every factor is specified. Evaluation
leaves the graph and complement restrictions unchanged, so ordinary graph-map uniqueness identifies
the evaluated ordinary map with its single-ring version. The normalized derived adjunction
evaluation preserves the direct-image unit; localization uniqueness therefore gives
$e_n\Theta_c=\theta_{c,n}$ under the specified comparisons. This computes constructed maps, rather
than lifting a family of maps or detecting equality by evaluation. The precise coefficient
evaluation identity used here is [lem-sp-varying-ring-graph-summand], for the actual varying-ring
theta and its specified sum/open/proper evaluation transports, before applying the single-ring
etale-origin graph normalization.
Uses: lem-route-graph-map-exists-unique, def-sp-varying-ring-graph-comparison,
def-sp-tower-gluing-interfaces, lem-coef-semilinear-derived-sections,
lem-sp-tower-geometry-adjunction-evaluation, lem-weil-pbc-localization-universal-property,
lem-sp-varying-ring-graph-summand.

13. The canonical finite etale compact-support comparisons furnish a graph- and homotopy-normalized
datum by the model-identification theorem. For any finite bounded constructible finite-Tor input
choose an etale origin as in step 2; in particular do this for every level of $K\in\mathcal C_U$.
The finite-origin graph-normalization theorem identifies $\theta_{c,n}(K_n)$, after the specified
sum/site comparison, with $b_c(L_n)\nu_T^*(c_{e,c}^{-1}(L_n))$. Both factors are isomorphisms:
finite compact-support site comparison is invertible on bounded-below origins, and the
graph-normalized etale compact-support comparison is an isomorphism. Each $e_n\Theta_c(K)$ is
therefore invertible. Joint conservativity of system evaluation makes $\Theta_c(K)$ invertible.
Define the new etale_shriek to be $\Theta_c^{-1}$ on $\mathcal C_U$, for every $e,c$. This is a
choice of the explicit graph map's inverse, not a property claimed for the unspecified comparison of
another existential theorem.
Uses: lem-sp-etale-origin-graph-normalization, lem-sp-finite-compact-support-domains,
lem-asd-etale-compact-support-normalization, lem-coef-semilinear-derived-sections,
lem-sp-chart-normalized-model-identification.

14. On arbitrary single-level unbounded inputs, exact restriction and sum extension commute with
cohomology and preserve each cohomological interval. For Tor intervals choose K-flat
representatives. Ringed-localization total tensor gives $e_!P$ K-flat and $e_!P\otimes H\simeq
e_!(P\otimes e^*H)$, so a module-sheaf test $H$ gives the same Tor interval for $e_!K$. For
pullback, its K-flat representative remains K-flat. Given any module sheaf $G$ on $U$, projection
gives $e_!(e^*K\otimes^LG)\simeq K\otimes^Le_!G$. The right side has the prescribed interval; exact
sum extension reflects vanishing cohomology by the ringed-slice exactness-reflection theorem, hence
the left input has that interval. Thus both finite_etale_intervals fields hold against all
module-sheaf tests.
Uses: lem-pur-site-restriction-module-adjunction-exact, lem-sf-ringed-open-total-tensor-kflat,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-ringed-slice-extension-exactness,
lem-pc-kflat-resolution.

15. A finite bounded constructible finite-Tor input has an etale origin. Step 13 identifies its sum
extension with finite compact support, which preserves this domain; the etale chart-domain theorem
gives preservation by pullback as well. The same statements hold on the pro-etale site by the
constructible and Tor comparisons. This proves both finite_etale_constructible fields. Evaluate the
system functors of step 10 and apply these finite results and step 14 to the uniform intervals of a
tower. The output levels are constructible finite-Tor and have the same uniform intervals, proving
both etale_preserves fields.
Uses: lem-sp-finite-compact-support-domains, lem-sp-etale-ctf-chart-domain,
lem-weil-pbc-finite-ring-constructible-derived-origin, lem-exc-comparison-tor-interval,
def-sp-coefficient-tower-shriek-interfaces.

16. For an open $j$, each test object has at most one lift, so its sum/open comparison $\omega_j$
preserves the ordinary inclusion unit and evaluation counit. For the trivial compactification
$(j,1)$, the lift graph is the whole test object and $\Theta$ is the open-unit comparison. For
another compactification $a=(i,r)$ of $j$, the refinement square $ri=j1$ has clopen graph $(i,1)$.
Its proper/open mate, transposed on ordinary sections, is the open unit on that graph and zero off
it. Graph-map uniqueness identifies this with the ordinary graph map; degreewise localization and
the derived unit identify $\Theta$ with the same refinement mate. These identifications survive
$g,q$ because their comparisons preserve the ordinary adjunctions. Hence $\omega_j\sigma_{j,a}$,
where $\sigma=\Theta^{-1}$, is the refinement comparison from $a$ to the trivial compactification.
Use that trivial compactification in the binary word of step 7 for $(j,f)$. Its proper/open square
has identity proper side, so the mate is identity and the word reduces to the canonical open
compositor $\mu_{j,c}$. Refinement compatibility gives exactly
$\alpha_{f,j}=\mu_{j,c}F_c(\omega_j\sigma_{j,a})$, including realization counits. This proves
open_normalization for the newly chosen graph comparison before evaluation.
Uses: lem-weil-proetale-weakly-etale-localization, lem-sp-compactification-refinement-coherence,
lem-route-graph-map-exists-unique, lem-sp-exact-derived-transformation-pasting,
def-sp-coefficient-tower-shriek-interfaces, lem-cbc-proper-open-clopen-projector,
lem-weil-pbc-mate-pasting.

17. Apply reduction-transition compatibility to the given $b,o,q,z$ and finiteData from step 2. It
gives reduction_formula with the actual proper-counit/open-tensor coefficient comparison. For
reduction_comparison_isIso apply the finite reduction-direct-image theorem to $R_n\to R_m$ and the
bounded constructible finite-Tor level $K_n$; both finite rings are killed by powers of $\ell$, and
no flatness or finite projective dimension of $R_m/R_n$ is required.
Uses: lem-route-reduction-transition-compatibility, det-sp-reduction-direct-image,
def-sp-coefficient-tower-shriek-interfaces.

18. For the remaining reduction fields write $r_{n,m}=s_{n,m}^{-1}t_{n,m}$, where $s$ is q.scalar
and $t$ the recorded natural system reduction. Naturality is that of the composite natural
transformation. At $m=n$, the system transition is identity; transpose under the scalar adjunction
and use its unit-preservation equation, obtaining scalarUnit. For $r\le m\le n$, substitute this
expression twice. Move $s^{-1}$ past the reduction by naturality, apply the recorded system
reduction cocycle, and cancel the adjacent $s\,s^{-1}$ pair. The remaining reassociation word is
exactly scalarAssoc by its definition from the same scalar adjunctions. Thus reduction_identity,
reduction_composition and reduction_naturality hold for these very scalar coordinates.
Uses: det-sp-coefficient-towers-abelian, def-sp-coefficient-tower-shriek-interfaces.

19. Exact open extension is triangulated after ordinary derived localization, and total
right-derived proper direct image is triangulated by the K-injective construction; Base supplies
those resolutions. Their composite and realization conjugate are triangulated. Combine this with
steps 8-9 to finish CompositionCoherence, with steps 10-15 to form EtaleCalculus, and with steps
17-18 to form ReductionCalculus. Step 16 gives open_normalization, so these fields form Calculus for
the chosen $z,h$. Its EtaleNormalized witness is precisely $g$: by steps 12-13 the inverse of
etale_shriek is the transported actual $\theta_c$, with graphDerivedSum and graphSupportCoordinates
exactly as in that definition. No equality for a previously supplied etale-shriek iso is used. Also
retain the tower refinement equation: for a geometric refinement the graph-extension word composed
with its proper/open refinement mate has the open-unit restriction on every lift graph and zero on
the complement. The graph-map uniqueness and mate-pasting statements therefore identify these actual
words; degreewise localization and the derived unit preserve the identity. Passing through common
refinements gives rho_(c,d) Theta_c = Theta_d, in the fixed coordinates used in step 7. With sigma_c
= Theta_c inverse, cancellation gives rho_(c,d) followed by sigma_d = sigma_c. This supplies
EtaleRefinementCompatible for this jointly constructed cal, without using finite evaluations to
detect equality or claiming a law for arbitrary refinements.
Uses: lem-weil-pbc-exact-functor-derived-factorization, lem-pc-right-derived-functor-triangulated,
def-sp-tower-shriek-data, def-sp-coefficient-tower-shriek-interfaces,
def-sp-tower-gluing-interfaces, def-sp-varying-ring-graph-comparison,
lem-route-graph-map-exists-unique, lem-sp-compactification-refinement-coherence,
lem-sp-exact-derived-transformation-pasting, lem-cbc-proper-open-clopen-projector,
lem-weil-pbc-mate-pasting.

20. Apply SpChartAdmissibility.global_tate_family, the corrected Tate-family theorem, on all
schemes where $\ell$ is invertible, with the Tate-data definition. Its construction is independent
of the calculus choices. Every coordinate-calculus scheme is over $k$, so $\ell$ is a unit
there because $\operatorname{char}(k)=p\ne\ell$. Together with $z,h$ and the graph-normalized
Calculus of step 19 this is exactly the requested tuple. No chart-adjunction or global smooth right
adjoint is needed.
Uses: lem-sp-global-tate-family, def-sp-chart-tate-tower-data.
-/
theorem global_chart_fixed_calculus
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) :
    ∃ z : SpTowerCalculus.FiniteCoordinates l E,
    ∃ h : SpTowerCalculus.Preservation l E k b o q,
    ∃ cal : SpTowerCalculus.Calculus l E k b o q z h,
      EtaleNormalized l E b o q k z cal.etale ∧
      EtaleRefinementCompatible l E b o q k z h cal ∧
        Nonempty (∀ T : Scheme.{u}, IsUnit (l : Γ(T, ⊤)) → SpChartAdmissibility.Twists l E T) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
