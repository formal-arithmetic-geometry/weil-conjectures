/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.FunctorialFanDesingularization
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent
public import Sheaf.AlgebraicGeometry.RegularNormalizedResolutionRule
public import Sheaf.AlgebraicGeometry.InducedNormalizedLogResolution
public import Sheaf.AlgebraicGeometry.CharacteristicZeroLogStrata
public import Sheaf.TraceFormula.SharpeningFanBijection
import Sheaf.AlgebraicGeometry.QEOrdinaryRegularResolution
import Sheaf.AlgebraicGeometry.NormalizedTowerRegularPullback
import Sheaf.AlgebraicGeometry.QEConductorNormalizedResolutionExtension
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison
import Sheaf.AlgebraicGeometry.GabberLogBlowupRegularization
import Sheaf.AlgebraicGeometry.NormalizedTowerSupportRecovery
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.AlgebraicGeometry.RationalToricCompletionRegularMap
import Mathlib.RingTheory.Smooth.Basic

/-!
# Characteristic-zero log-stratum independence of resolution

Source: ILO, Travaux de Gabber, VIII Theorem 2.3.10, Remarks 2.3.11--2.3.12,
3.2.19, Theorem 3.4.15 and Remark 3.4.16(i), pp. 93--94, 106, 113--114
(blueprint: lem-per-characteristic-zero-log-resolution-independence).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- A normalized regular-functorial rule exists; every such rule induces the fan
and log resolutions with their actual ordered centers. The underlying normalized
towers of two log structures agree over every scheme isomorphism when the generic
points of all their log strata have residue characteristic zero. No excellence
condition is imposed on the log schemes, and no componentwise contraction occurs.

Source: ILO VIII 2.3.10--2.3.12, 3.2.19, 3.3.15 and Theorem 3.4.15,
Remark 3.4.16(i) (blueprint: lem-per-characteristic-zero-log-resolution-independence).

Proof plan (the reviewed eleven-step split):
1. Choose the ordinary regular-functorial rule $F$ of [lem-per-qe-ordinary-regular-resolution].
On normal inputs let $N$ assign the normalized towers of
[lem-per-normalized-tower-regular-pullback]: they have coherent centers with nonempty nowhere
dense zero schemes and regular last level, and regular base change supplies the comparisons. For
a regular $h:T\to S$ of normal inputs every stage of the pulled-back normalized tower is normal
(the source is normal and later stages are normalizations), so a unit-ideal stage is an identity
and the ordinary deletions correspond exactly to deleting these identities; identity/composition
laws and surjective nondeletion survive. This fails for nonnormal sources: if the first center
of $F(X)$ misses a nonnormal point of an open $Y\subset X$, the pulled-back unit stage is
$Y^\nu\to Y$, not an isomorphism, so the normalization of $F$ itself is not regular-functorial
in the stated sense. Therefore let $\mathcal F=H_N$ of
[lem-per-qe-conductor-normalized-resolution-extension]: first the normalized blowup of the
conductor ideal, whose zero set is exactly the nonnormal locus and which commutes with regular
base change, then $N$. That lemma gives the finite centered tower, regular last level, nonempty
nowhere dense centers, contracted-pullback comparisons deleting only unit stages, which are
isomorphisms, identity/composition laws, finite disjoint unions and the empty input. This proves
the existence assertion. Uses: lem-per-qe-ordinary-regular-resolution,
lem-per-normalized-tower-regular-pullback, lem-per-qe-conductor-normalized-resolution-extension.

2. For the remaining assertions fix any normalized rule $\mathcal F$ as in the statement, using
the convention of VIII 2.3.2 that a normalized desingularization tower has nonempty nowhere
dense centers. Reduced finite-type rational schemes are excellent, hence qe, by
[lem-exc-fields-excellent] and [lem-exc-finite-type-localization-excellent] applied on affine
charts. Its restriction to them is smooth-functorial: smooth maps are flat by
[lem-pc-smooth-flat], their fibres are smooth by
[lem-weil-pbc-smooth-ring-map-base-change-composition], and those fibres are geometrically
regular by [lem-trf-smooth-geometrically-normal]. Toric realizations belong to this domain by
[lem-trf-toric-realization-finite-type]. Apply
[lem-trf-smooth-functorial-tower-torus-equivariance] to each component torus, extended by the
identity on the other components. It supplies torus invariance of every actual center ideal and
of the whole centered tower, with no contractions for the surjective projection and action maps.
Uses: lem-exc-fields-excellent, lem-exc-finite-type-localization-excellent, lem-pc-smooth-flat,
lem-weil-pbc-smooth-ring-map-base-change-composition, lem-trf-smooth-geometrically-normal,
lem-trf-toric-realization-finite-type, lem-trf-smooth-functorial-tower-torus-equivariance.

3. For each toric realization, [lem-trf-monoscheme-toric-tower-descent] descends its centered
tower uniquely to monoschemes, with smooth last monoscheme. Apply
[lem-trf-monoscheme-tower-comparison-coherence]: the comparisons of the fixed $\mathcal F$ meet
its smooth-pullback and identity/composition hypotheses, and the preceding descent gives its
unique lifts. Then apply the rule bijection in [lem-trf-sharpening-fan-bijection] on the
subcategory with torsion-free sharp stalk groups. This constructs the specified $\mathcal
R_{\mathcal F}$ on all fine torsion-free fans. It retains the centers, order, smooth last object
and coherent comparisons. The nonempty zero scheme of each toric center excludes the unit monoid
ideal; the ideal correspondence and sharpening preserve that condition. Open localizations,
isomorphisms and component inclusions have isomorphisms on stalk monoids, so are smooth by
[def-trf-fine-fan-blowup]. Uses: lem-trf-monoscheme-toric-tower-descent,
lem-trf-monoscheme-tower-comparison-coherence, lem-trf-sharpening-fan-bijection,
def-trf-fine-fan-blowup.

4. On a log scheme with a fan chart, pull back the fan tower by [lem-trf-log-fan-chart-blowup]
and delete whole-monoid centers. This is independent of the chart and has strict-pullback
comparisons. Indeed [lem-trf-strict-fan-chart-local-comparison] identifies, locally at each
source point, the two chart maps through isomorphic affine fan localizations.
Smooth-functoriality of $\mathcal R_{\mathcal F}$ and strict compatibility of chart pullback
identify the local contracted towers. To synchronize these local identifications, use the rule
on the finite disjoint union of the fan localizations; its surjective restrictions to the
original fan cover retain all indices before pullback. The uniqueness of center-preserving
comparisons in [lem-trf-log-tower-cover-rigidity] glues the local comparisons, with identity and
composition laws. Now [lem-trf-functorial-log-blowup-etale-descent] supplies the global finite
log tower. Its charted rule is precisely the one just compared and includes finite disjoint
unions. This establishes the asserted strict etale construction. Uses:
lem-trf-log-fan-chart-blowup, lem-trf-strict-fan-chart-local-comparison,
lem-trf-log-tower-cover-rigidity, lem-trf-functorial-log-blowup-etale-descent.

5. Apply [lem-per-gabber-log-blowup-regularization] to this chosen smooth-functorial fan rule.
Its statement gives the normalized underlying tower, Noetherian normal log regular stages,
regular last scheme, and equality of strict-transform and scheme pullback towers for strict
morphisms. Its hypotheses allow our separated Noetherian inputs and require no excellence. The
center is $J=\alpha(\mathcal I)\mathcal O$. No global center is the whole log structure, by
contraction in the preceding step. It follows that $V(J)$ is nonempty: choose a point where the
log ideal is proper; in its local ring all its generators are nonunits, for a log section maps
to a unit exactly when it is a log unit [def-trf-fs-log-blowup]. Hence they generate a proper
ring ideal there. Conversely a whole log ideal gives the unit ring ideal. This also explains why
the contractions match on the log and scheme sides. Uses:
lem-per-gabber-log-blowup-regularization, def-trf-fs-log-blowup.

6. Transport $(W,N)$ along $\phi$ so that both log structures are on the single scheme $X=V$.
Choose a common surjective finite strict etale cover on which both admit global charts, by
refining the two covers of [lem-trf-log-fan-chart-blowup]; take the finite disjoint union,
rather than separately contracting on its components. By
[lem-trf-log-tower-cover-synchronization] neither full tower loses a stage on this surjective
cover. Equality with ordered ring centers can be tested on it by
[lem-per-normalized-tower-support-recovery]. Thus it suffices to compare the towers when both
log structures are Zariski, keeping one indexing on this whole cover. Uses:
lem-trf-log-fan-chart-blowup, lem-trf-log-tower-cover-synchronization,
lem-per-normalized-tower-support-recovery.

7. Write $B_M=T_{\mathcal F}(X,M)$ and $B_N=T_{\mathcal F}(X,N)$. By
[lem-per-log-monoidal-associated-points], their associated-point images are contained
respectively in $\operatorname{Fan}(X,M)$ and $\operatorname{Fan}(X,N)$. Both sets lie in
$X_{\mathbf Q}$ by the stratum hypothesis. The rational localization is a quasi-compact flat
monomorphism; it need not be open. [lem-per-normalized-tower-support-recovery] therefore
recovers each full tower by closing the centers of its uncontracted restriction to $X_{\mathbf
Q}$. The strict comparison already obtained identifies the contracted restriction with the
induced tower of the restricted log structure. No stage contracts: a nonempty center has an
associated point, all such points map into $X_{\mathbf Q}$, and so its restriction is nonempty.
Hence equality for the two towers on $X_{\mathbf Q}$ implies equality on $X$. From now on $X$ is
a rational scheme, with no assumption that it is quasi-excellent. Uses:
lem-per-log-monoidal-associated-points, lem-per-normalized-tower-support-recovery.

8. Fix a geometric point $\bar x$ of $X$ and set $\widehat X_{\bar
x}=\operatorname{Spec}\widehat{\mathcal O^{\rm sh}_{X,\bar x}}$. By
[lem-trf-log-regular-completed-chart], after choosing a suitable sharp chart for $M$ its
complete ring is $B_k(P,n)=k[[P]][[t_1,\ldots,t_n]]$, with $P=\overline M_{\bar x}$ and with the
same chart monomials. For $N$ it has a presentation $B_{k'}(Q,m)$; both coefficient fields map
isomorphically to the same residue field, but need not be the same embedded subfield. Both
contain $\mathbf Q$. Apply [lem-per-rational-toric-completion-regular-map] to each presentation.
The two maps to the rational toric polynomial models are regular, and the complete scheme is a
reduced Noetherian qe input for $\mathcal F$. Each completion map to its respective log scheme
is strict; its underlying scheme map to $X$ is not claimed regular. Uses:
lem-trf-log-regular-completed-chart, lem-per-rational-toric-completion-regular-map.

9. For one of these presentations put $Z=\operatorname{Spec}\mathbf Q[P][t_1,\ldots,t_n]$. Its
fan is the sharpening of $P$; the extra polynomial variables have trivial log structure. The
toric descent and sharpening in Step 3 identify the induced log resolution on
$\operatorname{Spec}\mathbf Q[P]$ with $\mathcal F(\operatorname{Spec}\mathbf Q[P])$ including
their centers. Smooth-functoriality for the polynomial projection identifies the same objects on
$Z$ without contraction, since that projection is surjective. The strict log comparison from
Step 5 and the chart comparison from Step 4 identify the contracted pullback of $B_M$ to
$\widehat X_{\bar x}$ with the induced log resolution there. On the other hand the regular model
map of Step 8 and regular-functoriality identify this induced resolution with $\mathcal
F(\widehat X_{\bar x})$, after contraction. Repeat with $Q,m$ for $N$. Thus both contracted
completed towers equal the value of the single scheme-theoretic algorithm on the same complete
scheme. Uses: lem-trf-monoscheme-toric-tower-descent, lem-trf-sharpening-fan-bijection,
lem-per-gabber-log-blowup-regularization, lem-trf-strict-fan-chart-local-comparison,
lem-per-rational-toric-completion-regular-map.

10. Contractions alone do not yet identify the stage order. Let
$S=\operatorname{Fan}(X,M)\cup\operatorname{Fan}(X,N)$, a finite set by
[lem-per-log-monoidal-associated-points], and fix any extra geometric point $\bar x$. Choose a
geometric point above each $s\in S$ and let $H$ be the finite disjoint union of their completed
strict local schemes and $\widehat X_{\bar x}$. Work with the two log structures pulled back to
this single $H$. Every nonempty center of either tower remains nonempty on $H$: it has an
associated point over some $s\in S$ by that lemma; strict localization and completion over $s$
are faithfully flat local tests, so the fibre of this center survives
[lem-per-normalized-tower-support-recovery]. Therefore neither full pullback contracts any
stage. Step 9, applied simultaneously to the finite disjoint union of the respective rational
toric models, identifies both full pullbacks with $\mathcal F(H)$, with actual ordered centers.
The use of $\mathcal F(H)$, rather than independently chosen component towers, is essential.
Uses: lem-per-log-monoidal-associated-points, lem-per-normalized-tower-support-recovery,
lem-per-rational-toric-completion-regular-map, lem-per-gabber-log-blowup-regularization.

11. Restrict the equality on $H$ to its designated summand $\widehat X_{\bar x}$ without
deleting any stage. Since $\bar x$ was arbitrary, the completed strict local tests of
[lem-per-normalized-tower-support-recovery] give $B_M=B_N$ with the same finite index set and
all ideal centers. Step 7 recovers this equality before rational localization, and Step 6
descends it from the common strict etale cover. Undoing transport along $\phi$ gives
$T_{\mathcal F}(W,N)=\phi^*T_{\mathcal F}(V,M)$. All finite unions in the argument were treated
as single inputs, so this is equality with the original order, not componentwise contracted
equality. On the empty scheme the contracted tower has no proper center and length zero. No step
applied $\mathcal F$ directly to the possibly non-qe scheme $X$; only toric models and complete
local schemes were its inputs. Uses: lem-per-normalized-tower-support-recovery. -/
theorem characteristicZero_log_resolution_independence :
    Nonempty (RegularFunctorialNormalizedResolution.{u}) ∧
      ∀ F : RegularFunctorialNormalizedResolution.{u},
        Nonempty (InducedNormalizedLogResolution F) ∧
          ∀ (D : InducedNormalizedLogResolution F)
            (V W : FineSaturatedLogScheme.{u})
            (hV : IsNoetherianLogRegularInput V) (hW : IsNoetherianLogRegularInput W),
            V.scheme.IsSeparated → W.scheme.IsSeparated →
              ∀ φ : W.scheme ≅ V.scheme,
                HasCharacteristicZeroLogStrata V → HasCharacteristicZeroLogStrata W →
                  ((D.underlying V hV).toResolution).IsIsoOver
                    ((D.underlying W hW).toResolution) φ := by
  sorry

end AlgebraicGeometry
