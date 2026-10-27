/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.KummerLogMorphism
public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.RingTheory.LogRegularSaturationNormality
import WeilConjectures.RingTheory.CompletionDimension
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Very tame log quotients

Source: ILO VI Theorem 3.2 and Proposition 3.5, printed pp.73--76
(blueprint: lem-per-very-tame-log-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- The invariant quotient of a very tame, admissible, generically free action on a
Noetherian log regular fs log scheme is log regular and Kummer etale, with the
standard strict local charts and the categorical log factorization property.
Source: ILO VI Theorem 3.2 and Proposition 3.5, printed pp.73--76
(blueprint: lem-per-very-tame-log-quotient).

Proof plan:
Step 1. Apply [lem-per-tame-admissible-scheme-quotient] to the underlying $G$-scheme:
admissibility supplies its invariant affine cover, and very tameness supplies its prime-to-
residue-characteristic inertia hypothesis. It gives a Noetherian scheme quotient $q:X\to Y$,
finite surjective with geometric orbit fibres and $\mathcal O_Y=(q_*\mathcal O_X)^G$, and its
categorical property. Put $N=(q_*M)^G$. This is a log structure: an invariant section whose
structural image is a unit is an invariant unit, and the inverse of an invariant unit is
invariant; the identification of structural units is therefore $N\cap\mathcal
O_Y^\times=\mathcal O_Y^\times$.

Step 2. Fix $\bar x$ and $\bar y=q(\bar x)$, and put $H=\operatorname{Stab}_G(\bar x)$,
$A=\mathcal O_{X,\bar x}$ and $B=\mathcal O_{Y,\bar y}$. Apply [lem-per-finite-quotient-strict-
local-invariants]: $B=A^H$, $A$ is finite over $B$, and $N_{\bar y}=M_{\bar x}^H$. These are
strict local rings at geometric points, not invariants under the stabilizer of an ordinary
point. By [lem-sc-strict-henselization-noetherian], $A$ and $B$ are Noetherian. Write
$Q=\overline M_{\bar x}$ and $I$ for the nonunit log ideal. Log regularity gives $A/I$ regular
and $\dim A=\dim(A/I)+\operatorname{rank}Q^{\rm gp}$.

Step 3. Apply [lem-per-very-tame-equivariant-sharp-chart] to obtain the $H$-equivariant sharp fs
chart $a:Q\to M$ and diagonal pairing $\chi$ with fixed roots of unity. Its hypotheses are
exactly invertibility of $n=|H|$ and triviality on $Q$. The further very-tame hypothesis is
triviality on $A/I$, where $I=(a(u):u\ne0)A$. Apply [lem-per-very-tame-local-kummer-quotient]
using the finite extension of Step 2. It gives $P=Q\cap L$ with $P$ sharp fs, $P^{\rm
gp}=L\supset nQ^{\rm gp}$, finite index, a pointed etale-local chart of the actual $N$, and
$B/J\simeq A/I$, where $J=(a(p):p\ne0)B$. In particular $N$ is fs, since the neighbourhood
clause supplies a chart at every $\bar y$. Also $nu\in P$ for every $u\in Q$, directly from
$\chi_{nu}=\chi_u^n=1$.

Step 4. The finite injective extension $B\hookrightarrow A$ is integral by [lem-weil-pbc-finite-
algebra-is-integral]; [lem-weil-pbc-integral-injective-dimension-equal] gives $\dim B=\dim A$.
The finite-index inclusion $P^{\rm gp}=L\subset Q^{\rm gp}$ gives equal rational ranks, because
$nQ^{\rm gp}\subset L$. Hence $$\dim B=\dim(A/I)+\operatorname{rank}Q^{\rm
gp}=\dim(B/J)+\operatorname{rank}P^{\rm gp}.$$ The quotient $B/J$ is regular by the stratum
isomorphism. As $P$ identifies with the characteristic of $N$ at $\bar y$, $J$ is precisely its
nonunit log ideal. Thus the stratum and dimension conditions of [def-trf-fs-log-blowup] hold at
every geometric point, proving that $(Y,N)$ is log regular. This argument does not require $X$
to be integral or to come with a preselected global pair.

Step 5. Set $C=B\otimes_{\mathbf Z[P]}\mathbf Z[Q]$. By [lem-per-tame-diagonal-standard-closed-
immersion], whose quotient, chart, fixed-root, and trivial-stratum hypotheses were checked in
Steps 1–3, the comparison $C\to A$ is surjective and is represented etale locally by a strict
closed immersion. If $q_1,\ldots,q_s$ generate $Q$, then $nq_i\in P$. Reducing each coefficient
of a monomial expression modulo $n$ shows that the finitely many $z^{\sum r_iq_i}$, $0\le
r_i<n$, generate $C$ as a $B$-module. Thus $C$ is Noetherian by [lem-weil-pbc-finite-algebra-
noetherian], and $B\to C$ is injective since its composite with $C\to A$ is the inclusion
$B\hookrightarrow A$.

Step 6. The ring $C$ is strictly henselian local. Indeed, apply [lem-weil-pbc-finite-over-
henselian-local-product] to its finite algebra over strictly henselian $B$. In the closed fibre,
every nonzero monomial is nilpotent, since $(z^u)^n=z^{nu}$ with $0\ne nu\in P$ maps to zero in
the residue field. Here $nu\ne0$: saturation and sharpness imply that $Q^{\rm gp}$ is torsion
free, since $nv=0$ puts both $v,-v$ in $Q$, so $v$ is a unit. There are finitely many monoid
generators, so the ideal of nonzero monomials in this fibre is nilpotent and the quotient is
$k=B/\mathfrak m_B$. The finite henselian product therefore has exactly one factor with residue
field $k$; hence $C$ is henselian local with separably closed residue field. The standard chart
$P\to Q$ on $\operatorname{Spec}C\to\operatorname{Spec}B$ is injective, is Kummer, has group
cokernel killed by $n$, and has identity comparison morphism. The strict localization
$\operatorname{Spec}B\to Y$ is ind-etale locally on source and target, so by [lem-trf-ind-etale-
strict-local-invariance] its strict localization at every geometric point of
$\operatorname{Spec}B$ is the strict localization of $Y$ at the image geometric point, and the
pulled-back log structure, which has the chart $P$ by Step 3, has the same stalks there; hence
the stratum and dimension conditions proved for $(Y,N)$ in Step 4 hold at every geometric point
of $\operatorname{Spec}B$. Apply [lem-per-invertible-kummer-chart-log-regular] to this log
regular $(\operatorname{Spec}B,P)$: $\operatorname{Spec}C$ with chart $Q$ is log regular.

Step 7. The strictly local log regular ring $C$ is a domain. To see this without assuming
regularity of its underlying scheme, apply [lem-trf-log-regular-completed-chart] to its closed
geometric point. Its completion is one of the sharp fs formal-monoid models specified there.
Both models are domains by [lem-trf-log-regular-saturation-normality], including the mixed-
characteristic quotient. The completion map $C\to\widehat C$ is faithfully flat by [lem-weil-
pbc-local-completion-faithfully-flat] and injective by [lem-weil-pbc-faithfully-flat-
universally-injective] with module $C$. Thus $C$ embeds in a domain and is itself a domain. The
choice of chart in the completed-model theorem is irrelevant to this conclusion.

Step 8. Apply [lem-weil-pbc-finite-algebra-is-integral] to $B\hookrightarrow C$ and [lem-weil-
pbc-integral-injective-dimension-equal] to get $\dim C=\dim B=\dim A$. These dimensions are
finite because the rings are Noetherian local; this finiteness is also included in [lem-weil-
pbc-completion-dimension]. The surjection $C\to A$ of Step 5 is injective: if its kernel were
nonzero, every prime containing it would be nonzero in the domain $C$. A maximal-length chain of
primes in $A$ would lift to a chain in $C$ which could be extended at the bottom by $(0)$,
contradicting $\dim C=\dim A$. Hence $C\simeq A$. Together with strictness, this proves the
required strict-local cartesian monoid chart, rather than merely a closed immersion into a
standard cover.

Step 9. Use the pointed etale neighbourhood comparison which is a strict closed immersion in
Step 5. By the strict-localization clause of [lem-per-tame-diagonal-standard-closed-immersion],
its map on strict local rings at the selected geometric points is the map $C\to A$, which is the
isomorphism proved in Step 8; for a closed immersion this is the base-changed quotient map, by
[lem-trf-closed-immersion-strict-localization-cartesian]. The ordinary local ring of the target
maps faithfully flatly to its strict henselization by [lem-sc-strict-henselization-faithfully-
flat]. Apply [lem-weil-pbc-faithfully-flat-universally-injective] with the ordinary local ring
itself as module: its map into its strict henselization is injective. The closed-immersion
formula says every element of its kernel ideal maps to zero in this strict henselization, since
the base-changed quotient map is an isomorphism. Injectivity therefore makes the ordinary
localized kernel zero. The target is Noetherian, so finitely many generators of the kernel are
each killed by a denominator outside the selected prime; restrict to their product's principal
open. On that open the comparison is an isomorphism. Consequently the neighbourhood charts have
etale comparison. Their injective monoid map has finite group cokernel killed by the locally
invertible $n$, and $nu\in P$ for all $u\in Q$. If $Q^{\rm gp}$ has $r$ generators, this
cokernel is a quotient of $(\mathbf Z/n)^r$, so its order divides $n^r$ and is invertible as
required by the chart definition. The definition [def-per-fs-log-smooth-etale] now gives log
etaleness, while the characteristic maps are Kummer. This proves all local-chart clauses and
Kummer etaleness of $q$.

Step 10. Let $f:(X,M)\to(S,M_S)$ be an invariant log morphism. The categorical property of the
quotient from Step 1 gives a unique underlying map $g:Y\to S$ with $f=gq$. The map of log
sheaves $M_S\to f_*M=g_*q_*M$ takes values in $g_*(q_*M)^G=g_*N$ because $f$ is invariant, so it
defines a log morphism $g$ compatible with the already descended structural map. Any competing
log morphism has the same underlying $g$, and its log map has the same composite into $g_*q_*M$;
the inclusion $N\hookrightarrow q_*M$ is injective, so the two log maps agree. This proves
existence and uniqueness of the factorization.
-/
theorem exists_veryTame_logQuotient (X : FineSaturatedLogScheme.{u})
    [IsNoetherian X.scheme] (G : Type v) [Group G] [Finite G] (a : FSLogGroupAction G X)
    (hadmissible : ∀ x : X.scheme, ∃ U : X.scheme.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ (g : G) (z : X.scheme), (a.baseAction g).hom z ∈ U ↔ z ∈ U)
    (hfree : a.IsGenericallyFree) (hregular : X.IsLogRegular) (hverytame : a.IsVeryTame) :
    ∃ (Y : FineSaturatedLogScheme.{u}) (q : EtaleLogHom X Y),
      IsNoetherian Y.scheme ∧ IsFinite q.base ∧ Surjective q.base ∧ a.IsQuotient q ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x z : Spec (.of Ω) ⟶ X.scheme),
        x ≫ q.base = z ≫ q.base ↔ ∃ g : G, x ≫ (a.baseAction g).hom = z) ∧
      Y.IsLogRegular ∧ q.IsLogEtale ∧ q.IsKummer ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
        q.HasStrictLocalKummerChart t) ∧
      ∀ (S : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X S),
        (∀ g : G, (a.logMap g).CompEq f f) →
          ∃! r : EtaleLogHom Y S, q.CompEq r f := by
  sorry

end AlgebraicGeometry
