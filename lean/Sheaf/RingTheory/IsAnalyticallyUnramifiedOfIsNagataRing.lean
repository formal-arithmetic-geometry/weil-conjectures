/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.NagataRing
public import Sheaf.RingTheory.AnalyticallyUnramified
import Sheaf.Algebra.ChangeIdealCompletion
import Sheaf.RingTheory.AnalyticallyUnramifiedPrincipalCriterion
import Sheaf.RingTheory.FiniteOverNagata
import Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes
import Sheaf.RingTheory.IntegralExtensionDimension
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataLocalization
import Sheaf.RingTheory.RegularLocalDimOneIffNormal

/-!
# Reduced completion of a local Nagata domain

Source: Stacks Project, Algebra, Lemma Tag 0331
(blueprint: lem-weil-pbc-local-nagata-domain-analytically-unramified).
-/

@[expose] public section

universe u

/-- A Noetherian local Nagata integral domain has reduced maximal-ideal-adic completion.
Source: Stacks Project, Algebra, Lemma Tag 0331
(blueprint: lem-weil-pbc-local-nagata-domain-analytically-unramified).

Proof (the seven steps of the DAG node):

1. Induct on the finite Krull dimension $d=\dim A$: it is finite because the maximal ideal of a
Noetherian local ring has finitely many generators and [lem-weil-pbc-noetherian-local-dimension-
le-generators] bounds its dimension by their number. If $d=0$, the only prime of the local domain
$A$ is $(0)=\mathfrak m$, so $A$ is a field; its $\mathfrak m$-adic completion is $A$, which is
reduced. In the inductive step assume the assertion for all Noetherian local Nagata domains of
dimension strictly less than $d$. Dependencies: def-weil-pbc-adic-completion, def-weil-pbc-krull-
dimension-ring, lem-weil-pbc-noetherian-local-dimension-le-generators.

2. Let $S$ be the integral closure of $A$ in $K=\operatorname{Frac}(A)$. Since $A$ is Nagata, its
quotient by $(0)$ is N-2 [def-weil-pbc-nagata-ring], so $S$ is a finite $A$-module [def-weil-pbc-
japanese-domain]. It is a normal domain with fraction field $K$ [lem-weil-pbc-integral-closure-
finite-extension-normal], and is Nagata [lem-weil-pbc-finite-over-nagata-nagata]. Finiteness makes
$S$ Noetherian [lem-weil-pbc-finite-algebra-noetherian] and integral over $A$ [lem-weil-pbc-
finite-algebra-is-integral], so $\dim S\le d$ [lem-weil-pbc-integral-extension-dimension]. The
finite fibre $S/\mathfrak mS$ has finitely many maximal ideals by [lem-weil-pbc-finite-over-zero-
dim-local-discrete-spectrum]; their preimages are exactly the finitely many maximal ideals
$\mathfrak n_1,\ldots,\mathfrak n_r$ of $S$, since each contracts to $\mathfrak m$ [lem-weil-pbc-
finite-algebra-local-radical]. Dependencies: def-weil-pbc-nagata-ring, def-weil-pbc-japanese-
domain, lem-weil-pbc-integral-closure-finite-extension-normal, lem-weil-pbc-finite-over-nagata-
nagata, lem-weil-pbc-finite-algebra-noetherian, lem-weil-pbc-finite-algebra-is-integral, lem-weil-
pbc-integral-extension-dimension, lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum, lem-
weil-pbc-finite-algebra-local-radical.

3. The inclusion $A\hookrightarrow S$ is an injection of finite $A$-modules, with finite cokernel
because $A$ is Noetherian. Exactness of completion on finite modules [lem-weil-pbc-completion-
exact-finite-modules] makes the induced ring map $\widehat A_{\mathfrak m}\hookrightarrow\widehat
S_{\mathfrak mS}$ injective. Hence reducedness of the latter implies reducedness of $\widehat
A_{\mathfrak m}$. Dependencies: lem-weil-pbc-completion-exact-finite-modules.

4. For each $n\ge1$, $A/\mathfrak m^n$ is Artinian local [lem-weil-pbc-noetherian-local-quotient-
artinian-local]. The finite algebra $B_n=S/\mathfrak m^nS$ over it has exactly the maximal ideals
$\mathfrak n_i/\mathfrak m^nS$ and Jacobson radical consisting of nilpotent elements [lem-weil-
pbc-finite-over-zero-dim-local-discrete-spectrum]. The product decomposition [lem-weil-pbc-
product-of-localizations-at-maximal], with each factor identified by [lem-weil-pbc-localization-
at-prime-of-quotient], gives $B_n\cong\prod_i S_{\mathfrak n_i}/\mathfrak m^nS_{\mathfrak n_i}$,
compatibly with reduction in $n$. Taking compatible inverse limits yields $\widehat S_{\mathfrak
mS}\cong\prod_i\varprojlim_n S_{\mathfrak n_i}/\mathfrak m^nS_{\mathfrak n_i}$. Put
$J=\bigcap_i\mathfrak n_i$. The ideal $J/\mathfrak mS$ is finitely generated, since $S/\mathfrak
mS$ is Noetherian [lem-weil-pbc-finite-algebra-noetherian] and [lem-weil-pbc-noetherian-submodule-
finite] applies; each generator is nilpotent by the finite-fibre result, so a sufficiently high
power of their ideal vanishes. Thus $J^N\subseteq\mathfrak mS$ for some $N$, whereas $\mathfrak
mS\subseteq J$. On localization at $\mathfrak n_i$, distinct maximal ideals become the unit ideal,
so $JS_{\mathfrak n_i}=\mathfrak n_iS_{\mathfrak n_i}$. Thus the powers of $\mathfrak
mS_{\mathfrak n_i}$ and $\mathfrak n_iS_{\mathfrak n_i}$ are cofinal, and [lem-weil-pbc-change-
ideal-completion] identifies each displayed inverse limit with $\widehat{S_{\mathfrak
n_i}}_{\mathfrak n_i}$. Consequently $\widehat S_{\mathfrak mS}\cong\prod_i\widehat{S_{\mathfrak
n_i}}_{\mathfrak n_i}$. Dependencies: lem-weil-pbc-noetherian-local-quotient-artinian-local, lem-
weil-pbc-finite-over-zero-dim-local-discrete-spectrum, lem-weil-pbc-product-of-localizations-at-
maximal, lem-weil-pbc-localization-at-prime-of-quotient, lem-weil-pbc-finite-algebra-noetherian,
lem-weil-pbc-noetherian-submodule-finite, lem-weil-pbc-change-ideal-completion.

5. Each $S_{\mathfrak n_i}$ is a Noetherian local normal domain of dimension at most $d$ by [lem-
weil-pbc-localization-dimension-chains-below-prime], and is Nagata by [lem-weil-pbc-nagata-
localization]. If its dimension is less than $d$, the induction hypothesis gives reduced
completion. For factors of dimension $d$ it remains to prove the assertion for a normal local
Nagata domain $R$ of dimension $d$; the argument in the next two steps does this. Products of
reduced rings are reduced, so this proves reducedness of $\widehat S_{\mathfrak mS}$ and then, by
step 3, of $\widehat A_{\mathfrak m}$. Dependencies: lem-weil-pbc-localization-normal-domain, lem-
weil-pbc-nagata-localization, lem-weil-pbc-localization-dimension-chains-below-prime.

6. Let $(R,\mathfrak n)$ be a Noetherian normal local Nagata domain with $\dim R=d>0$. Choose
$0\ne x\in\mathfrak n$. Since $xR=R\cap xR$ inside $\operatorname{Frac}(R)$, [lem-weil-pbc-normal-
domain-fractional-principal-quotient-ass] says $R/xR$ has no embedded associated primes and every
associated prime $\mathfrak p$ has height one. The localization $R_{\mathfrak p}$ is a one-
dimensional Noetherian normal local domain: normality comes from [lem-weil-pbc-localization-
normal-domain], and its dimension is one by [lem-weil-pbc-localization-dimension-chains-below-
prime]. Hence it is regular by [lem-weil-pbc-regular-local-dim-one-iff-normal]. This verifies
conditions (2) and (3)(a) of [lem-weil-pbc-analytic-unramified-principal-criterion], while $x\ne0$
and $x\in\mathfrak n$ verify its condition (1). Dependencies: lem-weil-pbc-normal-domain-
fractional-principal-quotient-ass, lem-weil-pbc-localization-normal-domain, lem-weil-pbc-
localization-dimension-chains-below-prime, lem-weil-pbc-regular-local-dim-one-iff-normal, lem-
weil-pbc-analytic-unramified-principal-criterion.

7. For each associated prime $\mathfrak p$ above, $R/\mathfrak p$ is a Noetherian local domain and
is Nagata by the quotient clause of [lem-weil-pbc-finite-over-nagata-nagata]. Its dimension is
strictly less than $d$: any chain of primes above $\mathfrak p$ lifts to a chain in $R$, and
prepending $(0)\subsetneq\mathfrak p$ lengthens it by one. The induction hypothesis therefore says
$R/\mathfrak p$ is analytically unramified, verifying condition (3)(b). Apply [lem-weil-pbc-
analytic-unramified-principal-criterion] with $t=x$ to obtain reducedness of $\widehat
R_{\mathfrak n}$, completing the normal case and the induction. Dependencies: lem-weil-pbc-finite-
over-nagata-nagata, lem-weil-pbc-analytic-unramified-principal-criterion. -/
theorem isAnalyticallyUnramified_of_isNagataRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] (hA : IsNagataRing A) :
    IsAnalyticallyUnramified A := by
  sorry
