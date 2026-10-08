+++
id = "thm-sf-preservation-class"
kind = "theorem"
title = "The preservation clauses of exceptional-adjoint admissibility are theorems on the coefficient class"
order = 2085
uses = ["cor-pur-general-admissibility-datum", "cor-sf-ambient-adjoint-discharge", "def-compact-support-direct-image-detailed", "def-exc-open-complement-bound", "def-pur-conventions", "def-sbc-affine-space", "def-sf-fullcd-class", "def-sf-fullcd-used-class", "def-weil-ambient-exceptional-adjoint", "def-weil-compactifications-refinements", "def-weil-constructible-intervals", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "def-weil-scheme-morphism-properties", "lem-exc-open-complement-known", "lem-sf-proetale-constructible-origin", "prop-sf-comparison-bound-zero", "thm-pur-general-admissibility", "thm-pur-open-complement-unconditional", "thm-sf-ambient-adjoint-class", "thm-sf-fullcd-class"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, the algebraic
closure $k=\Fbar$ of the finite field $k_0$ of that datum, a
separated finite-type
$k$-scheme $Y$, a finite-type $k$-scheme $X$
([def-weil-scheme-morphism-properties]), and a
separated finite-type
$k$-morphism $f:X\to Y$; the source $X$ is then a separated finite-type
$k$-scheme as well, $f$ being separated and $Y$ separated over $k$.
Cover $Y$ by finitely many affine opens
$V\subseteq Y$, and for each $V$ cover $f^{-1}(V)$ by finitely many
affine opens $U\subseteq f^{-1}(V)$; each $U\to V$ is affine of finite
type, hence exhibits $U$ as a closed subscheme of the affine space
$\mathbf A^{d_U}_V$ of [def-sbc-affine-space] for some integer
$d_U\in\mathbf Z_{\geq0}$. Put $D=\max_U d_U$. Let $A=A_{E,n}$ be a
finite coefficient stage, let $Rf_{!,n}$ be the pro-étale
compact-support direct image
attached to a
compactification of
$f$, and let

$$
Rf_n^{\times}=\nu_X^*f^{\times}R\nu_{Y,*},
$$

with $\nu_X,\nu_Y$ the comparison morphisms of
[def-weil-pbc-site-comparison-morphism], be the right adjoint of
$Rf_{!,n}$ that [thm-sf-ambient-adjoint-class] constructs on the
blueprint's coefficient class [def-sf-fullcd-used-class]; that the
bounded constructible and finite-Tor objects of
[def-weil-finite-torsion-constructibility] and
[def-weil-finite-tor-amplitude] are exactly the complexes of étale
origin is [lem-sf-proetale-constructible-origin], and that both halves
of the ambient datum are theorems on them is
[cor-sf-ambient-adjoint-discharge]. Read the
exceptional inverse image
$Rf^!$ as the restriction of $Rf_n^{\times}$ to $D^b_c(Y,A)$ and to its
finite-Tor objects, and use the
constructible intervals
$D_c^{[a,b]}$ and the
finite-Tor condition. Then:

1. for all integers $a\leq b$,
$$
L\in D_c^{[a,b]}(Y,A)\quad\Longrightarrow\quad
Rf^!L\in D_c^{[a-2D,\,b+2\dim Y+1]}(X,A);
$$
1. if $K\in D^b_{ctf}(Y,A)$ has finite Tor amplitude in $[a,b]$, then
$Rf^!K$ has finite Tor amplitude in $[a-2D,b+2\dim Y+1]$; in particular
$Rf^!$ carries $D^b_{ctf}(Y,A)$ into $D^b_{ctf}(X,A)$;
1. the two constants $2D$ and $2\dim Y+1$ depend on $f$ and $Y$
alone and not on the coefficient stage $n$, so that the two clauses hold at
every finite coefficient stage $A_{E,n}$, $n\geq1$, with the same
constants;
1. consequently $f$ satisfies clauses (2) and (3) of
[def-weil-exceptional-adjoint-admissibility] at every finite coefficient
stage, with the signed constants $c_f^-=-2D$ and $c_f^+=2\dim Y+1$ of
that definition, *without* assuming clause (1) of that definition and
*without* assuming the ambient exceptional right adjoint datum of
[def-weil-ambient-exceptional-adjoint]: on the two categories
$D^b_c$ and $D^b_{ctf}$ that datum is the theorem
[cor-sf-ambient-adjoint-discharge]. In particular clause (v) of
the finite-Tor preservation summary holds at the stage $\Lambda=A$ for
*every* separated finite-type morphism $f$ with separated finite-type
target, the ambient datum
displayed there being redundant on that category.

This theorem concerns the finite coefficient stage and objects of
étale origin. The integral and field stages are established separately
in the subsequent coefficient-comparison sections; they are not premises
of this finite preservation argument.

## Proof

*Step 1: which functor is bounded.* By
[def-weil-exceptional-inverse-image] the functor $Rf^!$ is, on the
bounded constructible category $D^b_c(Y,A_{E,n})$, the restriction of the
ambient right adjoint $Rf_n^{\times}$ of $Rf_{!,n}$, and its restriction
to finite-Tor objects is the corresponding restriction of the same functor.
On the blueprint's coefficient class [def-sf-fullcd-used-class] that
right adjoint exists and is the explicit composite
$\nu_X^*f^{\times}R\nu_{Y,*}$ of
[thm-sf-ambient-adjoint-class](2), which also supplies its unit, its
counit and the compactification comparisons; the comparison morphisms
$\nu_X,\nu_Y$ are those of
[def-weil-pbc-site-comparison-morphism]. That the bounded constructible
and finite-Tor objects are exactly the complexes coming from the étale site
is [lem-sf-proetale-constructible-origin], and that both halves of the
ambient datum are theorems on that class is
[cor-sf-ambient-adjoint-discharge]. The bounds proved below are
therefore bounds on that explicitly constructed functor, and no clause of
[def-weil-ambient-exceptional-adjoint] is used in stating them.

*Step 2: the two bounds are the assembly of the purity chapter.* The
setting of [def-pur-conventions] is the present one: the same global
finite-field datum, the same $k=\Fbar$, the same separated finite-type
morphism $f:X\to Y$ between finite-type $k$-schemes and the same
coefficient ring $A=A_{E,n}$. [thm-pur-general-admissibility] proves
that a separated finite-type morphism satisfies the two preservation clauses
of [def-weil-exceptional-adjoint-admissibility] as soon as the
open-complement condition of [def-exc-open-complement-bound] holds for
the finitely many pairs $(W_U,\mathbf A^{d_U}_V)$ formed by the affine
charts of the statement, $W_U$ being the complement of $U$ in the affine
space $\mathbf A^{d_U}_V$ of [def-sbc-affine-space]; and
[cor-pur-general-admissibility-datum] removes that hypothesis by
[lem-exc-open-complement-known]. Indeed $\mathbf A^{d_U}_V$ is of
finite type over $k$ of dimension $d_U+\dim V\leq d_U+\dim Y$, the
complement $W_U$ is a quasi-compact open subscheme of it, and $A=A_{E,n}$
is a finite ring annihilated by the power $\varpi_E^n$ of the prime
$\ell\neq\operatorname{char}(k)$, so the pair satisfies the
open-complement condition with $c_U=2(d_U+\dim Y)$. The conclusion of
[cor-pur-general-admissibility-datum] is, in the notation of
[def-weil-constructible-intervals] and
[def-weil-finite-tor-amplitude], that $Rf^!$ carries
$D_c^{[a,b]}(Y,A)$ into $D_c^{[a-2D,b-2D+c]}(X,A)$ and finite Tor
amplitude in $[a,b]$ to finite Tor amplitude in $[a-2D,b-2D+c]$, where
$D=\max_Ud_U$ and $c=\max_U(c_U+1+2(D-d_U))$. For every chart $U$,

$$
c_U+1+2(D-d_U)=2d_U+2\dim Y+1+2D-2d_U=2D+2\dim Y+1,
$$

so the maximum is $c=2D+2\dim Y+1$, the lower end is $a-2D$, and the two
bounds become $[a-2D,b+2\dim Y+1]$: these are clauses (1) and (2) of the
statement. No clause of [def-weil-exceptional-adjoint-admissibility] is
used: [cor-pur-general-admissibility-datum] displays the ambient datum
only to record that on the coefficients it quantifies over — the bounded
constructible and finite-Tor objects, of étale origin by
[lem-sf-proetale-constructible-origin] — that datum is the theorem
[cor-sf-ambient-adjoint-discharge], whose vanishing half is the
class-restricted datum [def-sf-fullcd-class] supplied by
[thm-sf-fullcd-class] with the sharp comparison bound $M=0$ of
[prop-sf-comparison-bound-zero].

*Step 3: independence of the coefficient stage.* The charts
$U\subseteq f^{-1}(V)$, the integers $d_U$ and the number
$\dim V\leq\dim Y$ come from the presentation of the coordinate rings
$\mathcal O(U)$ over $\mathcal O(V)$, an operation on the schemes alone,
and do not depend on the coefficient ring; and the hypotheses under which
[lem-exc-open-complement-known] was applied in Step 2 are the same at
every finite stage, $A_{E,n}$ being a finite ring annihilated by the power
$\varpi_E^n$ of $\ell$. Hence both the open-complement condition with
the constants $c_U$ and the constants $D$, $c$ of
[thm-pur-general-admissibility] and
[cor-pur-general-admissibility-datum] are the same integers at every
stage, and instantiating that corollary at each $n\geq1$ gives clauses (1)
and (2) at $A_{E,n}$ with these constants and with no hypothesis; this is
clause (3). It is the stage-uniform form of the open-complement condition
recorded in [thm-pur-open-complement-unconditional].

*Step 4: reading the bounds in the definitions.* Clause (2) of
[def-weil-exceptional-adjoint-admissibility] asks for signed integers
$c_f^-,c_f^+\in\mathbf Z$ with
$Rf_n^{\times}L\in D_c^{[a+c_f^-,b+c_f^+]}(X,A)$ for every
$L\in D_c^{[a,b]}(Y,A)$, and clause (3) asks that $Rf_n^{\times}$ carry
$D^b_{ctf}(Y,A)$ into $D^b_{ctf}(X,A)$; by clauses (1) and (2) these hold
with $c_f^-=-2D$ and $c_f^+=2\dim Y+1$, and by Step 1 the functor these
two clauses bound is $Rf^!$ on the two categories they concern. Clause (1)
of the same definition is not assumed: the existence of $Rf_n^{\times}$ on
those categories, with its unit, counit and compactification comparisons, is
Step 1, that is [thm-sf-ambient-adjoint-class] read through
[def-weil-exceptional-inverse-image] and
[cor-sf-ambient-adjoint-discharge]. Finally clause (v) of
the finite-Tor preservation summary is the same two assertions at the coefficient
stage $\Lambda=A$, with the membership
$Rf^!D^b_{ctf}(Y,A)\subseteq D^b_{ctf}(X,A)$ as its conclusion and the
ambient exceptional right adjoint datum as its displayed hypothesis; by
Step 1 that hypothesis is, on that category and at that stage, the theorem
[cor-sf-ambient-adjoint-discharge], so the clause holds for every
separated finite-type morphism $f$ without it. The assertions of the
statement for the remaining coefficient stages are exactly the assertions
that this proof does not make, as the last paragraph of the statement
records.
