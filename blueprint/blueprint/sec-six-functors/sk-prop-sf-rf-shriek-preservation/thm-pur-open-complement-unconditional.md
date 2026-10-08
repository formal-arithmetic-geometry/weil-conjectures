+++
id = "thm-pur-open-complement-unconditional"
kind = "theorem"
title = "The open-complement condition is unconditional and uniform in the coefficient ring"
order = 2080
uses = ["def-exc-direct-image-input", "def-exc-open-complement-bound", "def-pur-conventions", "def-sbc-affine-space", "def-weil-finite-field-fiber", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "lem-exc-open-complement-known", "lem-kun-cd-sep-closed-point", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-strict-henselization-stalk-formula", "thm-dg-finite-type-constructibility", "thm-exc-curve-open-constructible-general", "thm-exc-curve-open-dimension-general", "thm-exc-direct-image-input-holds", "thm-pur-general-admissibility", "thm-sc-finite-type-torsion-cd"]
+++
Let $k$ be a separably closed field, let $A$ be a finite commutative ring
annihilated by a power of a prime $\ell\neq\operatorname{char}(k)$, let
$T$ be a finite-type
$k$-scheme of dimension at most $d$, and let
$j:V\hookrightarrow T$ be a
quasi-compact open immersion.
Then the pair $(V,T)$ satisfies the open-complement condition of
[def-exc-open-complement-bound] with $c=2d$, and it does so for
*every* finite coefficient ring $A$ of that shape at once: both
clauses hold — the vanishing $R^qj_*M=0$ for every $q>2d$ and every
sheaf $M$ of $A$-modules on $V_{\Et}$, and the
constructibility of
$R^qj_*F$ in every degree for every constructible $A$-sheaf $F$ — and
the constant $2d$ depends on $T$ alone, not on $A$. In particular, in
the setting of the global finite-field datum with $k=\Fbar$ and at the
finite coefficient stages $A=A_{E,n}$ of [def-pur-conventions], the
condition holds for every $n\geq1$ with the same constant $2d$; for the
chart complements $W_U\subseteq\mathbf A^{d_U}_V$ of the assembly
[thm-pur-general-admissibility], where
$d_U+\dim V\leq d_U+\dim Y$, it holds with
$c_U=2(d_U+\dim V)$, again independent of $n$. The special cases
recorded in [lem-exc-open-complement-known] — dimension zero, where an
open immersion of a zero-dimensional Noetherian scheme is also closed, and
dimension at most one, by
[thm-exc-curve-open-dimension-general], [thm-exc-curve-open-constructible-general]
— are independent computations of the same condition and are neither used
nor superseded here.

## Proof

The argument is that of [lem-exc-open-complement-known], repeated with
its two hypotheses weakened and its constant tracked; no step of it uses more
about $k$ or about $A$ than the hypotheses of the statement, which is why
the conclusion is uniform in the coefficient ring.

*Step 1: the direct-image input over $k$.* The field $k$ is
separably closed, so both clauses of the direct-image finiteness input
[def-exc-direct-image-input] hold over $k$ by
[thm-exc-direct-image-input-holds], for $N$ the exponent annihilating
$A$ and every finite commutative ring annihilated by $N$.

*Step 2: the constructibility clause.* The open immersion $j$ is
quasi-compact and $T$ is of finite type over $k$, so $j$ is a morphism
of finite type between finite-type $k$-schemes; clause (1) of the input
therefore gives, for every constructible $A$-sheaf $F$ on $V_{\Et}$ and
every $q\geq0$, the constructibility of $R^qj_*F$ on $T_{\Et}$. This is
the second clause of the open-complement condition, and it uses
[thm-dg-finite-type-constructibility] through that input.

*Step 3: the vanishing clause.* Fix a geometric point
$\bar t\to T$. The strict-henselization stalk formula
[prop-weil-pbc-strict-henselization-stalk-formula] identifies the stalk of
the higher direct image with the cohomology of the open complement over the
strict henselization at $\bar t$,

$$
\bigl(R^qj_*M\bigr)_{\bar t}\cong H^q\bigl(V\times_TT_{(\bar t)},M\bigr),
$$

a filtered colimit of the groups $H^q(V\times_TU,M)$ over the pointed
étale neighbourhoods $U\to T$ of $\bar t$. Each $V\times_TU$ is an
open subscheme of the étale $T$-scheme $U$, hence a finite-type
$k$-scheme of dimension at most $\dim U=\dim T\leq d$; the sheaf $M$ of
$A$-modules is a torsion sheaf of abelian groups, $A$ being finite and
annihilated by a power of $\ell\neq\operatorname{char}(k)$, and $k$ is
separably closed with characteristic prime to that power, so clause (2) of
the input gives $H^q(V\times_TU,M)=0$ for every $q>2d$. A filtered
colimit of zero groups is zero, so every geometric stalk of $R^qj_*M$
vanishes for $q>2d$, and the conservativity of geometric stalks
[lemma-weil-pbc-geometric-stalk-conservative] makes the sheaf itself zero.
This is the first clause of the open-complement condition, with $c=2d$.

*Step 4: uniformity in the coefficient ring.* Steps 2 and 3 use of
$A$ exactly its finiteness and the annihilation by a power of a prime
$\ell\neq\operatorname{char}(k)$: the constructibility clause is clause (1)
of the input, whose only coefficient hypothesis is that $A$ is finite and
annihilated by an integer invertible in $k$, and the vanishing clause is
clause (2), which is quantified over all torsion sheaves and mentions no
coefficient ring. The integer $d=\dim T$ likewise depends on the scheme
alone. Hence both clauses hold with the constant $2d$ for every finite ring
$A$ of the stated shape, which is the uniformity assertion. In the global
finite-field datum one has $k=\Fbar$, separably closed with
$\operatorname{char}(k)=p$, and $A_{E,n}$ is annihilated by the power
$\varpi_E^n$ of the prime $\ell\neq p$, so the condition holds at every
stage $n\geq1$ with the constant $2d$; for the chart complement
$W_U$ of the closed subscheme $U\subseteq\mathbf A^{d_U}_V$ of
[def-sbc-affine-space] the ambient scheme is of dimension
$d_U+\dim V\leq d_U+\dim Y$, giving $c_U=2(d_U+\dim V)$ independently of
$n$. This is the assertion of the second half of the statement, and the
final sentence records the two independent computations of the same condition
in [lem-exc-open-complement-known].
