import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Final assembly: the Weil conjectures" =>

This chapter assembles the final theorems from the interface hypotheses.
Everything here is Version I/II material: linear algebra and field theory
over an abstract algebraically closed coefficient field $`K` of
characteristic $`0`, consuming the trace formula, duality, and purity
only through their interface statements.

:::author "weil_project" (name := "Weil Conjectures Formalization Project")
:::

:::group "group:weil-final"
The Weil conjectures: cohomological factorization, rationality, functional
equation, Riemann hypothesis, and their assembly into the final theorem.
:::

# Cohomological factorization

:::theorem "thm:cohomological-factorization" (parent := "group:weil-final") (uses := "def:zeta-function, def:frobenius-module, def:reversed-charpoly") (effort := "small")
Given the trace-formula data $`(H^i, F_i)_{i=0}^{2d}` for $`X/\Fq`, the
image $`Z_K` of $`Z(X, t)` in $`K[\![t]\!]` factors as
$$`Z_K = \prod_{i=0}^{2d} \charrev{F_i}^{\,(-1)^{i+1}},`
the product taken in the unit group $`1 + tK[\![t]\!]` — so no division of
power series appears in the statement.
:::

:::proof "thm:cohomological-factorization" (uses := "thm:trace-formula, lem:det-trace")
Taking logarithms, $`\log Z_K = \sum_{n} N_n t^n/n`; substituting the trace
formula termwise and exchanging the finite sum over $`i` with the sum over
$`n` gives $`\log Z_K = \sum_i (-1)^i \sum_n \Tr(F_i^n) t^n/n`. By the
determinant–trace identity each inner sum is
$`-\log \charrev{F_i}`, and applying the group isomorphism $`\exp`
converts the alternating sum of logarithms into the alternating product.
:::

# Rationality

:::theorem "thm:zeta-rationality" (parent := "group:weil-final") (uses := "def:zeta-function") (lean := "AlgebraicGeometry.Scheme.zetaSeries_rational") (priority := "high") (effort := "medium")
(Dwork's theorem; here via the ℓ-adic route.) For any scheme $`X` of
finite type over $`k = \Fq`, there are polynomials
$`P, Q \in \ZZ[t]` with $`Q(0) = 1` and
$`Z(X, t) \cdot Q = P` in $`\QQ[\![t]\!]`. In reduced form: unique coprime
$`A, B \in \ZZ[t]` with constant term $`1` and $`Z = A/B`.
:::

:::proof "thm:zeta-rationality" (uses := "thm:cohomological-factorization")
From the factorization, $`Z_K` is a ratio of polynomials over $`K`, so the
coefficient sequence of $`Z` satisfies a linear recurrence over $`K`; hence
its Hankel matrix has finite rank over $`K`. The Hankel entries are
rational numbers, and rank is insensitive to field extension (a nonzero
minor *is* a nonzero rational), so the rank is finite over $`\QQ` and
$`Z \in \QQ(t)`. The Euler product gives $`Z \in 1 + t\ZZ[\![t]\!]`; the
integral Fatou lemma upgrades the presentation to integer polynomials with
$`Q(0) = 1`, and the normalized Gauss lemma reduces the fraction. The
Hankel, Fatou, and Gauss steps will be recorded as separate nodes of the
elementary-foundations chapter.
:::

# Functional equation

:::theorem "thm:functional-equation" (parent := "group:weil-final") (uses := "def:zeta-function, def:functional-equation-predicate") (effort := "medium")
In the situation of the interface (trace formula and similitude pairings
with multiplier $`q^d`, middle pairing $`(-1)^d`-symmetric, endpoint
normalization), with $`b_i = \dim H^i`, $`\chi = \sum_i (-1)^i b_i`:
$`d\chi/2 \in \ZZ`, and there is $`\varepsilon \in \{\pm 1\}` with
$$`Z\bigl(X, 1/(q^{d} t)\bigr) = \varepsilon\, q^{d\chi/2}\, t^{\chi}\, Z(X, t)`
as rational functions. In root-multiset form: $`\alpha \mapsto q^d/\alpha`
matches the reciprocal roots of $`P_i` with those of $`P_{2d-i}`, with
multiplicity — which is exactly the repository predicate
{bpref "def:functional-equation-predicate"}[].
:::

:::proof "thm:functional-equation" (uses := "thm:cohomological-factorization, thm:poincare-duality, lem:reciprocal-charpoly")
Substitute $`T \mapsto (q^d T)^{-1}` into the factorization and replace
each factor by its dual partner using the reciprocal-polynomial identity
for the similitude pair $`(H^i, H^{2d-i})`. Collecting terms: the powers of
$`T` contribute $`T^{\chi}`, the signs contribute $`(-1)^{\chi}`, and the
determinants contribute $`\prod_i D_i^{(-1)^i}` with $`D_i = \det F_i`.
Pairing $`i` with $`2d - i` gives $`D_i D_{2d-i} = q^{d b_i}`, and taking
determinants in the middle-degree similitude gives $`D_d^2 = q^{d b_d}`;
the parity lemma (an alternating perfect form forces even dimension) makes
$`d b_d` even, so $`\delta := D_d q^{-d b_d/2}` satisfies
$`\delta^2 = 1` and the sign is $`\varepsilon = (-1)^{\chi}
\delta^{(-1)^d}` — no Pfaffians needed. The identity holds over $`K` and
both sides lie in $`\QQ(t)`, so it descends to $`\QQ`.
:::

# Riemann hypothesis

:::theorem "thm:riemann-hypothesis" (parent := "group:weil-final") (uses := "def:zeta-function, def:riemann-hypothesis-predicate, def:universal-purity") (priority := "high") (effort := "medium")
In the situation of the interface with universal purity (AX4), the
polynomials $`P_i = \charrev{F_i}` descend to $`\ZZ[t]`, and every complex
root $`z` of $`P_i` satisfies $`\|z\| = q^{-i/2}` — the repository
predicate {bpref "def:riemann-hypothesis-predicate"}[]. Every reciprocal
root is an algebraic integer all of whose complex conjugates have absolute
value $`q^{i/2}`.
:::

:::proof "thm:riemann-hypothesis" (uses := "thm:purity-smooth-proper, thm:zeta-rationality, thm:cohomological-factorization, lem:weight-separation")
The arithmetic pipeline. (1) *No cancellation:* by weight separation, for
$`i \neq j` the factors $`\charrev{F_i}` and $`\charrev{F_j}` share no
root, so the odd and even parity products $`O` and $`E` are coprime in
$`K[t]`. (2) *Factor identification:* rationality provides reduced coprime
$`A, B \in \ZZ[t]` with $`Z = A/B`; coprimality persists under
$`\QQ \subseteq K` and reduced normalized fractions are unique, so
$`O = A` and $`E = B` in $`K[t]`. Hence every eigenvalue is a reciprocal
root of an *integer* polynomial — algebraicity is proved exactly here.
(3) *Descent:* every automorphism of $`K` fixes $`\QQ`, permutes the root
multiset of $`A` (resp. $`B`), and preserves each universal-weight class;
since the weight classes partition the roots, each $`P_i` has
automorphism-fixed coefficients, which lie in $`\QQ` because the fixed
field of $`\operatorname{Aut}(K/\QQ)` is $`\QQ`; the normalized Gauss lemma
then gives $`P_i \in \ZZ[t]`. (4) *Root moduli:* a complex root $`z` of
$`P_i` determines an embedding $`\QQ(\alpha) \to \CC` sending a suitable
eigenvalue $`\alpha` to $`z^{-1}`; extending it to
$`\iota \colon K \to \CC` (cardinality bound $`\#K \leq 2^{\aleph_0}`) and
applying universal purity gives $`\|z^{-1}\|^2 = q^{i}`.
:::

# The final theorem

:::theorem "thm:weil-conjectures" (parent := "group:weil-final") (uses := "def:zeta-function, def:weil-factorization, def:functional-equation-predicate, def:riemann-hypothesis-predicate") (lean := "AlgebraicGeometry.Scheme.weil_conjectures") (owner := "weil_project") (priority := "high") (effort := "large")
Let $`X` be a smooth, proper, geometrically integral scheme of dimension
$`d` over a finite field $`k` with $`q` elements. Then there exists a
family $`P \colon \operatorname{Fin}(2d+1) \to \ZZ[t]` such that
`IsWeilFactorization q d Z P`, `WeilFunctionalEquation q d P`, and
`WeilRiemannHypothesis q d P` all hold: the zeta function factors with
normalized integer polynomials and endpoints $`1 - t` and $`1 - q^d t`,
the map $`\alpha \mapsto q^d/\alpha` matches reciprocal roots in
complementary degrees, and all complex roots of $`P_i` have absolute value
$`q^{-i/2}`. The family is uniquely determined by $`(Z, q, d)`, hence
independent of $`\ell`.
:::

:::proof "thm:weil-conjectures" (uses := "thm:cohomological-factorization, thm:zeta-rationality, thm:functional-equation, thm:riemann-hypothesis")
Instantiate the interface for $`X` (Version III provides the data; until
then the four hypotheses are temporary axioms), obtain the factorization
with $`P_i = \charrev{F_i}`, whose integrality and root-modulus properties
are the Riemann-hypothesis pipeline; the endpoints come from the
normalization $`H^0 = K`, $`F_0 = 1` and its dual partner (eigenvalue
$`q^d`); the functional-equation predicate is the root-multiset form of the
graded functional equation; and uniqueness follows because the weight
strata of the root multiset of $`A` and $`B` are determined by
$`(Z, q, d)` alone.
:::
