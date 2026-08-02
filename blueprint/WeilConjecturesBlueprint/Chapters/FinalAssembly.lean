import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Final assembly: the Weil conjectures" =>

This chapter derives every final conclusion from the four interface
hypotheses (trace formula {bpref "TR-interface-proper"}[], similitude
duality {bpref "DU-interface"}[], endpoint normalization
{bpref "DU-endpoint"}[], universal purity {bpref "COH-purity-input"}[])
and the arithmetic facts about the zeta series. Everything here is
Layer I/II material: linear algebra and field theory over an abstract
algebraically closed field $`K` of characteristic $`0` with
$`\#K \leq 2^{\aleph_0}`. The chain is deliberately fine-grained — each
node is one future Lean declaration.

:::author "weil_project" (name := "Weil Conjectures Formalization Project")
:::

:::group "grp-final"
The Weil conjectures: factorization, rationality, endpoints, functional
equation, no-cancellation, algebraicity, integrality, Riemann hypothesis,
independence of ℓ, and the combined theorem.
:::

# From point counts to the determinant factorization

:::lemma_ "W-log-zeta" (parent := "grp-final") (uses := "Z-zeta-series, LA-trace-iter") (tags := "elementary-missing") (effort := "small")
Logarithmic form of the trace formula: given graded trace data for $`X` —
finite-dimensional $`K`-spaces $`H^0, \dots, H^{2d}` with automorphisms
$`F_i` satisfying $`(N_n : K) = \sum_i (-1)^i \Tr(F_i^n)` for all
$`n \geq 1` — the image $`Z_K` of $`Z(X, t)` in $`K[\![t]\!]` satisfies
$$`\operatorname{logOf} Z_K = \sum_{i=0}^{2d} (-1)^i \sum_{n \geq 1} \Tr(F_i^n)\frac{t^n}{n}.`
:::

:::proof "W-log-zeta" (uses := "LA-exp-log-iso, TR-interface-proper")
By definition $`Z = \exp(\sum_n N_n t^n/n)`, so
$`\operatorname{logOf} Z_K = \sum_n N_n t^n / n` by the inverse property
({bpref "LA-exp-log-iso"}[]) — note the coercion $`\mathbb{N} \to \QQ
\to K` of the point counts. Substitute the trace formula termwise and
exchange the *finite* sum over $`i \in \{0, \dots, 2d\}` with the sum
over $`n`: the exchange is coefficientwise finite (each coefficient of
$`t^n` involves only the $`2d + 1` traces $`\Tr(F_i^n)`), so no
convergence issue arises. In Lean this is one `Finset.sum` exchange under
`PowerSeries.ext`.
:::

:::theorem "W-factorization" (parent := "grp-final") (uses := "Z-zeta-series, LA-frobenius-module, LA-charpoly-rev") (tags := "elementary-missing") (effort := "small") (priority := "high")
Cohomological factorization: with the graded trace data of
{bpref "W-log-zeta"}[],
$$`Z_K = \prod_{i=0}^{2d} P_{F_i}(t)^{(-1)^{i+1}} \quad\text{in } 1 + tK[\![t]\!],`
where $`P_{F_i}(t) = \charrev{F_i}` and the product is taken in the unit
group (integer powers of units — no power-series division in the
statement). The same statement holds verbatim for compactly-supported
trace data of an arbitrary separated finite-type $`X`
({bpref "TR-interface-cc"}[]), with the grading range determined by that
data.
:::

:::proof "W-factorization" (uses := "W-log-zeta, LA-det-trace-graded")
By {bpref "W-log-zeta"}[], $`\operatorname{logOf} Z_K` is the alternating
sum of the trace series; by the graded determinant–trace identity
({bpref "LA-det-trace-graded"}[]), applying $`\exp` to that sum yields
exactly the alternating product of the reversed characteristic
polynomials, and $`\exp(\operatorname{logOf} Z_K) = Z_K` since
$`Z_K(0) = 1`.
:::

# Rationality and the reduced integral presentation

:::theorem "W-rationality" (parent := "grp-final") (uses := "Z-zeta-series") (lean := "AlgebraicGeometry.Scheme.zetaSeries_rational") (tags := "elementary-missing") (effort := "medium") (priority := "high")
Rationality (Dwork's theorem, here by the $`\ell`-adic route): for *any*
scheme $`X` of finite type over $`k`, there are polynomials
$`P, Q \in \ZZ[t]` with $`Q(0) = 1` and
$`Z(X, t) \cdot Q = P` in $`\QQ[\![t]\!]`. This is the repository's
`zetaSeries_rational` (statement formalized, proof pending); it requires
no smoothness, properness, or connectedness.
:::

:::proof "W-rationality" (uses := "W-factorization, TR-interface-cc, LA-linear-recurrence-hankel, LA-rank-descent, Z-integrality, LA-fatou")
Apply {bpref "W-factorization"}[] to the compactly-supported trace data
({bpref "TR-interface-cc"}[]): $`Z_K = O/E` with
$`O = \prod_{i \text{ odd}} P_{F_i}` and
$`E = \prod_{i \text{ even}} P_{F_i}` *polynomials* over $`K` (finite
dimensionality bounds all degrees). Hence the coefficient sequence of
$`Z` satisfies the linear recurrence given by $`E` beyond degree
$`\deg O`, so by {bpref "LA-linear-recurrence-hankel"}[] (2 ⇒ 4) its
Hankel matrix has finite rank over $`K`. The Hankel entries are rational
numbers; by rank descent ({bpref "LA-rank-descent"}[]) the rank is
finite over $`\QQ`, so by (4 ⇒ 1) $`Z \in \QQ(t)`. Finally
$`Z \in 1 + t\ZZ[\![t]\!]` ({bpref "Z-integrality"}[]), so the integral
Fatou lemma ({bpref "LA-fatou"}[]) produces $`P, Q \in \ZZ[t]` with
$`Q(0) = 1`. Every step of this chain is elementary; the only geometric
input is the compactly-supported trace formula.
:::

:::theorem "W-rationality-reduced" (parent := "grp-final") (uses := "W-rationality") (tags := "elementary-missing") (effort := "small")
Reduced integral presentation: there exist *unique* coprime
$`A, B \in \ZZ[t]` with $`A(0) = B(0) = 1` and $`Z \cdot B = A` in
$`\QQ[\![t]\!]`.
:::

:::proof "W-rationality-reduced" (uses := "LA-gauss-normalized, LA-reduced-fraction-unique")
Divide the presentation of {bpref "W-rationality"}[] by the normalized
gcd: write $`P = G A`, $`Q = G B` with $`A, B \in \QQ[t]` coprime and
constant terms $`1` (possible since $`P(0) = Q(0) = 1` forces
$`G(0) \in \{\pm 1\}`, normalizable to $`1`); the normalized Gauss lemma
({bpref "LA-gauss-normalized"}[]) applied to $`P = G \cdot A` and
$`Q = G \cdot B` puts $`G, A, B` in $`\ZZ[t]`. Uniqueness is
{bpref "LA-reduced-fraction-unique"}[].
:::

# Endpoints

:::lemma_ "W-endpoints" (parent := "grp-final") (uses := "LA-charpoly-rev, DU-interface, DU-endpoint") (tags := "elementary-missing") (effort := "small")
Endpoint computation: under the endpoint normalization
({bpref "DU-endpoint"}[]: $`\dim H^0 = 1`, $`F_0 = 1`) and the similitude
pairing ({bpref "DU-interface"}[]),
$$`P_{F_0}(t) = 1 - t, \qquad P_{F_{2d}}(t) = 1 - q^d t.`
In particular $`b_0 = b_{2d} = 1`. The top endpoint is *not* an extra
axiom: it is forced by duality against $`H^0`.
:::

:::proof "W-endpoints" (uses := "DU-reciprocal-transport")
$`P_{F_0} = \det(1 - t \cdot 1) = 1 - t` on the one-dimensional $`H^0`.
The pairing $`\varphi_0 \colon H^0 \times H^{2d} \to K` is perfect, so
$`\dim H^{2d} = \dim H^0 = 1`; by the similitude transport
({bpref "DU-reciprocal-transport"}[]) $`F_{2d}` corresponds to
$`q^d (F_0^{-1})^\vee = q^d` on the one-dimensional dual, so
$`P_{F_{2d}} = 1 - q^d t`. (This matches the normalization tests
{bpref "Z-normalization-tests"}[] for $`\mathbb{P}^1`, $`d = 1`.)
:::

# The functional equation

:::theorem "W-functional-equation" (parent := "grp-final") (uses := "Z-zeta-series, Z-fe-predicate, DU-interface") (tags := "elementary-missing") (effort := "medium") (priority := "high")
Functional equation. Under the interface hypotheses (trace data and
similitude pairings with multiplier $`q^d`, middle pairing
$`(-1)^d`-symmetric, endpoints), with $`b_i := \dim H^i` and
$`\chi := \sum_i (-1)^i b_i`:
1. root-multiset form: the family $`P_i := P_{F_i}` satisfies the
   predicate {bpref "Z-fe-predicate"}[] — $`\alpha \mapsto q^d/\alpha`
   sends the reciprocal-root multiset of $`P_i` to that of
   $`P_{2d-i}`, with multiplicity;
2. classical form: $`d\chi/2 \in \ZZ`, and
   $$`Z\bigl(X, 1/(q^d t)\bigr) = \varepsilon\, q^{d\chi/2}\, t^{\chi}\, Z(X, t)`
   as rational functions over $`\QQ`, where
   $`\varepsilon = (-1)^{\chi} \delta^{(-1)^d} \in \{\pm 1\}` and
   $`\delta = (\det F_d)\, q^{-d b_d/2}` satisfies $`\delta^2 = 1`.
The sign is thus *explicitly determined* by the determinant of the middle
Frobenius; the repository's final predicate records only the root-multiset
form, which carries no sign, and the classical form with its explicit
$`\varepsilon` is this separate node.
:::

:::proof "W-functional-equation" (uses := "W-factorization, DU-graded-fe, DU-reciprocal-transport, DU-sign-analysis, W-rationality-reduced")
Form 1 is the eigenvalue-multiset statement of the similitude transport
({bpref "DU-reciprocal-transport"}[]): the pairing identifies
$`F_{2d-i}` with $`q^d (F_i^{-1})^\vee`, whose eigenvalue multiset is
$`\{q^d/\alpha_j\}`; multiplicities are preserved because characteristic
polynomials are conjugation- and dual-invariant. Form 2 is the abstract
graded functional equation ({bpref "DU-graded-fe"}[]) applied to the
factorization ({bpref "W-factorization"}[]), with the determinant and
sign bookkeeping of {bpref "DU-sign-analysis"}[]; the resulting identity
holds in $`K(t)`, both sides lie in the subfield $`\QQ(t)` (by
{bpref "W-rationality-reduced"}[]), and $`\QQ(t) \to K(t)` is injective,
so it descends to $`\QQ`.
:::

:::lemma_ "W-fe-uniqueness" (parent := "grp-final") (uses := "Z-zeta-series") (tags := "elementary-missing") (effort := "small")
Uniqueness of functional-equation parameters: if a nonzero
$`Z \in \QQ(t)` satisfies two identities
$`Z(1/(q^d t)) = \varepsilon_j q^{d\chi_j/2} t^{\chi_j} Z(t)`
($`j = 1, 2`, $`\varepsilon_j \in \{\pm 1\}`, $`d\chi_j/2 \in \ZZ`), then
$`\chi_1 = \chi_2` and $`\varepsilon_1 = \varepsilon_2`.
:::

:::proof "W-fe-uniqueness"
Dividing the two identities gives
$`1 = (\varepsilon_1/\varepsilon_2) q^{d(\chi_1 - \chi_2)/2}
t^{\chi_1 - \chi_2}` in $`\QQ(t)`; a monomial equal to $`1` forces the
exponent $`\chi_1 - \chi_2 = 0` and then the constant
$`\varepsilon_1/\varepsilon_2 = 1` (as $`q^0 = 1`). Consequence: $`\chi`
and $`\varepsilon` are determined by $`Z` alone — one of the two
$`\ell`-independence statements that come for free
({bpref "W-ell-independence"}[]).
:::

# No cancellation and factor identification

:::lemma_ "W-no-cancellation" (parent := "grp-final") (uses := "LA-eigenvalue, COH-purity-input") (tags := "elementary-missing") (effort := "small") (priority := "high")
No cancellation: under universal purity
({bpref "COH-purity-input"}[]: eigenvalues on $`H^i` are universally
pure of weight $`i` relative to $`q`), for $`i \neq j` the polynomials
$`P_{F_i}` and $`P_{F_j}` have no common root in $`K`. Consequently
$`O = \prod_{\text{odd}} P_{F_i}` and
$`E = \prod_{\text{even}} P_{F_i}` are coprime in $`K[t]`.
:::

:::proof "W-no-cancellation" (uses := "WT-separation, LA-embedding-extension")
Fix one ring homomorphism $`\iota_0 \colon K \to \CC` — one exists by
{bpref "LA-embedding-extension"}[] applied to $`\QQ \subseteq K`. A
common root $`\rho` of $`P_{F_i}, P_{F_j}` is nonzero (constant terms
$`1`), and $`\alpha := \rho^{-1}` is then a common eigenvalue of $`F_i`
and $`F_j`; weight separation ({bpref "WT-separation"}[]) at $`\iota_0`
gives $`q^i = \|\iota_0\alpha\|^2 = q^j`, hence $`i = j` since
$`q \geq 2` — contradiction. Since $`K[t]` is a PID and the $`P_{F_i}`
split into linear factors over the algebraically closed $`K`, pairwise
absence of common roots gives coprimality of the parity products. This is
the *only* place a single embedding suffices; every later step needs the
full universal quantifier.
:::

:::theorem "W-factor-identification" (parent := "grp-final") (uses := "W-rationality-reduced, W-no-cancellation") (tags := "elementary-missing") (effort := "small") (priority := "high")
Factor identification: in $`K[t]`,
$$`O = A \quad\text{and}\quad E = B,`
where $`A, B` are the reduced integral numerator and denominator of
{bpref "W-rationality-reduced"}[] (images in $`K[t]`). Hence the
alternating determinant product over $`K` *is* the reduced integral
fraction — the bridge between the abstract data and arithmetic.
:::

:::proof "W-factor-identification" (uses := "W-factorization, LA-reduced-fraction-unique")
Over $`K` we have two presentations of the same element of $`K(t)`:
$`Z_K = O/E` with $`O, E` coprime ({bpref "W-no-cancellation"}[]) and
constant terms $`1`, and $`Z_K = A/B` with $`A, B` coprime over $`\QQ`,
hence still coprime over $`K` (Bézout persists,
{bpref "LA-reduced-fraction-unique"}[]), constant terms $`1`. Uniqueness
of reduced normalized fractions ({bpref "LA-reduced-fraction-unique"}[])
gives $`O = A`, $`E = B`.
:::

:::theorem "W-algebraicity" (parent := "grp-final") (uses := "W-factor-identification, LA-eigenvalue") (tags := "elementary-missing") (effort := "small")
Algebraicity of Frobenius eigenvalues: every eigenvalue of every $`F_i`
is algebraic over $`\QQ`; indeed it is a reciprocal root of $`A` or $`B
\in \ZZ[t]`, hence an *algebraic integer* (the reversal
$`t^{\deg} A(1/t)` is monic integral because $`A(0) = 1`).
:::

:::proof "W-algebraicity"
Immediate from {bpref "W-factor-identification"}[]: each eigenvalue is a
reciprocal root of $`O = A` or $`E = B`, which are integer polynomials
with constant coefficient $`1`. *Order matters*: algebraicity is a
*conclusion* at this point of the pipeline — no earlier node may assume
Frobenius eigenvalues are algebraic, and none does.
:::

# Descent of the factors to the integers

:::theorem "W-rational-coefficients" (parent := "grp-final") (uses := "W-factor-identification, LA-charpoly-rev") (tags := "elementary-missing") (effort := "medium")
Rationality of the factors: each $`P_{F_i}` lies in $`\QQ[t]`
(coefficientwise, under $`\QQ \subseteq K`).
:::

:::proof "W-rational-coefficients" (uses := "WT-aut-stability, LA-aut-fixed-field, COH-purity-input")
Let $`\sigma` be any ring automorphism of $`K`; it fixes $`\QQ`
pointwise. $`\sigma` transports the factorization
$`A = \prod_\alpha (1 - \alpha t)^{m_\alpha}` of the integer polynomial
$`A` in $`K[t]`, so it permutes the reciprocal-root multiset of $`A`
(with multiplicities), and likewise for $`B`. By Aut-stability of
universal weights ({bpref "WT-aut-stability"}[]) and universal purity
({bpref "COH-purity-input"}[]), $`\sigma` preserves each weight class;
by {bpref "W-no-cancellation"}[] the reciprocal-root multiset of
$`P_{F_i}` is exactly the weight-$`i` part of the multiset of $`A` (odd
$`i`) or $`B` (even $`i`). Hence $`\sigma` fixes that sub-multiset, and
therefore fixes each coefficient of $`P_{F_i}` (elementary symmetric
functions of a $`\sigma`-stable multiset). Since this holds for *every*
automorphism, the coefficients lie in the fixed field of
$`\operatorname{Aut}(K)`, which is $`\QQ` by
{bpref "LA-aut-fixed-field"}[]. This is the step that genuinely needs
the universal quantifier over $`\iota` inside universal purity: weight
classes must be stable under *all* automorphisms.
:::

:::theorem "W-integral-coefficients" (parent := "grp-final") (uses := "W-rational-coefficients") (tags := "elementary-missing") (effort := "small")
Integrality of the factors: each $`P_i := P_{F_i}` lies in $`\ZZ[t]`,
with $`P_i(0) = 1`.
:::

:::proof "W-integral-coefficients" (uses := "LA-gauss-normalized, W-factor-identification")
$`A = \prod_{i \text{ odd}} P_i` is a factorization of the primitive
integer polynomial $`A` (constant term $`1`) into $`\QQ[t]`-polynomials
with constant term $`1` ({bpref "W-rational-coefficients"}[]); the
normalized Gauss lemma ({bpref "LA-gauss-normalized"}[]), applied
inductively splitting off one factor at a time, puts every factor in
$`\ZZ[t]`. Same for $`B` and the even factors.
:::

# The Riemann hypothesis

:::theorem "W-riemann-hypothesis" (parent := "grp-final") (uses := "W-integral-coefficients, Z-rh-predicate, COH-purity-input") (tags := "elementary-missing") (effort := "medium") (priority := "high")
Riemann hypothesis, complex-root form: the family
$`P \colon \operatorname{Fin}(2d+1) \to \ZZ[t]`,
$`P_i = P_{F_i}`, satisfies {bpref "Z-rh-predicate"}[]: every root
$`z \in \CC` of the image of $`P_i` in $`\CC[t]` has
$`\|z\| = q^{-i/2}`. Equivalently: every reciprocal root of $`P_i` is an
algebraic integer all of whose complex conjugates have absolute value
$`q^{i/2}`.
:::

:::proof "W-riemann-hypothesis" (uses := "W-factor-identification, LA-embedding-extension, W-algebraicity")
Let $`z` be a complex root of $`P_i` and $`\beta := z^{-1}` (nonzero
since $`P_i(0) = 1`). The minimal polynomial $`m \in \QQ[t]` of the
algebraic number $`\beta` ({bpref "W-algebraicity"}[]) divides the
reversal of $`P_i` in $`\QQ[t]`; since $`P_{F_i}` splits over $`K`, $`m`
has a root among the eigenvalues of $`F_i` — pick one, say $`\alpha`.
Both $`\alpha \in K` and $`\beta \in \CC` are roots of the
$`\QQ`-irreducible $`m`, so $`\alpha \mapsto \beta` defines a field
embedding $`\tau \colon \QQ(\alpha) \to \CC`. By
{bpref "LA-embedding-extension"}[] (using
$`\#K \leq 2^{\aleph_0}`), $`\tau` extends to
$`\iota \colon K \to \CC`; then $`\beta = \iota(\alpha)` and universal
purity ({bpref "COH-purity-input"}[]) gives
$`\|\beta\|^2 = q^i`, i.e. $`\|z\| = q^{-i/2}`. This is precisely why
purity must be quantified over all $`\iota`: the embedding is
manufactured from the root $`z`, not chosen in advance.
:::

# Independence of ℓ and the combined theorem

:::theorem "W-ell-independence" (parent := "grp-final") (uses := "W-integral-coefficients, W-riemann-hypothesis") (tags := "elementary-missing") (effort := "small")
Uniqueness and independence of $`\ell`: the family $`(P_0, \dots,
P_{2d})` is uniquely determined by $`(Z, q, d)` among families of
normalized integer polynomials satisfying factorization and the
root-modulus condition. Consequently any two cohomological realizations —
in particular any two primes $`\ell, \ell' \neq p` — produce the *same*
polynomials, the same Betti numbers $`b_i = \deg P_i`, the same
$`\chi`, and the same sign $`\varepsilon`.
:::

:::proof "W-ell-independence" (uses := "W-factor-identification, W-fe-uniqueness")
By {bpref "W-factor-identification"}[], $`A` and $`B` are determined by
$`Z` (uniqueness of the reduced presentation), and by
{bpref "W-riemann-hypothesis"}[] the root multiset of $`A` (resp. $`B`)
in $`\CC` is *partitioned by modulus*: the roots of modulus $`q^{-i/2}`
are exactly the roots of $`P_i`. A normalized divisor of a polynomial is
determined by its root sub-multiset, so
$`P_i` = the unique normalized divisor of $`A` (odd $`i`) or $`B` (even
$`i`) whose roots all have modulus $`q^{-i/2}` — a characterization
mentioning only $`(Z, q, i)`. The parameters $`\chi, \varepsilon` are
determined by $`Z` alone via {bpref "W-fe-uniqueness"}[].
:::

:::theorem "W-weil-conjectures" (parent := "grp-final") (uses := "Z-zeta-series, Z-weil-factorization, Z-fe-predicate, Z-rh-predicate") (lean := "AlgebraicGeometry.Scheme.weil_conjectures") (owner := "weil_project") (tags := "elementary-missing") (effort := "medium") (priority := "high")
The combined Weil conjectures (the repository's root statement): for
$`X` smooth, projective, geometrically integral of pure dimension $`d`
over the finite field $`k` with $`q` elements, there exists
$`P \colon \operatorname{Fin}(2d+1) \to \ZZ[t]` with
`IsWeilFactorization q d Z P`, `WeilFunctionalEquation q d P`, and
`WeilRiemannHypothesis q d P`.
:::

:::proof "W-weil-conjectures" (uses := "COH-instantiation, W-factorization, W-rationality-reduced, W-endpoints, W-integral-coefficients, W-functional-equation, W-riemann-hypothesis, W-factor-identification")
Instantiate the abstract package for $`X`
({bpref "COH-instantiation"}[] — until the realization chapters are
formalized this is the axiom boundary AX1–AX4). Take
$`P_i := P_{F_i}`, integral by {bpref "W-integral-coefficients"}[] with
constant coefficient $`1`. `IsWeilFactorization`: normalization is
built in; endpoints are {bpref "W-endpoints"}[]; the product identity
$`Z \cdot \prod_{\text{even}} P_i = \prod_{\text{odd}} P_i` in
$`\QQ[\![t]\!]` is {bpref "W-factorization"}[] combined with
{bpref "W-factor-identification"}[] (the identity holds in
$`K[\![t]\!]` and all series involved have rational coefficients, so it
descends by injectivity of $`\QQ[\![t]\!] \to K[\![t]\!]`).
`WeilFunctionalEquation` is form 1 of
{bpref "W-functional-equation"}[]. `WeilRiemannHypothesis` is
{bpref "W-riemann-hypothesis"}[]. (Uniqueness — hence independence of
$`\ell` — is the separate node {bpref "W-ell-independence"}[]; the
repository predicate asserts existence only.)
:::
