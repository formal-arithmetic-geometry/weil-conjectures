import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Elementary foundations" =>

This chapter holds the elementary toolkit of Layer I: formal power-series
calculus, the rationality toolkit (Hankel, Fatou, Gauss), and the
field-theoretic leaves used by the descent and Riemann-hypothesis pipeline.
Nothing here mentions Frobenius modules or geometry; every node is either
verified Mathlib infrastructure or elementary mathematics that can be
formalized directly.

:::group "grp-foundations"
Formal power series, the rationality toolkit, and field-theoretic leaves.
:::

# Formal exponential and logarithm

:::definition "ML-power-series-exp" (parent := "grp-foundations") (lean := "PowerSeries.exp") (tags := "mathlib")
The formal exponential $`\exp(t) = \sum_{n \geq 0} t^n/n! \in A[\![t]\!]`
over a $`\QQ`-algebra $`A`. Mathlib provides it as `PowerSeries.exp` with
the coefficient formula (`coeff_exp`), constant coefficient $`1`, behaviour
under ring maps (`map_exp`), and the characterization by
$`\exp' = \exp` with constant term $`1`
(`exp_unique_of_derivative_eq_self`). The repository's zeta function is
*defined* by substituting into this series.
:::

:::definition "ML-power-series-log" (parent := "grp-foundations") (lean := "PowerSeries.logOf") (tags := "mathlib")
The formal logarithm: `PowerSeries.log` is
$`\log(1+t) = \sum_{n \geq 1} (-1)^{n-1} t^n/n`, and
`PowerSeries.logOf f` is $`\log` substituted at $`f - 1`, defined for
$`f` with constant coefficient $`1`. Mathlib provides the definitions,
coefficient formulas, and the derivative computation (`deriv_log`).
:::

:::lemma_ "LA-exp-log-iso" (parent := "grp-foundations") (uses := "ML-power-series-exp, ML-power-series-log") (tags := "elementary-missing") (effort := "medium")
Let $`R` be a commutative $`\QQ`-algebra. Substitution into $`\exp` and
$`\operatorname{logOf}` are mutually inverse *group isomorphisms*
$$`\exp \colon (tR[\![t]\!], +) \xrightarrow{\ \sim\ } (1 + tR[\![t]\!], \times), \qquad \operatorname{logOf} \colon (1 + tR[\![t]\!], \times) \xrightarrow{\ \sim\ } (tR[\![t]\!], +).`
In particular $`\exp(a + b) = \exp(a)\exp(b)` for
$`a, b \in tR[\![t]\!]`, $`\operatorname{logOf}(fg) =
\operatorname{logOf} f + \operatorname{logOf} g` for
$`f, g \in 1 + tR[\![t]\!]`, and integer powers pass through as integer
multiples.
:::

:::proof "LA-exp-log-iso"
All identities are between power series with constant-term normalization,
so they can be proved by the *logarithmic-derivative characterization*: a
series $`f \in 1 + tR[\![t]\!]` is uniquely determined by
$`f(0) = 1` together with $`f'/f` (equivalently by
$`t f' = g f` for given $`g`), because the coefficient of $`t^n` in
$`tf' - gf` determines $`f_n` recursively from $`f_0, \dots, f_{n-1}`
(the coefficient of $`f_n` is the nonzero scalar $`n` — this is where
$`\QQ \subseteq R` is used). Both $`\exp(a)\exp(b)` and $`\exp(a+b)` have
constant term $`1` and logarithmic derivative $`a' + b'`, hence agree; the
same method gives $`\operatorname{logOf}(\exp a) = a` and
$`\exp(\operatorname{logOf} f) = f` from the derivative computations
already in Mathlib (`derivative_exp`, `deriv_log`). Mathlib contains the
definitions and derivative lemmas but not this homomorphism package; the
missing part is elementary coefficient induction. This is exactly the
uniqueness device the repository already uses for the Euler product
({bpref "Z-log-derivative"}[]), so the formalization can reuse
`PowerSeries.coeff_eq_of_X_mul_derivative_eq`.
:::

:::lemma_ "LA-locally-finite-products" (parent := "grp-foundations") (uses := "ML-power-series-log") (tags := "elementary-missing") (effort := "small")
Let $`(f_\lambda)_{\lambda \in \Lambda}` be a family in
$`1 + tR[\![t]\!]` such that for every $`N` only finitely many
$`f_\lambda` differ from $`1` modulo $`t^{N+1}`. Then the product
$`\prod_\lambda f_\lambda` is a well-defined element of
$`1 + tR[\![t]\!]` (each coefficient is a finite computation), and
$`\operatorname{logOf}\prod_\lambda f_\lambda =
\sum_\lambda \operatorname{logOf} f_\lambda`, the right side being
$`t`-adically locally finite in the same sense.
:::

:::proof "LA-locally-finite-products"
Modulo $`t^{N+1}` the product reduces to the finite product of the finitely
many factors that are $`\neq 1` mod $`t^{N+1}`, and these truncations are
compatible as $`N` grows, so the coefficientwise limit exists; the
logarithm identity follows from the finite case
({bpref "LA-exp-log-iso"}[]) applied modulo each $`t^{N+1}`. The
repository's Euler-product infrastructure
(`PowerSeries.coeff_tprod_inv_one_sub_X_pow` and the `Multipliable`
apparatus in `EulerProductAux`) already implements the special case of
factors $`(1 - t^{d})^{-1}` via `tprod` in the coefficientwise topology;
this node is the mild generalization the abstract layer consumes.
:::

# The rationality toolkit

:::theorem "LA-linear-recurrence-hankel" (parent := "grp-foundations") (tags := "elementary-missing, infrastructure") (effort := "large")
Let $`K` be a field and $`f = \sum_{n \geq 0} a_n t^n \in K[\![t]\!]`. The
following are equivalent:
1. $`f = A/B` in $`K[\![t]\!]` for polynomials $`A, B \in K[t]` with
   $`B(0) \neq 0`;
2. the coefficients satisfy an eventual linear recurrence: there are
   $`r, N` and $`b_1, \dots, b_r \in K` with
   $`a_n + b_1 a_{n-1} + \dots + b_r a_{n-r} = 0` for all $`n \geq N`;
3. the shifted sequences $`S^m a := (a_{n+m})_n`, $`m \geq 0`, span a
   finite-dimensional subspace of $`K^{\mathbb{N}}`;
4. the infinite Hankel matrix $`(a_{i+j})_{i,j \geq 0}` has finite rank
   (supremum of the ranks of its finite submatrices).
:::

:::proof "LA-linear-recurrence-hankel" (uses := "ML-cayley-hamilton")
(1 ⇒ 2): write $`B = \sum b_i t^i` with $`b_0 \neq 0`; the coefficient of
$`t^n` in $`Bf = A` vanishes for $`n > \deg A`, which after dividing by
$`b_0` is the recurrence.
(2 ⇒ 3): the tails $`(S^m a)_{m \geq N}` lie in the span of
$`S^N a, \dots, S^{N+r-1} a` by induction using the recurrence; adding the
finitely many heads $`S^0a, \dots, S^{N-1}a` keeps the span
finite-dimensional.
(3 ⇔ 4): the columns of the Hankel matrix *are* the shifted sequences, and
the rank of an infinite matrix equals the dimension of its column span,
computed as the supremum of finite minors.
(3 ⇒ 1): let $`V` be the (finite-dimensional) shift span. The shift
operator $`S` maps $`V` to itself; by Cayley–Hamilton
({bpref "ML-cayley-hamilton"}[]) applied to $`S|_V`, there is a monic
polynomial $`\chi(S)` annihilating $`V`, i.e. a global linear recurrence
valid from $`n = 0`. If $`\chi(t) = t^r + c_1 t^{r-1} + \dots + c_r`, set
$`B(t) := 1 + c_1 t + \dots + c_r t^r` (the reversal); then $`Bf` has
vanishing coefficients beyond degree $`r - 1`, so $`A := Bf` is a
polynomial and $`B(0) = 1 \neq 0`.
Design note: represent the Hankel matrix as `Matrix ℕ ℕ K` and define its
rank as the supremum of finite-minor ranks; Mathlib has no Hankel
infrastructure, so this node is genuinely new but self-contained.
:::

:::theorem "ML-cayley-hamilton" (parent := "grp-foundations") (lean := "Matrix.aeval_self_charpoly") (tags := "mathlib")
Cayley–Hamilton over an arbitrary commutative ring: for a square matrix
$`M` over $`R`, evaluating its characteristic polynomial at $`M` gives
$`0`. Verified in Mathlib as `Matrix.aeval_self_charpoly`. Used twice in
this blueprint: over a field for the Hankel argument
({bpref "LA-linear-recurrence-hankel"}[]) and over $`\ZZ` for the integral
Fatou lemma ({bpref "LA-fatou"}[]) — the commutative-ring generality is
essential for the latter.
:::

:::lemma_ "LA-rank-descent" (parent := "grp-foundations") (tags := "elementary-missing") (effort := "medium")
Let $`K \subseteq L` be a field extension and $`M` a (possibly infinite)
matrix with entries in $`K`. Then $`M` has the same rank over $`K` as over
$`L`. Consequently $`K[\![t]\!] \cap L(t) = K(t)`: a power series with
coefficients in $`K` that is rational over $`L` is already rational over
$`K`.
:::

:::proof "LA-rank-descent" (uses := "LA-linear-recurrence-hankel")
"Rank $`\geq r`" means some $`r \times r` minor is nonzero; that minor is
an element of $`K`, and a nonzero element of $`K` stays nonzero in $`L` —
so the rank is insensitive to extension in both directions (a
$`K`-linearly independent family stays $`L`-independent by the minor
criterion). For the consequence, apply
{bpref "LA-linear-recurrence-hankel"}[] twice: rationality over $`L` gives
finite Hankel rank over $`L`, the entries lie in $`K`, so the rank is
finite over $`K`, giving rationality over $`K`. *Warning recorded from
the lecture notes:* do not attempt to descend denominators by averaging
over automorphisms — no finite Galois group is available for
$`\Qlbar/\QQ`; the minor criterion is the correct device.
:::

:::theorem "LA-fatou" (parent := "grp-foundations") (tags := "elementary-missing, infrastructure") (effort := "large")
Integral Fatou lemma: if $`f \in \ZZ[\![t]\!]` is rational over $`\QQ`
(that is, $`f \in \QQ(t) \cap \ZZ[\![t]\!]`), then $`f = A/B` in
$`\QQ[\![t]\!]` for polynomials $`A, B \in \ZZ[t]` with $`B(0) = 1` and
$`A(0) = a_0`.
:::

:::proof "LA-fatou" (uses := "LA-linear-recurrence-hankel, ML-cayley-hamilton")
Let $`V \subseteq \QQ^{\mathbb{N}}` be the shift span of the coefficient
sequence $`a`, finite-dimensional by
{bpref "LA-linear-recurrence-hankel"}[]. *Finite-coordinate detection*:
the kernels $`V \cap \ker \pi_N` of the truncation maps
$`\pi_N \colon V \to \QQ^N` form a descending chain of subspaces of the
finite-dimensional $`V` with intersection $`0`, so some $`\pi_N` is
injective on $`V`. Let $`M := \sum_{m \geq 0} \ZZ \cdot S^m a \subseteq V`
be the subgroup generated by *all* integral shifts (not an arbitrary
lattice — this is the point). Then $`\pi_N(M) \subseteq \ZZ^N` is a
finitely generated abelian group ($`\ZZ` Noetherian), so $`M` is finitely
generated, torsion-free, hence free of finite rank, and by construction
$`S(M) \subseteq M`. Cayley–Hamilton over $`\ZZ`
({bpref "ML-cayley-hamilton"}[]) for $`S|_M` (in a $`\ZZ`-basis of $`M`)
yields a *monic integral* recurrence valid from $`n = 0`; its reversal
$`B \in \ZZ[t]` has $`B(0) = 1` and $`A := Bf \in \ZZ[t]` by the
recurrence, with $`A(0) = B(0) a_0 = a_0`.
:::

:::lemma_ "ML-gauss-primitive" (parent := "grp-foundations") (lean := "Polynomial.IsPrimitive.mul") (tags := "mathlib")
Gauss's lemma on contents: over a GCD domain, the product of primitive
polynomials is primitive. Verified in Mathlib as
`Polynomial.IsPrimitive.mul`. This is the engine behind the normalized
Gauss lemma below.
:::

:::lemma_ "LA-gauss-normalized" (parent := "grp-foundations") (uses := "ML-gauss-primitive") (tags := "elementary-missing") (effort := "small")
Normalized Gauss lemma: let $`C \in \ZZ[t]` with $`C(0) = 1`, and suppose
$`C = P Q` with $`P, Q \in \QQ[t]` and $`P(0) = Q(0) = 1`. Then
$`P, Q \in \ZZ[t]`.
:::

:::proof "LA-gauss-normalized"
$`C` is primitive (its constant coefficient is $`1`). Write
$`P = a P_0`, $`Q = b Q_0` with $`a, b \in \QQ_{> 0} \cdot \{\pm 1\}` and
$`P_0, Q_0 \in \ZZ[t]` primitive. Then $`C = (ab) P_0 Q_0` with
$`P_0 Q_0` primitive by {bpref "ML-gauss-primitive"}[]; comparing contents
of the two sides gives $`ab = \pm 1`, and since
$`1 = C(0) = ab\, P_0(0) Q_0(0)` with $`P_0(0), Q_0(0) \in \ZZ`, all four
factors are $`\pm 1`; adjusting signs into $`P_0, Q_0` gives $`a = b = 1`
after the normalization $`P(0) = Q(0) = 1`, so $`P = P_0 \in \ZZ[t]` and
likewise for $`Q`. Applied inductively (splitting off one factor against
the product of the rest), this upgrades any factorization of a normalized
integer polynomial into normalized rational factors to integer factors —
the form consumed by {bpref "W-integral-coefficients"}[].
:::

:::lemma_ "LA-reduced-fraction-unique" (parent := "grp-foundations") (tags := "elementary-missing") (effort := "small")
Uniqueness of reduced normalized fractions: over a field $`K`, if
$`A/B = A'/B'` in $`K(t)` with $`A, B` coprime, $`A', B'` coprime, and
$`A(0) = B(0) = A'(0) = B'(0) = 1`, then $`A = A'` and $`B = B'`.
Moreover, coprimality is stable under field extension: if
$`A, B \in \QQ[t]` are coprime, their images in $`K[t]` are coprime for
every field $`K \supseteq \QQ`.
:::

:::proof "LA-reduced-fraction-unique"
Cross-multiplying, $`A B' = A' B` in $`K[t]`; coprimality of $`(A, B)`
gives $`A \mid A'` and coprimality of $`(A', B')` gives $`A' \mid A`, so
$`A` and $`A'` are associates; the constant-term normalization fixes the
unit to be $`1`. For stability: a Bézout identity $`1 = uA + vB` in
$`\QQ[t]` remains valid in $`K[t]`. This tiny lemma is load-bearing: it is
what identifies the abstract determinant factors with the integral
numerator and denominator in {bpref "W-factor-identification"}[].
:::

# Field-theoretic leaves

:::definition "ML-alg-closed-classification" (parent := "grp-foundations") (lean := "IsAlgClosed.equivOfTranscendenceBasis") (tags := "mathlib")
Mathlib's classification toolkit for algebraically closed fields: an
isomorphism of algebraically closed fields is induced by a bijection of
transcendence bases over a common prime field
(`IsAlgClosed.equivOfTranscendenceBasis`), together with the isomorphism
extension theorem for algebraic closures (`IsAlgClosed.lift` and the
`IntermediateField` lifting API). These are the raw materials for the two
embedding lemmas below.
:::

:::lemma_ "LA-aut-fixed-field" (parent := "grp-foundations") (uses := "ML-alg-closed-classification") (tags := "elementary-missing") (effort := "medium")
Let $`K` be an algebraically closed field of characteristic $`0`. Every
ring automorphism of $`K` fixes $`\QQ` pointwise, and the fixed field of
the full automorphism group $`\operatorname{Aut}(K)` is exactly $`\QQ`:
for every $`x \in K \setminus \QQ` there is an automorphism $`\sigma` of
$`K` with $`\sigma x \neq x`.
:::

:::proof "LA-aut-fixed-field"
Ring homomorphisms fix $`\ZZ` and hence $`\QQ` in characteristic $`0`. For
the converse, take $`x \notin \QQ`. If $`x` is algebraic over $`\QQ`, its
minimal polynomial has degree $`\geq 2`, so it has a second root
$`y \neq x` in $`K`; the isomorphism $`\QQ(x) \cong \QQ(y)` sending
$`x \mapsto y` extends to the algebraic closure $`\overline{\QQ} \subseteq K`
of $`\QQ` (isomorphism extension), and further to $`K` by extending along
a transcendence basis of $`K` over $`\overline{\QQ}` (identity on the
basis) and using {bpref "ML-alg-closed-classification"}[] to close up
algebraically. If $`x` is transcendental, choose a transcendence basis
$`T \ni x` of $`K` over $`\QQ`; the self-bijection of $`T` fixing
everything and the field map determined by $`x \mapsto x + 1` extends to
an automorphism of $`\QQ(T)` and then of its algebraic closure $`K`.
:::

:::lemma_ "LA-embedding-extension" (parent := "grp-foundations") (uses := "ML-alg-closed-classification") (tags := "elementary-missing") (effort := "medium")
Extension of complex embeddings: let $`K` be an algebraically closed field
of characteristic $`0` with $`\#K \leq 2^{\aleph_0}`, let $`E \subseteq K`
be a subfield and $`\tau \colon E \to \CC` a ring homomorphism. Then
$`\tau` extends to a ring homomorphism $`\iota \colon K \to \CC`. In
particular (taking $`E = \QQ`) the set of ring homomorphisms
$`K \to \CC` is nonempty.
:::

:::proof "LA-embedding-extension"
First extend $`\tau` to the relative algebraic closure $`\bar{E}` of $`E`
in $`K` by the isomorphism-extension theorem (the image lands in $`\CC`
because $`\CC` is algebraically closed). Choose a transcendence basis
$`T` of $`K` over $`\bar{E}`; since
$`\#T \leq \#K \leq 2^{\aleph_0}` and $`\CC` has transcendence degree
$`2^{\aleph_0}` over any countable subfield, there is an injection of
$`T` into a transcendence basis of $`\CC` over the image of $`\bar E`;
extend to $`\bar{E}(T)` and finally to its algebraic closure $`K` (again
landing in the algebraically closed $`\CC`). The cardinality hypothesis is
the only reason the bound $`\#K \leq 2^{\aleph_0}` appears in the
abstract package.
:::

:::lemma_ "LA-qlbar-cardinality" (parent := "grp-foundations") (tags := "elementary-missing") (effort := "small")
$`\#\Qlbar = 2^{\aleph_0}`. Consequently the abstract cardinality
hypothesis holds for $`K = \Qlbar`, and by
{bpref "LA-embedding-extension"}[] there exist ring homomorphisms
$`\Qlbar \to \CC` (necessarily discontinuous and highly non-canonical;
nothing in this project ever chooses a preferred one).
:::

:::proof "LA-qlbar-cardinality"
$`\#\ZZ_\ell = 2^{\aleph_0}` (Cantor: $`\ell`-adic digit expansions), so
$`\#\Ql = 2^{\aleph_0}`; an algebraic closure of an infinite field has the
same cardinality (it is a countable union of finite-dimensional
extensions of finite subextensions, bounded by
$`\aleph_0 \cdot \#\Ql`), and $`2^{\aleph_0}` is an upper bound by the
same counting. Verification task recorded: check whether Mathlib's
`Padic`/cardinality API already contains $`\#\ZZ_\ell = 2^{\aleph_0}`; if
not it is a short exercise with `Cardinal.mk_congr` on digit expansions.
:::
