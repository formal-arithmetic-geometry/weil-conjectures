import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Duality" =>

Poincaré duality enters the final assembly in a deliberately minimal form:
perfect similitude pairings between complementary degrees with multiplier
$`q^d` and one sign constraint in the middle degree (interface AX2), plus
the endpoint normalization (AX3). This chapter contains the complete
linear-algebra derivation of the functional equation — every power of
$`q` and $`t` and every sign accounted for — and the realization nodes:
trace map, Tate-twist action, cup-product pairing, and the duality
theorems on varieties and curves.

:::group "grp-duality"
Similitude pairings, the reciprocal characteristic-polynomial identity,
the sign analysis, and Poincaré duality.
:::

# Interface statements

:::theorem "DU-interface" (parent := "grp-duality") (uses := "LA-frobenius-module") (tags := "temporary-axiom, deep-input") (effort := "large") (priority := "high")
Similitude pairings (interface hypothesis AX2). In the situation of
{bpref "TR-interface-proper"}[] ($`X` smooth projective of pure
dimension $`d`, spaces $`H^i` with geometric Frobenius $`F_i`), there
are perfect $`K`-bilinear pairings
$$`\varphi_i \colon H^i \times H^{2d-i} \to K \qquad (0 \leq i \leq 2d)`
with the similitude property
$`\varphi_i(F_i x,\, F_{2d-i} y) = q^d\, \varphi_i(x, y)`, and
$`\varphi_d(x, y) = (-1)^d \varphi_d(y, x)` (symmetric middle pairing
for $`d` even, alternating for $`d` odd). The multiplier is $`q^{+d}` —
not $`q^{-d}` — because the pairing takes values in the Tate twist
$`\Ql(-d)`, on which geometric Frobenius acts by $`q^d`
({bpref "DU-tate-twist-action"}[]).
:::

:::proof "DU-interface" (uses := "DU-poincare-duality, DU-cup-pairing, DU-tate-twist-action")
Interface axiom until realized. Realization: untwist the perfect
Galois-equivariant pairing
$`H^i \times H^{2d-i} \to \Ql(-d)` of
{bpref "DU-poincare-duality"}[]/{bpref "DU-cup-pairing"}[] by choosing
the target identification $`\Ql(-d) \otimes \Qlbar \cong \Qlbar`; the
equivariance $`\varphi(Fx, Fy) = F \cdot \varphi(x, y)` then reads
$`\varphi(Fx, Fy) = q^d \varphi(x, y)` by
{bpref "DU-tate-twist-action"}[]. The sign in middle degree is
graded-commutativity of the cup product:
$`x \smile y = (-1)^{i(2d - i)} y \smile x`, and for $`i = d` the sign
is $`(-1)^{d^2} = (-1)^d`.
:::

:::theorem "DU-endpoint" (parent := "grp-duality") (uses := "LA-frobenius-module") (tags := "temporary-axiom") (effort := "medium")
Endpoint normalization (interface hypothesis AX3): $`\dim H^0 = 1` and
$`F_0 = \operatorname{id}`. This is where geometric integrality
(connectedness of $`X_{\Fqbar}`) enters — and the *only* place.
:::

:::proof "DU-endpoint" (uses := "ET-h0-computation")
Interface axiom until realized by {bpref "ET-h0-computation"}[]:
$`H^0(X_{\Fqbar}, \Ql) = \Ql^{\pi_0(X_{\Fqbar})}` with Frobenius
permuting the factors as it permutes components; geometric
connectedness gives one component, fixed, with trivial action. Without
geometric connectedness $`P_0` would be the permutation factor
$`\det(1 - tF \mid \Ql^{\pi_0})` and the endpoints of the final theorem
would change accordingly; the blueprint fixes the geometrically integral
case, matching the repository statement.
:::

# The reciprocal identity, step by step

:::lemma_ "DU-reciprocal-transport" (parent := "grp-duality") (uses := "LA-frobenius-module") (tags := "elementary-missing") (effort := "small")
Similitude transport. Let $`V, W` be finite-dimensional $`K`-spaces,
$`\langle\,,\rangle \colon V \times W \to K` a perfect pairing, $`u, v`
automorphisms with $`\langle ux, vy\rangle = \mu \langle x, y\rangle`
for a unit $`\mu \in K^\times`. Then: (i) $`\dim V = \dim W =: r`;
(ii) under the induced identification $`W \cong V^\vee`
($`y \mapsto \langle -, y\rangle`), $`v` corresponds to
$`\mu\,(u^{-1})^\vee`; (iii) $`\det v = \mu^r / \det u`; (iv) over
algebraically closed $`K`, the eigenvalue multiset of $`v` is
$`\{\mu/\alpha_1, \dots, \mu/\alpha_r\}` where
$`\{\alpha_j\}` is that of $`u`.
:::

:::proof "DU-reciprocal-transport"
(i) is perfectness. (ii): from the similitude relation,
$`\langle x, vy \rangle = \mu \langle u^{-1}x, y\rangle`, i.e.
$`\xi(vy) = \mu\, (u^{-1})^\vee(\xi(y))` for the identification $`\xi`.
(iii): determinants in (ii), $`\det((u^{-1})^\vee) = (\det u)^{-1}` and
the scalar $`\mu` contributes $`\mu^r`. (iv): the eigenvalues of
$`(u^{-1})^\vee` are the $`\alpha_j^{-1}` with the same multiplicities
(dual and inverse preserve characteristic-polynomial factorizations),
and scaling by $`\mu` scales eigenvalues.
:::

:::lemma_ "DU-det-identity" (parent := "grp-duality") (uses := "LA-charpoly-rev") (tags := "elementary-missing") (effort := "small")
Determinant reversal identity: for an automorphism $`w` of an
$`r`-dimensional space and a unit $`s`,
$$`\det(1 - s\,w) = (-s)^{r}\, (\det w)\, \det\bigl(1 - s^{-1} w^{-1}\bigr)`
in $`K[s, s^{-1}]` (equivalently, as an identity of Laurent
polynomials after substituting any unit for $`s`).
:::

:::proof "DU-det-identity"
Factor the endomorphism: $`1 - s w = (-s w)(1 - s^{-1} w^{-1})`, an
identity of endomorphisms valid whenever $`s` and $`w` are invertible;
take determinants, using $`\det(-s w) = (-s)^r \det w`. This two-line
identity replaces all eigenvalue-multiset manipulations in the
functional equation: no multiset bookkeeping is ever needed.
:::

:::lemma_ "DU-reciprocal-charpoly" (parent := "grp-duality") (uses := "DU-reciprocal-transport, LA-charpoly-rev") (tags := "elementary-missing") (effort := "small")
Reciprocal characteristic polynomials of a similitude pair: in the
situation of {bpref "DU-reciprocal-transport"}[], with
$`P_u(T) = \charrev{u}` (variable $`T`),
$$`P_v\bigl((\mu T)^{-1}\bigr) = (-1)^{r}\, T^{-r} \mu^{-r}\, (\det u)\, \cdot (\det u)^{-2} \cdot \dots`
— precisely:
$$`P_v\bigl(\mu^{-1}T^{-1}\bigr) = (-1)^r\, T^{-r}\, (\det u)^{-1}\, P_u(T)`
in $`K[T, T^{-1}]`.
:::

:::proof "DU-reciprocal-charpoly" (uses := "DU-det-identity, LA-charpoly-rev-props")
By transport (ii), $`P_v(s) = \det(1 - s\,\mu (u^{-1})^\vee) =
\det(1 - s \mu u^{-1})` (dual invariance,
{bpref "LA-charpoly-rev-props"}[](v)). Apply
{bpref "DU-det-identity"}[] with $`w = u^{-1}` and the unit
$`s\mu`: $`\det(1 - s\mu u^{-1}) = (-s\mu)^r (\det u)^{-1}
\det(1 - (s\mu)^{-1} u)`. Substitute $`s = \mu^{-1}T^{-1}`: the prefactor
becomes $`(-T^{-1})^r (\det u)^{-1}` and the last determinant is
$`P_u(T)`.
:::

# Euler characteristic, parity, and the sign

:::lemma_ "DU-euler-char" (parent := "grp-duality") (uses := "DU-interface") (tags := "elementary-missing") (effort := "small")
Betti symmetry and integrality of the exponent: with
$`b_i = \dim H^i` and $`\chi = \sum_{i=0}^{2d} (-1)^i b_i`: (i)
$`b_i = b_{2d-i}` (perfect pairings); (ii)
$`\chi = 2\sum_{i < d} (-1)^i b_i + (-1)^d b_d`; (iii) $`d\chi/2 \in
\ZZ` — if $`d` is even this is clear, and if $`d` is odd then $`b_d` is
even (by {bpref "DU-alternating-even"}[]) so $`\chi` is even.
:::

:::proof "DU-euler-char" (uses := "DU-alternating-even")
(i) is {bpref "DU-reciprocal-transport"}[](i) applied to each
$`\varphi_i`. (ii) pairs the terms $`i` and $`2d - i` using (i). (iii)
as stated; for odd $`d` the middle form is a perfect alternating form,
forcing $`2 \mid b_d`, hence $`2 \mid \chi` by (ii).
:::

:::lemma_ "DU-alternating-even" (parent := "grp-duality") (tags := "elementary-missing") (effort := "small")
A finite-dimensional vector space (over a field of characteristic
$`\neq 2`) carrying a perfect alternating bilinear form has even
dimension.
:::

:::proof "DU-alternating-even"
Induct: pick $`x \neq 0`; perfectness gives $`y` with
$`\langle x, y\rangle = 1`; the plane $`\langle x, y\rangle_K` is
nondegenerate for the form (its Gram matrix is
$`\begin{pmatrix} 0 & 1 \\ -1 & 0\end{pmatrix}`), so the space splits as
the plane plus its perpendicular, which again carries a perfect
alternating form; recurse. (Equivalently: a symplectic basis exists.
Mathlib verification task: check `LinearAlgebra/SymplecticGroup` or the
`BilinForm` API for an existing even-dimensionality lemma before
formalizing.)
:::

:::lemma_ "DU-determinant-pairing" (parent := "grp-duality") (uses := "DU-interface") (tags := "elementary-missing") (effort := "small")
Determinant constraints from duality: with $`D_i := \det F_i` and
$`\mu = q^d`: (i) $`D_i \cdot D_{2d-i} = q^{d b_i}` for all $`i`; (ii)
in the middle degree, $`D_d^2 = q^{d b_d}`.
:::

:::proof "DU-determinant-pairing" (uses := "DU-reciprocal-transport")
(i) is {bpref "DU-reciprocal-transport"}[](iii) for the pair
$`(F_i, F_{2d-i})`. (ii) is (i) at $`i = d` — the middle pairing is a
similitude of $`(H^d, F_d)` with itself.
:::

:::theorem "DU-sign-analysis" (parent := "grp-duality") (uses := "DU-determinant-pairing, DU-euler-char") (tags := "elementary-missing") (effort := "medium")
The sign of the functional equation. Set
$`\delta := D_d \, q^{-d b_d / 2}` (well-defined:
$`d b_d` is even by {bpref "DU-alternating-even"}[] when $`d` is odd,
trivially when $`d` is even). Then:
1. $`\delta^2 = 1`, i.e. $`\delta \in \{\pm 1\}` — by
   {bpref "DU-determinant-pairing"}[](ii);
2. $`\prod_{i=0}^{2d} D_i^{(-1)^i} = \delta^{(-1)^d} \, q^{d\chi/2}`;
3. *define* $`\varepsilon := (-1)^{\chi}\, \delta^{(-1)^d} \in
   \{\pm 1\}`.
The theorem {bpref "DU-graded-fe"}[] then *proves* that this
$`\varepsilon` is the sign of the functional equation — the logical
order is (1)(2)(3) here, then the substitution computation there;
nothing circulates. So $`\varepsilon` is explicitly computable from
$`\det F_d`: for example $`\varepsilon = +1` whenever $`\chi` is even
and $`\det F_d = +q^{d b_d/2}`. The final combined theorem only needs
$`\varepsilon \in \{\pm 1\}`, but nothing is left as an unexplained
$`\pm`.
:::

:::proof "DU-sign-analysis"
For 1: {bpref "DU-determinant-pairing"}[](ii) gives
$`D_d^2 = q^{d b_d}`, so $`\delta^2 = D_d^2 q^{-d b_d} = 1`. For 2:
pair off $`i < d` with $`2d - i`:
$`D_i^{(-1)^i} D_{2d-i}^{(-1)^{2d-i}} = (D_i D_{2d-i})^{(-1)^i} =
q^{d b_i (-1)^i}` by {bpref "DU-determinant-pairing"}[](i) (the
exponents agree since $`(-1)^{2d-i} = (-1)^i`); the middle contributes
$`D_d^{(-1)^d} = (\delta\, q^{d b_d/2})^{(-1)^d}` — using
$`\delta = \delta^{-1}` when $`d` is odd. Multiplying:
$`\prod_i D_i^{(-1)^i} = q^{d \sum_{i<d} (-1)^i b_i} \cdot
\delta^{(-1)^d} q^{(-1)^d d b_d / 2} = \delta^{(-1)^d} q^{d\chi/2}`
using {bpref "DU-euler-char"}[](ii). Item 3 is a definition. *No
Pfaffians*: one never needs to know *which* sign $`\delta` is, only
that $`\delta^2 = 1`; computing $`\delta` for a given $`X` amounts to
computing $`\det F_d`, which the blueprint does not need.
:::

:::theorem "DU-graded-fe" (parent := "grp-duality") (uses := "DU-interface, LA-charpoly-rev") (tags := "elementary-missing") (effort := "medium") (priority := "high")
Abstract graded functional equation. Given the similitude data of
{bpref "DU-interface"}[] with $`\mu = q^d`, set
$`Z_F(T) := \prod_{i=0}^{2d} P_{F_i}(T)^{(-1)^{i+1}} \in K(T)`. Then
$$`Z_F\bigl(q^{-d} T^{-1}\bigr) = \varepsilon\, q^{d\chi/2}\, T^{\chi}\, Z_F(T), \qquad \varepsilon = (-1)^{\chi}\,\delta^{(-1)^d} \in \{\pm 1\}.`
All conventions explicit: geometric Frobenius, multiplier $`q^{+d}`,
$`\chi = \sum (-1)^i b_i`, $`\delta = D_d q^{-db_d/2}`.
:::

:::proof "DU-graded-fe" (uses := "DU-reciprocal-charpoly, DU-sign-analysis, DU-euler-char")
Independent recomputation (audited): from
{bpref "DU-reciprocal-charpoly"}[] in the form
$`P_{F_i}\bigl(1/(q^d T)\bigr) = (-q^d T)^{-b_i}\, D_i\, P_{F_{2d-i}}(T)`
(the similitude pair $`(F_i, F_{2d-i})` with multiplier $`q^d`),
substitute into the product:
$`Z_F(q^{-d}T^{-1}) = \prod_i \bigl[(-q^dT)^{-b_i} D_i
P_{F_{2d-i}}(T)\bigr]^{(-1)^{i+1}}`. The three prefactor families:
$`\prod_i (-q^dT)^{-b_i(-1)^{i+1}} = (-q^dT)^{\chi} =
(-1)^{\chi} q^{d\chi} T^{\chi}`; the determinants give
$`\prod_i D_i^{(-1)^{i+1}} = \bigl(\prod_i D_i^{(-1)^i}\bigr)^{-1} =
\delta^{-(-1)^d} q^{-d\chi/2} = \delta^{(-1)^d} q^{-d\chi/2}` by
{bpref "DU-sign-analysis"}[](1)(2); re-indexing
$`i \mapsto 2d - i` (parity-preserving) turns the last family into
$`Z_F(T)`. Total:
$`Z_F(q^{-d}T^{-1}) = (-1)^{\chi}\delta^{(-1)^d} q^{d\chi - d\chi/2}
T^{\chi} Z_F(T) = \varepsilon\, q^{d\chi/2}\, T^{\chi}\, Z_F(T)`.
Sanity test $`\mathbb{P}^1` ($`d = 1`, $`b_0 = b_2 = 1`, $`b_1 = 0`,
$`\chi = 2`, $`H^1 = 0` so $`D_1 = 1`, $`\delta = 1`):
$`\varepsilon = (+1)(1) = +1` and indeed
$`Z(1/(qT)) = qT^2 Z(T)` for $`Z = ((1-T)(1-qT))^{-1}`.
:::

# Realization nodes

:::definition "DU-tate-twist-action" (parent := "grp-duality") (uses := "ET-tate-twist") (tags := "elementary-missing") (effort := "small")
Frobenius action on Tate objects: geometric Frobenius acts on
$`\Ql(1) = (\varprojlim \mu_{\ell^n}) \otimes \Ql` by the scalar
$`q^{-1}`, hence on $`\Ql(m)` by $`q^{-m}` and on $`\Ql(-d)` by
$`q^{d}`. Derivation: arithmetic Frobenius $`\varphi \colon a \mapsto
a^q` sends an $`\ell^n`-th root of unity $`\zeta` to $`\zeta^q`, so it
acts on $`\varprojlim \mu_{\ell^n} \cong \ZZ_\ell` by multiplication by
$`q`; geometric Frobenius is its inverse. The weight of $`\Ql(m)` is
$`-2m` (its eigenvalue $`q^{-m}` has $`\|\iota(q^{-m})\|^2 =
q^{-2m}`). Pinned executably by {bpref "Z-normalization-tests"}[].
:::

:::theorem "DU-trace-map" (parent := "grp-duality") (uses := "ET-tate-twist") (tags := "deep-input, infrastructure") (effort := "large")
Trace map / top-degree normalization: for $`X` smooth of pure dimension
$`d` over an algebraically closed field, separated of finite type, a
canonical isomorphism
$`\operatorname{tr}_X \colon H_c^{2d}(X, \Ql(d)) \xrightarrow{\sim} \Ql`,
compatible with open immersions (sum over components), étale maps, and —
over $`\Fqbar` with descent data — Galois action (so that
$`H_c^{2d}(X, \Ql) \cong \Ql(-d)` equivariantly). Normalization: for
$`X = \mathbb{A}^d`, the $`d`-fold product of the Kummer classes
generates, and $`\operatorname{tr}` sends it to $`1`.
:::

:::proof "DU-trace-map"
Deep infrastructure (part of the duality package
{bpref "GEO-duality-realization"}[]): constructed from the Gysin/Kummer
class of a point via purity for the smooth pair
$`(\mathbb{A}^d, \{0\})`, then glued. The blueprint isolates it because
the functional equation's powers of $`q` all originate here: the trace
map is where the identification "top cohomology $`=` $`\Ql(-d)`, Frobenius
acts by $`q^d`" is fixed once and for all.
:::

:::theorem "DU-cup-pairing" (parent := "grp-duality") (uses := "DU-trace-map") (tags := "deep-input") (effort := "large")
Cup-product pairing: for $`X` smooth projective of pure dimension $`d`
over $`\Fqbar` (base-changed from $`X_0`), the composite
$$`H^i(X, \Ql) \times H^{2d-i}(X, \Ql) \xrightarrow{\smile} H^{2d}(X, \Ql) \cong \Ql(-d)`
is a Galois-equivariant bilinear pairing, graded-commutative with sign
$`(-1)^{i(2d-i)}`. (Perfectness is the separate statement
{bpref "DU-poincare-duality"}[].)
:::

:::proof "DU-cup-pairing"
Realization input, packaged with {bpref "GEO-duality-realization"}[]:
requires cup products on étale cohomology (multiplicative structure of
$`R\Gamma`), their graded commutativity, and equivariance of everything
under the Galois action; the sign convention is the Koszul rule for the
tensor structure on complexes.
:::

:::theorem "DU-poincare-duality" (parent := "grp-duality") (uses := "DU-cup-pairing") (tags := "deep-input") (effort := "large") (priority := "high")
Poincaré duality, absolute form: for $`X` smooth projective of pure
dimension $`d` over an algebraically closed field of characteristic
$`p \neq \ell`, the cup-product pairing of {bpref "DU-cup-pairing"}[] is
*perfect*: it identifies $`H^{2d-i}(X, \Ql)` with
$`H^i(X, \Ql)^\vee(-d)`. Only this absolute statement is on the critical
path — relative Verdier duality ($`Rf^!`, the duality functor) is *not*
required for the main theorem, and curve duality
({bpref "DU-curve-duality"}[]) is stated separately for the weight
branch.
:::

:::proof "DU-poincare-duality"
Deep input ({bpref "GEO-duality-realization"}[]): Verdier-style proof
via $`f^! \Ql \cong \Ql(d)[2d]` for smooth $`f` (relative purity), or
the classical reduction to curves by fibration; the internal
decomposition lives in the geometric-inputs chapter. The consumers are:
{bpref "DU-interface"}[] (via untwisting), and the purity squeeze
({bpref "PUR-duality-squeeze"}[]) — note the latter uses duality a
second time, independently of the functional equation.
:::

:::theorem "DU-curve-duality" (parent := "grp-duality") (uses := "SIX-j-star-curves") (tags := "deep-input") (effort := "large")
Curve duality for middle extensions: let $`C` be a smooth projective
curve over $`\Fqbar`, $`j \colon U \hookrightarrow C` a dense open, $`L`
a lisse $`\Qlbar`-sheaf on $`U`. There are perfect Frobenius-compatible
pairings
$$`H^i(C, j_*L) \times H^{2-i}(C, j_*L^\vee) \to \Qlbar(-1) \qquad (i = 0, 1, 2),`
and in particular: $`H^0_c(U, L) = 0` for $`U` affine and $`L` without
trivial sub, and
$`H^2_c(U, L) \cong (L_{\bar\eta})_{\pi_1(U)}(-1)` (coinvariants,
twisted). The special cases are recorded separately as
{bpref "SIX-affine-curve-bounds"}[] because the weight machinery
consumes them constantly.
:::

:::proof "DU-curve-duality"
Deep input, packaged with {bpref "GEO-duality-realization"}[] (local
duality on curves: inertia invariants pair with inertia coinvariants,
$`H^1` of inertia is dual to invariants with a twist). Consumers:
{bpref "MON-r1j-m2"}[] (the lower boundary bound is dual to the upper
one) and {bpref "PUR-projective-curve"}[] (the lower purity bound on
curves is dual to the upper bound for the dual sheaf).
:::
