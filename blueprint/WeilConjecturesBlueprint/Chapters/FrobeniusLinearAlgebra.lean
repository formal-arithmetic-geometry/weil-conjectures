import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Frobenius modules and linear algebra" =>

The linear-algebra backbone of Layer I: Frobenius modules, eigenvalues via
characteristic polynomials, reversed characteristic polynomials, traces of
iterates, and the determinant–trace exponential identity. Everything is
independent of the geometric chapters; several nodes are already
formalized in `WeilConjectures/Weights/FrobeniusModule.lean`.

:::group "grp-linear-algebra"
Frobenius modules over an abstract coefficient field and their
characteristic-polynomial calculus.
:::

# Frobenius modules and eigenvalues

:::definition "LA-frobenius-module" (parent := "grp-linear-algebra")
Let $`K` be a field. A *Frobenius module* over $`K` is a
finite-dimensional $`K`-vector space $`V` with a linear automorphism
$`f \colon V \xrightarrow{\sim} V`. The formalization keeps this notion
deliberately *unbundled* — a space with `[FiniteDimensional K V]` and an
equivalence `f : V ≃ₗ[K] V` — so that every predicate below applies
without a wrapper structure; a bundled graded family appears only in the
abstract package {bpref "COH-weil-package"}[]. In the étale realization
$`K = \Qlbar` and $`f` is geometric Frobenius on a cohomology group.
:::

:::definition "LA-eigenvalue" (parent := "grp-linear-algebra") (uses := "LA-frobenius-module") (lean := "Weil.IsEigenvalue") (tags := "existing-project")
$`\alpha \in K` is an *eigenvalue* of $`(V, f)` if it is a root of the
characteristic polynomial of $`f` (as endomorphism). Formalized as
`Weil.IsEigenvalue` with the determinant characterization
$`\det(\alpha \cdot 1 - f) = 0` (`Weil.isEigenvalue_iff_det`). Note the
predicate deliberately ignores multiplicity; the pipeline steps that need
multiplicities ({bpref "W-rational-coefficients"}[]) work with the
characteristic polynomial itself, and a future refinement may add the
multiset `(charpolyRev f).roots` alongside the predicate.
:::

:::lemma_ "LA-eigenvalue-exists" (parent := "grp-linear-algebra") (uses := "LA-eigenvalue") (lean := "Weil.exists_isEigenvalue") (tags := "existing-project")
Over an algebraically closed $`K`, a Frobenius module with $`V \neq 0`
has at least one eigenvalue.
:::

:::proof "LA-eigenvalue-exists"
The characteristic polynomial has degree $`\dim V \geq 1`, hence a root in
$`K`. Formalized and sorry-free (via `IsAlgClosed.exists_root` and the
degree computation `LinearMap.charpoly_natDegree`).
:::

:::lemma_ "LA-eigenvalue-nonzero" (parent := "grp-linear-algebra") (uses := "LA-eigenvalue") (lean := "Weil.IsEigenvalue.ne_zero") (tags := "existing-project")
Every eigenvalue of a Frobenius module is nonzero (the defining map is an
automorphism). Formalized and sorry-free; the proof uses that
$`\det f` is a unit (`LinearEquiv.isUnit_det'`), so $`0` is not a root of
the characteristic polynomial.
:::

# Reversed characteristic polynomials

:::definition "LA-charpoly-rev" (parent := "grp-linear-algebra") (uses := "LA-frobenius-module") (lean := "Matrix.charpolyRev") (tags := "mathlib")
The *reversed characteristic polynomial* of an endomorphism $`u` of an
$`n`-dimensional $`K`-space:
$$`P_u(t) = \charrev{u} \in K[t].`
Mathlib provides the matrix-level primitive `Matrix.charpolyRev`
$`= \det(1 - t \cdot M)` together with `Matrix.reverse_charpoly` (it is
the reversal of the characteristic polynomial). Still needed (part of
{bpref "LA-charpoly-rev-props"}[]): the basis-independent linear-map-level
wrapper, so that $`P_u` is defined for `u : V →ₗ[K] V` without choosing a
basis.
:::

:::lemma_ "LA-charpoly-rev-props" (parent := "grp-linear-algebra") (uses := "LA-charpoly-rev, LA-eigenvalue") (tags := "elementary-missing") (effort := "medium")
Basic properties of $`P_u`: (i) $`P_u(0) = 1`; (ii)
$`\deg P_u \leq \dim V`, with equality iff $`u` is invertible, and for an
automorphism the leading coefficient is $`(-1)^{\dim V}\det u`; (iii)
$`\alpha \neq 0` is an eigenvalue of $`u` iff $`P_u(\alpha^{-1}) = 0`;
(iv) over an algebraically closed field,
$`P_u = \prod_j (1 - \alpha_j t)` where $`(\alpha_j)` is the eigenvalue
multiset of the automorphism $`u`; (v) $`P_u` is invariant under
conjugation and under passing to the dual endomorphism $`u^\vee`.
:::

:::proof "LA-charpoly-rev-props"
(i)–(iii) and (v) follow from `Matrix.reverse_charpoly` and determinant
calculus: the constant term is $`\det(1) = 1`; the reversal exchanges the
top and bottom coefficients of the characteristic polynomial; roots of the
reversal are inverses of the nonzero roots; conjugation invariance is
determinant conjugation invariance; and
$`\operatorname{charpoly}(u^\vee) = \operatorname{charpoly}(u)` because a
matrix and its transpose have equal determinants. (iv) is the splitting of
the characteristic polynomial over $`\overline K` rewritten through the
reversal.
:::

:::lemma_ "LA-charpoly-rev-mult" (parent := "grp-linear-algebra") (uses := "LA-charpoly-rev") (tags := "elementary-missing") (effort := "medium")
Multiplicativity on invariant subspaces: if $`W \subseteq V` is a
$`u`-invariant subspace, then
$$`P_{u|_V} = P_{u|_W} \cdot P_{\bar u|_{V/W}}`
where $`\bar u` is the induced endomorphism of $`V/W`. Consequently, for a
Frobenius module with a finite $`f`-stable filtration, $`P_f` is the
product of the $`P` of the graded pieces, and the eigenvalue multiset of
$`f` is the union of those of the graded pieces.
:::

:::proof "LA-charpoly-rev-mult"
Choose a basis of $`W` and extend to a basis of $`V`; in this basis the
matrix of $`1 - tu` is block upper triangular with diagonal blocks
$`1 - t(u|_W)` and $`1 - t\bar u`, and the determinant of a block
upper-triangular matrix is the product of the determinants of the diagonal
blocks (`Matrix.det_fromBlocks_zero₂₁` in Mathlib provides the two-block
case). The filtration statement follows by induction on the filtration
length. This lemma is used three times: in the determinant–trace induction
({bpref "LA-det-trace"}[]), in the filtration weight bound
({bpref "WT-filtration-bound"}[]), and in the endpoint analysis.
:::

# Traces of iterates

:::definition "LA-trace-iter" (parent := "grp-linear-algebra") (uses := "LA-frobenius-module") (lean := "Weil.traceIter") (tags := "existing-project")
For a Frobenius module $`(V, f)` and $`n \in \mathbb{N}`, the trace of the
$`n`-th iterate $`\Tr(f^n \mid V) \in K`. Formalized as `Weil.traceIter`
with the normalizations $`\Tr(f^0) = \dim V` and
$`\Tr(f^1) = \Tr(f)`. These are the quantities the trace formula equates
with point counts.
:::

:::lemma_ "LA-trace-additive" (parent := "grp-linear-algebra") (uses := "LA-trace-iter") (tags := "elementary-missing") (effort := "small")
If $`W \subseteq V` is $`u`-invariant then
$`\Tr(u^n \mid V) = \Tr(u^n|_W \mid W) + \Tr(\bar u^n \mid V/W)` for all
$`n`.
:::

:::proof "LA-trace-additive"
In an adapted basis the matrix of $`u^n` is block upper triangular with
diagonal blocks $`(u|_W)^n` and $`\bar u^n`, and the trace of a
block-triangular matrix is the sum of the traces of the diagonal blocks.
(Mathlib's `LinearMap.trace` API plus the `fromBlocks` trace lemma; only
the glue is missing.)
:::

# The determinant–trace identity

:::theorem "LA-det-trace" (parent := "grp-linear-algebra") (uses := "LA-charpoly-rev, LA-trace-iter, ML-power-series-exp") (tags := "elementary-missing, infrastructure") (effort := "large") (priority := "high")
Let $`K` be a field of characteristic $`0`, $`V` finite-dimensional over
$`K`, $`u \in \operatorname{End}_K(V)`. In $`K[\![t]\!]`:
$$`\exp\Bigl(\sum_{n \geq 1} \Tr(u^n) \frac{t^n}{n}\Bigr) = \frac{1}{\charrev{u}}.`
Both sides lie in $`1 + tK[\![t]\!]`; the right side is the inverse of a
polynomial with constant term $`1`, so no division of power series is
implicit in the statement.
:::

:::proof "LA-det-trace" (uses := "LA-eigenvalue-exists, LA-charpoly-rev-mult, LA-trace-additive, LA-exp-log-iso")
*Step 1 (scalar extension).* Every coefficient of either side is a
universal polynomial with $`\QQ`-coefficients in the entries of a matrix
of $`u`; equivalently, both sides are compatible with the injective ring
map $`K[\![t]\!] \to \overline{K}[\![t]\!]`. So it suffices to prove the
identity over the algebraic closure.

*Step 2 (induction on dimension).* Over $`\overline K`, induct on
$`\dim V`. If $`V = 0`, both sides are $`1`. Otherwise, if $`u` is not
invertible restrict attention as follows: pick, by
{bpref "LA-eigenvalue-exists"}[] applied to the characteristic polynomial
(or directly: any root $`\lambda` of $`\operatorname{charpoly}(u)`, which
exists since $`\dim V \geq 1`), an eigenvector $`v` with
$`u v = \lambda v`; the line $`L = \overline{K} v` is $`u`-invariant.
Multiplicativity {bpref "LA-charpoly-rev-mult"}[] and additivity
{bpref "LA-trace-additive"}[] on $`0 \to L \to V \to V/L \to 0`, together
with the homomorphism property of $`\exp`
({bpref "LA-exp-log-iso"}[]), reduce the identity for $`V` to the
identities for $`L` and $`V/L`, and the latter holds by induction.

*Step 3 (dimension one).* For $`V = \overline{K}`, $`u = \lambda`:
$`\sum_{n \geq 1} \lambda^n t^n/n = \operatorname{logOf}\,(1 - \lambda t)^{-1}`,
which is the geometric-series computation
$`-\log(1 - s) = \sum s^n/n` at $`s = \lambda t`, i.e. the coefficient
formula for `PowerSeries.logOf` applied to a linear polynomial.

This route needs only *one eigenvector*, not triangularization, and avoids
Jacobi's derivative-of-determinant formula entirely. The alternative
(logarithmic derivative of $`\det(1 - tu)` via Jacobi) is recorded as a
fallback with higher formalization cost.
:::

:::theorem "LA-det-trace-graded" (parent := "grp-linear-algebra") (uses := "LA-det-trace") (tags := "elementary-missing") (effort := "small")
Graded alternating version: for a finite graded family
$`(V_i, u_i)_{i \in I}` with signs $`\epsilon(i) = (-1)^i`,
$$`\exp\Bigl(\sum_{n \geq 1}\Bigl(\sum_i (-1)^i \Tr(u_i^n)\Bigr)\frac{t^n}{n}\Bigr) = \prod_i P_{u_i}(t)^{(-1)^{i+1}},`
the product taken in the unit group $`1 + tK[\![t]\!]` (integer powers of
units, no power-series division).
:::

:::proof "LA-det-trace-graded" (uses := "LA-exp-log-iso")
Apply {bpref "LA-det-trace"}[] in each degree, raise to the integer power
$`(-1)^{i+1}` inside the unit group (which $`\exp` intertwines with
integer multiples on the additive side by {bpref "LA-exp-log-iso"}[]),
and multiply the finitely many factors, using that $`\exp` converts the
finite sum into the finite product. This is the exact algebraic shape
consumed by {bpref "W-factorization"}[].
:::
