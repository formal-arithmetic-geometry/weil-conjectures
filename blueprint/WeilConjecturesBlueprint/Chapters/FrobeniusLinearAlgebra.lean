import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Frobenius modules and linear algebra" =>

This chapter contains the linear-algebra backbone of Version I: Frobenius
modules, reversed characteristic polynomials, traces of iterates, and the
determinant–trace exponential identity. Everything here is elementary and
independent of all geometric chapters.

:::group "group:frobenius"
Frobenius modules over an abstract coefficient field and their
characteristic-polynomial calculus.
:::

# Frobenius modules

:::definition "def:frobenius-module" (parent := "group:frobenius")
Let $`K` be a field. A *Frobenius module* over $`K` is a finite-dimensional
$`K`-vector space $`V` together with a linear automorphism
$`f \colon V \xrightarrow{\ \sim\ } V`. In the formalization this notion is
deliberately kept unbundled — a space with instances plus an equivalence
$`f : V \simeq_{\ell} V` — so that all predicates below can be stated
without a wrapper structure. For the étale realization, $`K` will be
$`\Qlbar` and $`f` the geometric Frobenius acting on a cohomology group.
:::

:::definition "def:frobenius-eigenvalue" (parent := "group:frobenius") (uses := "def:frobenius-module") (lean := "Weil.IsEigenvalue")
An element $`\alpha \in K` is an *eigenvalue* of the Frobenius module
$`(V, f)` if it is a root of the characteristic polynomial of $`f`. Over a
field this is equivalent to $`\det(\alpha \cdot 1 - f) = 0`, and over an
algebraically closed field a nontrivial Frobenius module has at least one
eigenvalue; every eigenvalue is nonzero because $`f` is invertible.
:::

:::definition "def:reversed-charpoly" (parent := "group:frobenius") (uses := "def:frobenius-module") (lean := "Matrix.charpolyRev") (tags := "mathlib")
The *reversed characteristic polynomial* of an endomorphism $`u` of an
$`n`-dimensional space is
$$`P_u(t) = \charrev{u} \in K[t],`
with constant term $`1`, degree $`\leq n` (with equality iff $`u` is
invertible), and leading coefficient $`(-1)^n \det u` when $`u` is
invertible. Its roots are the inverses of the nonzero eigenvalues of $`u`;
its *reciprocal roots* are the eigenvalues. Mathlib provides the matrix-level
primitive `Matrix.charpolyRev` together with `Matrix.reverse_charpoly`; the
project still needs the linear-map-level wrapper and the multiplicativity
lemma for invariant subspaces.
:::

:::definition "def:trace-iterate" (parent := "group:frobenius") (uses := "def:frobenius-module") (lean := "Weil.traceIter")
For a Frobenius module $`(V, f)` and $`n \in \mathbb{N}`, the *trace of the
$`n`-th iterate* is $`\Tr(f^n \mid V) \in K`. These are the quantities that
the trace formula equates with point counts.
:::

# The determinant–trace identity

:::lemma_ "lem:det-trace" (parent := "group:frobenius") (uses := "def:reversed-charpoly, def:trace-iterate") (effort := "medium")
Let $`K` be a field of characteristic $`0`, $`V` a finite-dimensional
$`K`-vector space and $`u` an endomorphism of $`V`. Then in $`K[\![t]\!]`:
$$`\frac{1}{\charrev{u}} = \exp\Bigl(\sum_{n \geq 1} \Tr(u^n) \frac{t^n}{n}\Bigr).`
Both sides live in the group $`1 + tK[\![t]\!]` of units with constant term
$`1`; no convergence is involved.
:::

:::proof "lem:det-trace" (uses := "def:frobenius-eigenvalue")
Both sides have coefficients given by universal polynomial expressions in
the entries of a matrix of $`u`, so the identity may be checked after the
injective scalar extension $`K \to \overline{K}`. There, induct on
$`\dim V`. If $`V = 0` both sides are $`1`. Otherwise $`u` has an
eigenvector ({bpref "def:frobenius-eigenvalue"}[]), spanning a
$`u`-invariant line $`L`, and we obtain the exact sequence
$`0 \to L \to V \to V/L \to 0`. The reversed characteristic polynomial is
multiplicative in such sequences (block-triangular determinant), the trace
of $`u^n` is additive, and $`\exp` turns sums into products, so the claim
reduces to the one-dimensional case, which is the geometric series identity
$`-\log(1 - \lambda t) = \sum_{n \geq 1} \lambda^n t^n / n`. This route
needs only the existence of one eigenvector, not a full triangularization.
:::

Future nodes of this chapter: the graded alternating version of
{bpref "lem:det-trace"}[] for a finite family $`(V_i, u_i)`, the formal
$`\exp`/$`\log` group isomorphism between $`(tK[\![t]\!], +)` and
$`(1 + tK[\![t]\!], \times)`, the Hankel-rank characterization of rational
power series, the integral Fatou lemma, and the normalized Gauss lemma —
the entire rationality toolkit of Version I.
