import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Zeta functions" =>

This chapter fixes the arithmetic objects appearing in the final statements:
point counts, the zeta function as a formal power series, and the three
predicates on integer polynomials that express the Weil conjectures. All
definitions in this chapter are formalized (they live in the repository's
statement layer), so every node here links to an existing Lean declaration.

:::group "group:zeta"
The zeta function of a variety over a finite field and the statement-level
predicates for the Weil conjectures.
:::

# Point counts and the zeta series

:::definition "def:point-count" (parent := "group:zeta") (lean := "AlgebraicGeometry.Scheme.Hom.pointCount")
Let $`X` be a scheme over a finite field $`k` with $`q` elements, given by a
structure morphism $`f \colon X \to \Spec k`. For $`n \geq 1`, the *point
count* $`N_n` is the number of $`k_n`-rational points of $`X`, where
$`k_n/k` is the degree-$`n` extension of $`k`:
$$`N_n = \# X(\Fqn{n}).`
:::

:::definition "def:zeta-function" (parent := "group:zeta") (uses := "def:point-count") (lean := "AlgebraicGeometry.Scheme.Hom.zetaSeries")
The *zeta function* of $`X/k` is the formal power series
$$`Z(X, t) = \exp\Bigl(\sum_{n \geq 1} N_n \frac{t^n}{n}\Bigr) \in \QQ[\![t]\!].`
No convergence is involved: $`\exp` is the formal exponential and the sum is
$`t`-adically convergent.
:::

# The statement-level predicates

The three conclusions of the Weil conjectures are expressed by predicates on
a family of integer polynomials $`P_0, \dots, P_{2d} \in \ZZ[t]`. This keeps
the final statements free of any cohomological vocabulary.

:::definition "def:weil-factorization" (parent := "group:zeta") (uses := "def:zeta-function") (lean := "AlgebraicGeometry.IsWeilFactorization")
`IsWeilFactorization q d Z P` says: each $`P_i` has constant coefficient
$`1`, the endpoints are $`P_0 = 1 - t` and $`P_{2d} = 1 - q^d t`, and
$$`Z \cdot \prod_{i \text{ even}} P_i = \prod_{i \text{ odd}} P_i`
holds in $`\QQ[\![t]\!]`. This is the rationality-with-factorization shape
$`Z = (P_1 \cdots P_{2d-1})/(P_0 \cdots P_{2d})` predicted for a smooth,
proper, geometrically integral variety of dimension $`d`, stated without
dividing power series.
:::

:::definition "def:functional-equation-predicate" (parent := "group:zeta") (lean := "AlgebraicGeometry.WeilFunctionalEquation")
`WeilFunctionalEquation q d P` says: for every $`i`, the map
$`z \mapsto (q^d z)^{-1}` sends the multiset of complex roots of $`P_i`
to the multiset of complex roots of $`P_{2d-i}`. Equivalently,
$`\alpha \mapsto q^d/\alpha` matches the reciprocal roots of $`P_i` with
those of $`P_{2d-i}`, with multiplicity. This root-multiset form implies the
classical identity $`Z(X, 1/(q^d t)) = \pm\, q^{d\chi/2} t^{\chi} Z(X, t)`.
:::

:::definition "def:riemann-hypothesis-predicate" (parent := "group:zeta") (lean := "AlgebraicGeometry.WeilRiemannHypothesis")
`WeilRiemannHypothesis q d P` says: every complex root $`z` of the image of
$`P_i` in $`\CC[t]` satisfies $`\|z\| = q^{-i/2}`. Since each $`P_i` has
integer coefficients and constant coefficient $`1`, its reciprocal roots are
automatically algebraic integers, so this constrains all their complex
absolute values to be $`q^{i/2}`.
:::

Future nodes of this chapter (not yet written): the Euler product over closed
points, integrality $`Z \in 1 + t\ZZ[\![t]\!]`, and the executable
normalization tests $`Z(\Spec k) = (1-t)^{-1}`,
$`Z(\mathbb{A}^1) = (1-qt)^{-1}`, $`Z(\mathbb{P}^1) = ((1-t)(1-qt))^{-1}`
that pin the Frobenius conventions.
