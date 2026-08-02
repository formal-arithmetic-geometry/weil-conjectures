import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The trace formula" =>

The trace formula is the first of the four interface hypotheses (AX1) of the
abstract cohomology package: it converts point counts into alternating sums
of traces of Frobenius iterates and thereby feeds the entire algebraic
machine. At the interface it is a single statement; its realization
decomposes into the Lefschetz–Verdier trace formula with finite
coefficients, the computation of Frobenius local terms, and the passage to
ℓ-adic coefficients.

:::group "group:trace-formula"
The Grothendieck–Lefschetz trace formula: interface form and realization
plan.
:::

# The interface statement

:::theorem "thm:trace-formula" (parent := "group:trace-formula") (uses := "def:point-count, def:frobenius-module, def:trace-iterate") (tags := "deep, axiom-candidate") (effort := "large")
Let $`X` be smooth and projective over $`k = \Fq`, of pure dimension $`d`.
There are finite-dimensional $`K`-vector spaces $`H^0, \dots, H^{2d}` with
automorphisms $`F_i` (geometric Frobenius) such that for all $`n \geq 1`
$$`\# X(\Fqn{n}) = \sum_{i=0}^{2d} (-1)^i \, \Tr\bigl(F_i^n \mid H^i\bigr)`
in $`K`. (Compact-support variant for arbitrary separated finite-type
$`X`: same shape, with $`\Hc^i` and no upper bound $`2d` on the range —
this weaker form already suffices for rationality of the zeta function of
an arbitrary variety.)
:::

:::proof "thm:trace-formula"
Deep input; initially assumed as the temporary axiom *AX1* of the
interface. The planned realization (Version III): the Lefschetz–Verdier
trace formula for correspondences with finite coefficients
$`\ZZ/\ell^\nu\ZZ`, applied to the graph of the $`q^n`-power Frobenius
correspondence, whose fixed points are exactly the $`\Fqn{n}`-rational
points, each isolated with multiplicity one because the differential of
Frobenius vanishes; then conversion between closed points and rational
points, supertrace calculus for bounded complexes, and the ℓ-adic limit.
For proper $`X` compactly supported and ordinary cohomology agree, which
gives the displayed form. These realization steps will become separate
nodes of the geometric chapters.
:::
