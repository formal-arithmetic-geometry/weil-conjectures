import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Weights" =>

Weight predicates on Frobenius modules are the vocabulary in which purity is
consumed by the final assembly. They are stated for an arbitrary ring
homomorphism $`\iota \colon K \to \CC` and quantified over *all* such
homomorphisms in the universal form; no topology on $`K` is ever used. The
squared normalization $`\|\iota\alpha\|^2 = q^w` avoids square roots and
half-integer exponents throughout.

:::group "group:weights"
Purity and mixedness predicates for Frobenius modules, and the weight
separation arguments used in the no-cancellation step.
:::

# Purity predicates

:::definition "def:pure-weight" (parent := "group:weights") (uses := "def:frobenius-eigenvalue") (lean := "Weil.IsPureWeight")
Let $`(V, f)` be a Frobenius module over $`K`, let
$`\iota \colon K \to \CC` be a ring homomorphism, $`q \in \mathbb{N}` and
$`w \in \ZZ`. Then $`(V, f)` is *$`\iota`-pure of weight $`w`* (relative to
$`q`) if every eigenvalue $`\alpha` of $`f` satisfies
$$`\|\iota \alpha\|^2 = q^{w}.`
There are companion predicates *mixed of weight $`\leq w`* and *mixed of
weight $`\geq w`*, defined by the corresponding eigenvalue bounds. At the
module level mixedness is an eigenvalue bound, not a filtration; over an
algebraically closed field the two agree, and only the sheaf level needs
filtrations.
:::

:::definition "def:universal-purity" (parent := "group:weights") (uses := "def:pure-weight") (lean := "Weil.IsUnivPureWeight")
$`(V, f)` is *universally pure of weight $`w`* if it is $`\iota`-pure of
weight $`w` for *every* ring homomorphism $`\iota \colon K \to \CC`. This
universal quantifier is essential: the Galois-stability arguments that make
the polynomials $`P_i` rational, and the conversion of purity into a
statement about all complex roots of integer polynomials, use exactly the
freedom to move $`\iota`. A single embedding would not suffice.
:::

# Weight separation

:::lemma_ "lem:weight-separation" (parent := "group:weights") (uses := "def:pure-weight") (lean := "Weil.IsPureWeight.not_isEigenvalue_of_ne")
Let $`q \geq 2`. If $`(V, f)` is $`\iota`-pure of weight $`w`, $`(W, g)` is
$`\iota`-pure of weight $`w'`, and $`w \neq w'`, then no eigenvalue of $`f`
is an eigenvalue of $`g`. In particular a nonzero Frobenius module is pure
of at most one weight.
:::

:::proof "lem:weight-separation"
If $`\alpha` were a common eigenvalue then
$`q^{w} = \|\iota\alpha\|^2 = q^{w'}`, and
$`n \mapsto q^n` is injective on $`\ZZ` for $`q \geq 2` (strict
monotonicity of integer powers of a real number $`> 1`). This lemma is
formalized and sorry-free; it is the kernel of the *no-cancellation*
argument: for $`i \neq j` the factors $`P_i` and $`P_j` share no
reciprocal root, so the odd and even parity products are coprime.
:::

Future nodes of this chapter: stability of universal weights under
$`\operatorname{Aut}(K/\QQ)`, the fixed field of the automorphism group of
an algebraically closed characteristic-$`0` field being $`\QQ`, extension of
complex embeddings from subfields (under the cardinality bound
$`\#K \leq 2^{\aleph_0}`), the finite-filtration weight bound that replaces
every spectral-sequence argument, and the Weil-polynomial bridge between
eigenvalue purity and complex root moduli.
