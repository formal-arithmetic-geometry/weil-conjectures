import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Duality" =>

Poincaré duality enters the final assembly in a deliberately minimal form:
as a *similitude pairing* between complementary cohomological degrees, with
multiplier $`q^d` and a sign constraint in the middle degree. This is the
second interface hypothesis (AX2). The reciprocal-polynomial identity it
induces is pure linear algebra and lives in this chapter as well.

:::group "group:duality"
Similitude pairings, the reciprocal characteristic-polynomial identity, and
Poincaré duality as an interface axiom.
:::

# The interface statement

:::theorem "thm:poincare-duality" (parent := "group:duality") (uses := "def:frobenius-module") (tags := "deep, axiom-candidate") (effort := "large")
In the situation of the trace formula ($`X` smooth projective of pure
dimension $`d`, spaces $`H^i` with Frobenius $`F_i`), there are perfect
$`K`-bilinear pairings
$`\varphi_i \colon H^i \times H^{2d-i} \to K`
satisfying the similitude property
$$`\varphi_i(F_i x, F_{2d-i} y) = q^{d}\, \varphi_i(x, y),`
and the middle pairing $`\varphi_d` is symmetric for $`d` even and
alternating for $`d` odd. Moreover $`\dim H^0 = 1` with $`F_0 = 1`
(endpoint normalization, using geometric connectedness — interface
hypothesis AX3). The multiplier is $`q^{+d}` because geometric Frobenius
acts on the Tate object $`\Ql(-d)` by $`q^{d}`; consequently the eigenvalue
paired with $`\alpha` is $`q^d/\alpha`.
:::

:::proof "thm:poincare-duality"
Deep input; initially assumed as the temporary axiom *AX2* (with AX3 for
the endpoint). The planned realization: cup product and the trace map
$`H^{2d}(X, \Ql(d)) \cong \Ql` induce a Galois-equivariant perfect pairing
$`H^i \times H^{2d-i} \to \Ql(-d)`; equivariance gives the similitude
multiplier, and graded commutativity of the cup product gives the
$`(-1)^{i(2d-i)}`-symmetry, which in middle degree is
$`(-1)^{d}`-symmetry. Only the absolute statement over the algebraically
closed base is needed; relative Verdier duality is not on the critical
path. The endpoint $`P_{2d} = 1 - q^d t` is *not* a separate axiom: it
follows from the pairing against $`H^0`.
:::

# The reciprocal-polynomial identity

:::lemma_ "lem:reciprocal-charpoly" (parent := "group:duality") (uses := "def:frobenius-module, def:reversed-charpoly") (effort := "small")
Let $`V, W` be $`K`-vector spaces of dimension $`r`, let
$`\langle\,,\rangle \colon V \times W \to K` be a perfect pairing, and let
$`u, v` be automorphisms of $`V, W` with
$`\langle u x, v y\rangle = \mu \langle x, y\rangle` for a unit $`\mu`.
Then $`\det v = \mu^{r}/\det u`, and in $`K[T, T^{-1}]`
$$`P_v(\mu^{-1}T^{-1}) = (-1)^{r}\, T^{-r}\, (\det u)^{-1}\, P_u(T),`
where $`P_u(T) = \charrev{u}` (with $`t = T`). On eigenvalue multisets this
says the eigenvalues of $`v` are $`\{\mu/\alpha_j\}` where
$`\{\alpha_j\}` are those of $`u`.
:::

:::proof "lem:reciprocal-charpoly"
The pairing identifies $`W \cong V^\vee`, under which
$`v = \mu\,(u^{-1})^\vee`: indeed
$`\langle x, v y\rangle = \mu \langle u^{-1}x, y\rangle`. Taking
determinants gives $`\det v = \mu^r/\det u`. For the Laurent identity,
avoid eigenvalues entirely: from the endomorphism identity
$`1 - s w = (-s w)(1 - s^{-1} w^{-1})` take determinants to get
$`\det(1 - s w) = (-s)^{r} \det(w) \det(1 - s^{-1}w^{-1})`, and apply it
with $`w = v`, $`s = \mu^{-1}T^{-1}`, using that the characteristic
polynomial of a dual endomorphism equals that of the endomorphism. Working
with the polynomial identity rather than eigenvalue multisets avoids all
multiplicity bookkeeping in the formalization.
:::

Future nodes of this chapter: the abstract graded functional equation (the
sign analysis $`\delta^2 = 1`, the parity lemma that a perfect alternating
form forces even dimension, and the determinant bookkeeping
$`D_i D_{2d-i} = q^{d b_i}`), and on the realization side the trace map,
fundamental classes, and curve duality.
