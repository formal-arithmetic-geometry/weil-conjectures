import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Purity" =>

Purity of the cohomology of smooth proper varieties is the fourth and
deepest interface hypothesis (AX4): it is the Riemann-hypothesis input. The
plan follows the Laumon–Deligne route: a general weight *upper bound* for
compactly supported higher direct images, proved by devissage to curves and
the Fourier–Deligne transform, then squeezed into purity by Poincaré
duality.

:::group "group:purity"
Deligne's purity theorem and the weight-estimate machinery that proves it.
:::

# The target

:::theorem "thm:purity-smooth-proper" (parent := "group:purity") (uses := "def:universal-purity") (tags := "deep") (effort := "large")
Let $`X` be smooth and proper over $`k = \Fq`, of pure dimension $`d`, and
let $`\ell \neq p`. For every $`i`, every ring homomorphism
$`\iota \colon \Qlbar \to \CC`, and every eigenvalue $`\alpha` of geometric
Frobenius on $`H^i_{\text{ét}}(X_{\Fqbar}, \Ql)`:
$$`\|\iota\alpha\|^2 = q^{i}.`
That is, $`H^i` is universally pure of weight $`i`. No algebraicity of
$`\alpha` is asserted here; algebraicity is a *conclusion* of the final
assembly, never a hypothesis.
:::

:::proof "thm:purity-smooth-proper" (uses := "thm:weight-estimate, thm:poincare-duality")
The duality squeeze. The weight estimate applied to the structure morphism
gives the upper bound: every eigenvalue on $`H^i` satisfies
$`\|\iota\alpha\|^2 \leq q^{i}` (weights $`\leq i`). Poincaré duality
identifies $`H^i \cong (H^{2d-i})^\vee(-d)`, so each eigenvalue $`\alpha`
on $`H^i` equals $`q^d/\beta` for an eigenvalue $`\beta` on $`H^{2d-i}`;
the same upper bound in the complementary degree,
$`\|\iota\beta\|^2 \leq q^{2d-i}`, gives
$`\|\iota\alpha\|^2 = q^{2d}/\|\iota\beta\|^2 \geq q^{i}`. Both bounds
together give purity. Note the lower bound needs *no new theorem* — only
the same upper bound in the complementary degree.
:::

# The weight estimate

:::theorem "thm:weight-estimate" (parent := "group:purity") (uses := "def:pure-weight") (tags := "deep") (effort := "large")
(Deligne–Laumon.) Let $`f \colon X \to Y` be a separated morphism of
finite-type $`\Fq`-schemes and let $`\mathcal{F}` be a constructible Weil
$`\Qlbar`-sheaf on $`X` that is $`\iota`-mixed of weights $`\leq w`. Then
for every $`i`, the sheaf $`R^i f_! \mathcal{F}` is $`\iota`-mixed of
weights $`\leq w + i`. Only the absolute case ($`Y` a point,
$`\mathcal{F}` constant) is consumed by the purity squeeze, but the
general-sheaf statement is forced as the induction vehicle: the devissage
passes through direct images on curves, which are non-constant lisse
sheaves.
:::

:::proof "thm:weight-estimate"
Deep input; the core of Weil II in the Laumon–Deligne formulation. Proof
plan (future nodes): six devissages (exact sequences, source and target
localization, composition via a finite filtration bound replacing the Leray
spectral sequence, universal homeomorphisms, finite morphisms) reduce to a
controlled relative curve; there, the curve estimate is proved via the
Fourier–Deligne transform on the affine line, the stationary-phase exact
sequence, the real-sheaf purity criterion, and boundary-monodromy weight
bounds. The deep leaves (real-sheaf purity, local monodromy, local Fourier
theory, tame reduction) will be axiomatized individually with the narrowest
possible statements and eliminated in a planned order.
:::
