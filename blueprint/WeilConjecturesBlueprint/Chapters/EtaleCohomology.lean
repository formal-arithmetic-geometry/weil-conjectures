import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Étale cohomology" =>

Layer III plumbing: the small étale site, stalks and exactness, the
ℓ-adic coefficient formalism, the Frobenius dictionary, the Tate twist,
the concrete computations that pin the conventions, and the realization
theorem that instantiates the abstract package. Deep theorems (base
change, finiteness, duality, trace formula) are *not* hidden here — they
live in their own chapters and this chapter only wires them together.
The repository already contains a first block of site-theoretic
infrastructure (the localization lower shriek).

:::group "grp-etale"
The small étale site, ℓ-adic coefficients, Frobenius dictionary, and the
realization theorem.
:::

# Sites, stalks, coefficients

:::definition "ET-etale-site" (parent := "grp-etale") (tags := "infrastructure") (effort := "large")
The small étale site of a scheme $`X`: the category of schemes étale
over $`X` with covers the jointly surjective families of étale
morphisms; abelian sheaves and $`\Lambda`-module sheaves on it; and
$`H^i(X, -)`, $`H^i_c(X, -)` as derived functors of global sections
(compactly-supported sections via a compactification,
{bpref "SIX-rf-shriek"}[]). Mathlib status: Grothendieck sites,
sheafification and sheaf categories exist; étale morphism classes exist
(`AlgebraicGeometry.IsEtale`); a usable small-étale-site bundle with its
abelian sheaf category is new infrastructure. The repository's slice-site
work below is a first installment.
:::

:::definition "ET-lower-shriek" (parent := "grp-etale") (lean := "CategoryTheory.GrothendieckTopology.localizationLowerShriek") (tags := "existing-project")
Localization lower shriek: for a site $`(C, J)`, a morphism
$`f \colon V \to U`, and coefficients $`A`, the functor
$`j_! \colon \mathrm{Sh}(J/V, A) \to \mathrm{Sh}(J/U, A)`, left adjoint
to restriction (`localizationLowerShriekAdjunction`), built as presheaf
left Kan extension followed by sheafification. Formalized and
sorry-free, with identity and composition isomorphisms. This is the
site-level engine behind extension by zero, hence behind the
localization triangle {bpref "SIX-localization-triangle"}[].
:::

:::theorem "ET-open-localization" (parent := "grp-etale") (uses := "ET-lower-shriek") (lean := "CategoryTheory.GrothendieckTopology.IsOpenLocalization") (tags := "existing-project")
Open localizations: if the sheafified-representable map of
$`f \colon V \to U` is a monomorphism (`IsOpenLocalization`; automatic
when $`f` is a monomorphism, `isOpenLocalization_of_mono`), then the
unit of $`j_! \dashv j^*` is an isomorphism and $`j_!` is fully
faithful — sheaf-theoretic extension by zero along an open immersion.
Formalized and sorry-free, including presheaf-level extension-by-zero
formulas. For the small étale site this captures open subschemes.
:::

:::definition "ET-geometric-points" (parent := "grp-etale") (uses := "ET-etale-site") (tags := "infrastructure") (effort := "medium")
Geometric points and stalks: a geometric point $`\bar x \to X` (Spec of
a separably closed field), the stalk functor
$`\mathcal{F} \mapsto \mathcal{F}_{\bar x}` (filtered colimit over
étale neighbourhoods), its exactness, and joint conservativity: a map of
étale sheaves is an isomorphism iff it is on all stalks at a
conservative family of geometric points. Mathlib has the étale-points
scaffolding (`AlgebraicGeometry/Sites/EtalePoint`); the stalk-exactness
package for the abelian categories is to be built on it.
:::

:::definition "ET-adic-formalism" (parent := "grp-etale") (tags := "infrastructure") (effort := "large")
ℓ-adic coefficients: torsion levels $`\Lambda_\nu = \ZZ/\ell^\nu\ZZ`,
normalized projective systems (Artin–Rees category),
$`\ZZ_\ell`-sheaves as pro-systems with surjective transition maps
modulo AR-null systems, $`\Ql`- and $`\Qlbar`-coefficients by scalar
extension on Homs; exactness properties via Mittag-Leffler; and the
passage functors $`H^i(X, \ZZ_\ell) := \varprojlim H^i(X, \Lambda_\nu)`
with their finiteness hypotheses. *Recorded warning from the lecture
notes:* never argue "inverse limits are exact"; every limit exchange
must go through finiteness (Mittag-Leffler) at torsion level. This node
is large but purely formal infrastructure; it consumes
{bpref "GEO-finiteness"}[] to know the torsion groups are finite.
:::

# Frobenius

:::definition "ET-frobenius-dictionary" (parent := "grp-etale") (uses := "ET-etale-site") (tags := "infrastructure") (effort := "medium") (priority := "high")
The Frobenius dictionary. For $`X_0/\Fq` with base change
$`X = X_0 \times_{\Fq} \Fqbar`: (i) the *arithmetic Frobenius*
$`\varphi \in \operatorname{Gal}(\Fqbar/\Fq)` acts on $`X` through the
second factor; (ii) the *$`q`-power Frobenius endomorphism*
$`F_{X} = \operatorname{Fr}_{X_0} \times \operatorname{id}` acts
through the first; (iii) the *absolute* $`q`-power Frobenius of $`X` is
their composite and acts trivially on the étale topos (it is a
universal homeomorphism inducing the identity on étale sites); hence
(iv) on étale cohomology of $`X`, the action of $`F_X^*` equals the
action of the *geometric* Frobenius $`\varphi^{-1}` of the Galois
group. For a closed point $`x` of $`X_0` of degree $`d_x`, the local
geometric Frobenius $`F_x` at a geometric point over $`x` is the
$`d_x`-th power of the corresponding global convention
({bpref "TR-closed-points-conversion"}[]). All trace-formula and
weight statements use (iv) to move between the correspondence picture
(needed for local terms) and the Galois picture (needed for weights).
:::

:::definition "ET-tate-twist" (parent := "grp-etale") (uses := "ET-etale-site") (tags := "infrastructure") (effort := "medium")
The Tate object: $`\ZZ_\ell(1) := \varprojlim_\nu \mu_{\ell^\nu}` as a
Galois module / lisse sheaf, $`\Ql(1)` its rationalization, twists
$`\mathcal{F}(m) := \mathcal{F} \otimes \Ql(1)^{\otimes m}`. The
arithmetic Frobenius acts on $`\ZZ_\ell(1)` by $`q`; the geometric
Frobenius by $`q^{-1}` ({bpref "DU-tate-twist-action"}[]). Needed for:
the target of the trace map ({bpref "DU-trace-map"}[]), the duality
pairings, all weight bookkeeping, and the Fourier transform's twist
$`(-1)`.
:::

# Convention-pinning computations

:::theorem "ET-h0-computation" (parent := "grp-etale") (uses := "ET-etale-site") (tags := "elementary-missing") (effort := "medium")
$`H^0`: for $`X` of finite type over an algebraically closed field,
$`H^0(X, \Ql) = \Ql^{\pi_0(X)}`, and for $`X = (X_0)_{\Fqbar}` the
geometric Frobenius permutes the factors through its permutation of the
geometric components. If $`X_0` is geometrically connected, $`H^0 =
\Ql` with trivial action — realizing {bpref "DU-endpoint"}[].
:::

:::proof "ET-h0-computation"
Global sections of the constant sheaf on a connected scheme are
constants (any étale cover of a connected base has locally constant
sections determined on components); the finite-type hypothesis makes
$`\pi_0` finite, and functoriality of $`H^0` under the
Frobenius/Galois action is the component permutation. The formal
content is small once {bpref "ET-etale-site"}[] exists.
:::

:::theorem "ET-curve-computations" (parent := "grp-etale") (uses := "ET-tate-twist") (tags := "elementary-missing") (effort := "large")
Basic curve computations over an algebraically closed field of
characteristic $`p \neq \ell` (with Frobenius actions over $`\Fqbar`):
$$`H^i_c(\mathbb{A}^1) = \begin{cases}\Ql(-1) & i = 2\\ 0 & \text{else},\end{cases}\quad H^i(\mathbb{P}^1) = \begin{cases}\Ql & i = 0\\ \Ql(-1) & i = 2\\ 0 & \text{else},\end{cases}\quad H^1(\mathbb{G}_m) = \Ql(-1) \text{ (via Kummer)},`
so geometric Frobenius acts by $`1, q` on
$`H^0, H^2(\mathbb{P}^1)` — matching {bpref "Z-normalization-tests"}[]
through the trace formula. Proof route: the Kummer exact sequence
$`1 \to \mu_{\ell^\nu} \to \mathbb{G}_m \xrightarrow{\ell^\nu} \mathbb{G}_m \to 1`
computes $`H^1(\mathbb{G}_m, \mu_{\ell^\nu})` from units and Picard
groups; localization triangles then give $`\mathbb{A}^1` and
$`\mathbb{P}^1`. These computations are simultaneously convention tests
and genuine inputs (the Artin–Schreier orthogonality
{bpref "SIX-as-orthogonality"}[] and the constant-case curve lemma
{bpref "PUR-constant-case"}[] reduce to them).
:::

# The realization theorem

:::theorem "ET-realization" (parent := "grp-etale") (uses := "COH-weil-package, ET-etale-site, ET-adic-formalism, ET-frobenius-dictionary") (tags := "infrastructure") (effort := "large") (priority := "high")
Étale realization (Layer III): for $`X_0` smooth, projective,
geometrically integral of pure dimension $`d` over $`\Fq` and any
$`\ell \neq p`, the data
$`H^i := H^i(X_{\Fqbar}, \Ql) \otimes_{\Ql} \Qlbar` with $`F_i` = the
geometric Frobenius of {bpref "ET-frobenius-dictionary"}[] is a Weil
package for $`(q, d, N_\bullet(X_0))`. The constituents are exposed
separately, none hidden: *construction* of the spaces
({bpref "ET-etale-site"}[], {bpref "ET-adic-formalism"}[]);
*finite-dimensionality* ({bpref "GEO-finiteness"}[]); *Frobenius
action and its automorphy* ({bpref "ET-frobenius-dictionary"}[]);
*trace formula* = AX1 ({bpref "TR-interface-proper"}[] realized via
{bpref "TR-l-function"}[]); *Poincaré duality and twists* = AX2
({bpref "DU-interface"}[] realized via
{bpref "DU-poincare-duality"}[], {bpref "DU-trace-map"}[],
{bpref "ET-tate-twist"}[]); *endpoint* = AX3
({bpref "ET-h0-computation"}[]); *purity* = AX4
({bpref "PUR-smooth-proper"}[]); *cardinality*
({bpref "LA-qlbar-cardinality"}[]). Algebraicity, integrality, and
independence of $`\ell` are *not* inputs here: they are theorems of
Layer I ({bpref "W-algebraicity"}[],
{bpref "W-integral-coefficients"}[], {bpref "W-ell-independence"}[]).
:::

:::proof "ET-realization" (uses := "GEO-finiteness, TR-interface-proper, DU-interface, DU-endpoint, PUR-smooth-proper, LA-qlbar-cardinality")
Assembly only: each field of {bpref "COH-weil-package"}[] is discharged
by the listed node, with the scalar extension $`\Ql \to \Qlbar` flat
(dimension, traces, determinants, pairings and eigenvalue statements
all base-change along it). The theorem's value is exactly that it is
*only* assembly: every mathematical debt is visible in the graph as its
own leaf.
:::
