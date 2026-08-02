import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The six-operation fragment" =>

The weight machinery does not need a six-functor *formalism*; it needs an
explicit, finite list of constructions and compatibilities, each for an
explicit class of morphisms. This chapter is that list. Each node states
the exact fragment required and its consumers; the deep realization
debts (base change, finiteness) are separate leaves in the
geometric-inputs chapter. Equally important is the exclusion list at the
end: operations deliberately *not* in the interface.

:::group "grp-six-operations"
Sheaf categories, the individual operations, and the exact fragment of
each that the proof uses.
:::

# Sheaf categories

:::definition "SH-constructible" (parent := "grp-six-operations") (uses := "ET-etale-site") (tags := "infrastructure") (effort := "large")
Constructible and lisse sheaves: a $`\Lambda`-sheaf on $`X` étale is
*lisse* if it is locally constant with finitely generated stalks
(equivalently, a continuous $`\pi_1`-representation on each connected
component); *constructible* if $`X` admits a finite partition into
locally closed subschemes on which it is lisse. Closure properties:
kernels, cokernels, extensions, pullbacks, tensor products; the
noetherian induction principle "prove it on a dense open, then on the
complement". Boundedness conventions: all complexes are bounded with
constructible cohomology. Mathlib has neither notion; this is
foundational infrastructure for everything below.
:::

:::definition "SH-weil-sheaf" (parent := "grp-six-operations") (uses := "SH-constructible, ET-frobenius-dictionary") (tags := "infrastructure") (effort := "medium")
Weil sheaves: pairs $`(\mathcal{F}, \varphi)` of a constructible
$`\Qlbar`-sheaf on $`X = (X_0)_{\Fqbar}` and an isomorphism
$`\varphi \colon F_X^*\mathcal{F} \xrightarrow{\sim} \mathcal{F}`
(Frobenius descent datum, *not* required to come from a sheaf on
$`X_0` — a genuine enlargement: the scalar twists
$`\Qlbar^{(b)}` with $`F` acting by a unit $`b` are Weil sheaves that
descend only when $`b` is an $`\ell`-adic unit of the right kind).
Local Frobenii $`F_x` on stalks; twisting; duals. *The entire weight
branch is stated for Weil sheaves*, because the real-envelope trick
({bpref "PUR-real-envelope"}[]) requires scalar twists that do not
descend.
:::

# The operations, with their exact required fragments

:::definition "SIX-pullback" (parent := "grp-six-operations") (uses := "SH-constructible") (tags := "infrastructure") (effort := "medium")
$`f^*` for *all* morphisms of finite-type $`\Fq`-schemes: exact,
monoidal, preserves constructibility and lisse-ness, compatible with
Weil structures. Consumers: every devissage; restriction to strata;
Frobenius pullback itself.
:::

:::definition "SIX-rf-shriek" (parent := "grp-six-operations") (uses := "SH-constructible") (tags := "infrastructure") (effort := "large") (priority := "high")
$`R^i f_!` for *separated, finite-type* morphisms $`f`: defined via a
compactification $`f = \bar f \circ j` ($`j` open immersion, $`\bar f`
proper — Nagata, {bpref "GEO-nagata"}[]) as
$`R^i \bar f_*(j_! -)`; independence of compactification; vanishing for
$`i > 2 \dim(f)` (cohomological-dimension bound); constructibility of
the images ({bpref "GEO-finiteness"}[]); $`R^0`-and-stalk descriptions
for immersions. The blueprint consumes $`R^i f_!` of *sheaves* plus
long exact sequences — full derived categories are optional
packaging, and no triangulated-category theory is presupposed
(bounded complexes with explicit truncations suffice,
{bpref "TR-supertrace"}[]).
:::

:::theorem "SIX-proper-comparison" (parent := "grp-six-operations") (uses := "SIX-rf-shriek") (tags := "infrastructure") (effort := "small")
For proper $`f`: $`R^i f_! = R^i f_*` (take the compactification
$`j = \operatorname{id}`). Consumer: the trace formula for smooth
projective $`X` is stated for ordinary cohomology
({bpref "TR-interface-proper"}[]); this comparison is the reason no
compact-support decoration reaches the final assembly.
:::

:::theorem "SIX-localization-triangle" (parent := "grp-six-operations") (uses := "SIX-rf-shriek, ET-open-localization") (tags := "infrastructure") (effort := "medium") (priority := "high")
Localization: for a closed immersion
$`i \colon Z \hookrightarrow X` with open complement
$`j \colon U \hookrightarrow X`, the sequence
$`0 \to j_! j^* \mathcal{F} \to \mathcal{F} \to i_* i^* \mathcal{F} \to 0`
is exact, $`j_!` is exact, and applying $`R^\bullet f_!` yields the
long exact sequence relating the compactly-supported cohomologies of
$`U, X, Z`. Consumers: devissage {bpref "PUR-devissage-source"}[],
the curve estimate, additivity in the trace formula. The repository's
{bpref "ET-open-localization"}[] is the site-level core of $`j_!`.
:::

:::theorem "SIX-base-change" (parent := "grp-six-operations") (uses := "SIX-rf-shriek") (tags := "infrastructure") (effort := "medium") (priority := "high")
Compact-support base change — the exact fragment: (i) *stalk form*: for
$`f \colon X \to Y` separated finite type, a geometric point
$`\bar y \to Y`, canonically
$`(R^i f_! \mathcal{F})_{\bar y} \cong H^i_c(X_{\bar y}, \mathcal{F}|)`,
Frobenius-equivariantly when $`\bar y` lies over a closed point of
$`Y_0`; (ii) *projection form*: base change along the projections
$`\mathbb{A}^1 \times Y \to Y` (used by the Fourier transform,
{bpref "PUR-fourier-def"}[]). Both are consequences of proper base
change ({bpref "GEO-proper-base-change"}[]) combined with the
compactification definition; the blueprint requires *only* these two
instances, not a general base-change formalism.
:::

:::theorem "SIX-projection-formula" (parent := "grp-six-operations") (uses := "SIX-rf-shriek") (tags := "infrastructure") (effort := "medium")
Projection formula — the exact fragment: for $`f` separated finite
type and $`L` a *lisse* sheaf on the base,
$`R^i f_!(\mathcal{F} \otimes f^* L) \cong (R^i f_! \mathcal{F}) \otimes L`.
Consumers: Fourier inversion ({bpref "PUR-fourier-inversion"}[]) with
rank-one kernels, and the geometrically constant curve case
({bpref "PUR-constant-case"}[]) — which is precisely how *Künneth is
eliminated* from the interface: the only "product" computations ever
needed factor through this projection formula.
:::

:::theorem "SIX-finite-pushforward" (parent := "grp-six-operations") (uses := "SH-constructible") (tags := "infrastructure") (effort := "medium")
Finite pushforward: for finite $`g`, $`g_* = R^0 g_! = R g_!` is exact
on sheaves, preserves constructibility, and its stalks are
$`(g_* \mathcal{F})_{\bar y} = \bigoplus_{\bar x \mapsto \bar y}
\mathcal{F}_{\bar x}` with Frobenius permuting the summands along the
fiber and acting on each stalk through the residue extension. Consumer:
the zero-dimensional devissage {bpref "PUR-devissage-finite"}[], whose
weight computation reads off exactly this stalk description.
:::

:::theorem "SIX-rf-composition" (parent := "grp-six-operations") (uses := "SIX-rf-shriek") (tags := "infrastructure") (effort := "medium") (priority := "high")
Composition filtration (the spectral-sequence replacement): for
$`f = g \circ h` (both separated finite type) and a constructible
$`\mathcal{F}`, each $`R^n f_! \mathcal{F}` carries a natural finite
Frobenius-stable filtration whose graded pieces are subquotients of the
sheaves $`R^a g_!\, R^b h_! \mathcal{F}` with $`a + b = n`. *This
filtration is the only Leray-type datum in the entire project*: the
weight devissage consumes it exclusively through the filtration weight
bound {bpref "WT-filtration-bound"}[], so no spectral-sequence
infrastructure (pages, differentials, convergence) is ever formalized.
:::

:::proof "SIX-rf-composition"
With the compactification definition of {bpref "SIX-rf-shriek"}[], the
statement reduces to the proper case, where the filtration is the
standard one induced by the truncation filtration of
$`Rh_! \mathcal{F}` (a bounded complex): apply $`R^\bullet g_!` to the
short exact sequences of truncations and splice the resulting long
exact sequences; the subquotient description is exactly what splicing
yields, without ever organizing the data into a spectral sequence. The
formal content is bounded-complex bookkeeping over
{bpref "TR-supertrace"}[]-style truncation calculus.
:::

# Artin–Schreier theory and curve fragments

:::definition "SIX-artin-schreier" (parent := "grp-six-operations") (uses := "SH-weil-sheaf") (tags := "infrastructure") (effort := "medium")
Artin–Schreier sheaves: for a nontrivial additive character
$`\psi \colon \Fq \to \Qlbar^\times`, the rank-one lisse Weil sheaf
$`\mathcal{L}_\psi` on $`\mathbb{A}^1_{\Fq}`, obtained from the
Artin–Schreier torsor $`y^q - y = x` by pushing out along $`\psi`;
trace normalization $`t_{\mathcal{L}_\psi}(x) = \psi(\operatorname{Tr}_{\Fqn{n}/\Fq}(x))`;
additivity $`m^* \mathcal{L}_\psi \cong p_1^* \mathcal{L}_\psi \otimes p_2^* \mathcal{L}_\psi`
for the addition map $`m`; wild ramification at $`\infty` with Swan
conductor $`1` for $`\mathcal{L}_{\psi(a\cdot)}`, $`a \neq 0`. This is
the Fourier kernel.
:::

:::theorem "SIX-as-orthogonality" (parent := "grp-six-operations") (uses := "SIX-artin-schreier") (tags := "infrastructure") (effort := "medium")
Artin–Schreier orthogonality:
$$`H^i_c\bigl(\mathbb{A}^1_{\Fqbar}, \mathcal{L}_{\psi(a\cdot)}\bigr) = 0 \ \ \text{for all } i, \text{ if } a \neq 0; \qquad = \Ql(-1) \text{ concentrated in } i = 2, \text{ if } a = 0.`
:::

:::proof "SIX-as-orthogonality" (uses := "ET-curve-computations")
For $`a = 0` this is $`H^\bullet_c(\mathbb{A}^1)`
({bpref "ET-curve-computations"}[]). For $`a \neq 0`: $`H^0_c` vanishes
on the affine line for any sheaf without sections supported at points;
$`H^2_c` is the twisted coinvariants of the monodromy
({bpref "SIX-affine-curve-bounds"}[]), which vanish because
$`\mathcal{L}_{\psi(a\cdot)}` has nontrivial (wild) monodromy at
$`\infty`; and $`\chi_c = 0` by Grothendieck–Ogg–Shafarevich (rank
$`1`, Swan$`_\infty = 1`: $`\chi_c = \operatorname{rank}\cdot
\chi_c(\mathbb{A}^1) - \operatorname{Swan}_\infty = 1 - 1 = 0`) — so
$`H^1_c = 0` as well. The GOS input can be scoped to exactly this
rank-one computation, recorded inside the node rather than as a general
theorem. Consumer: Fourier inversion's kernel computation.
:::

:::theorem "SIX-affine-curve-bounds" (parent := "grp-six-operations") (uses := "SH-constructible") (tags := "infrastructure") (effort := "medium")
Affine-curve cohomology bounds: for $`U` a smooth affine connected
curve over $`\Fqbar` and $`\mathcal{G}` a constructible sheaf: (i)
$`H^i_c(U, \mathcal{G}) = 0` for $`i \notin [0, 2]`; (ii)
$`H^0_c(U, L) = 0` for $`L` lisse (no sections with proper support on
an affine curve); (iii)
$`H^2_c(U, \mathcal{G}) \cong (\mathcal{G}_{\bar\eta})_{\pi_1(U)}(-1)`
(coinvariants of the generic stalk, Tate-twisted).
:::

:::proof "SIX-affine-curve-bounds" (uses := "DU-curve-duality")
(i) is the cohomological-dimension bound for curves. (ii): a
compactly-supported section is a section vanishing near the boundary;
for a lisse sheaf on a connected curve, a section is determined by its
generic stalk, so vanishing near the punctures forces vanishing. (iii)
is the top-degree part of curve duality
({bpref "DU-curve-duality"}[]): dual to
$`H^0(U, L^\vee) = (L^\vee)^{\pi_1}`-invariants. Consumers: the
positivity route of {bpref "PUR-real-purity"}[] (pole analysis of
L-functions needs exactly (ii) and (iii)) and the concentration lemma
{bpref "PUR-fourier-concentration"}[].
:::

:::theorem "SIX-j-star-curves" (parent := "grp-six-operations") (uses := "SH-constructible") (tags := "infrastructure") (effort := "medium")
Underived $`j_*` on curves with inertia stalks: for
$`j \colon U \hookrightarrow C` a dense open immersion of smooth curves
and $`L` lisse on $`U` with generic monodromy representation $`V`, the
sheaf $`j_* L` has stalks $`(j_* L)_{\bar s} = V^{I_s}` (inertia
invariants) at boundary points $`s`, $`R^1 j_* L` has stalks
$`H^1(I_s, V)`, and $`R^{> 1} j_* L = 0` (the wild inertia is
pro-$`p`, the tame quotient pro-cyclic of order prime to $`p`, and both
have $`\ell`-cohomological dimension $`\leq 1` on
$`\ell`-adic modules). Consumers: the statement of
{bpref "MON-boundary-m1"}[]/{bpref "MON-r1j-m2"}[], the middle
extension in {bpref "PUR-projective-curve"}[], and the local terms of
the stationary-phase sequence {bpref "LFT-stationary-phase"}[].
:::

:::theorem "SIX-frobenius-equivariance" (parent := "grp-six-operations") (uses := "SH-weil-sheaf, SIX-rf-shriek") (tags := "infrastructure") (effort := "medium")
Frobenius equivariance: every operation above ($`f^*`, $`R^i f_!`,
$`\otimes`, finite $`g_*`, $`j_*` on curves) carries Weil structures to
Weil structures, compatibly with composition, stalk formulas, and the
localization sequence; the induced Frobenius on
$`(R^i f_! \mathcal{F})_{\bar y}` matches, under the stalk formula, the
Frobenius on $`H^i_c` of the fiber. Without this node no weight
statement about images of operations would even be well-formed.
:::

# Deliberate exclusions

Not in the interface, with the reason: *$`Rf^!` and the duality functor
$`D`* — only the two duality *statements*
({bpref "DU-poincare-duality"}[], {bpref "DU-curve-duality"}[]) are
consumed, never a duality formalism; *general $`Rf_*`* — only finite
pushforward and $`j_*` on curves appear; *internal Hom* — duals of
lisse sheaves suffice; *derived tensor* — all twists are by lisse
(flat) sheaves; *Künneth* — eliminated by the projection formula (see
{bpref "SIX-projection-formula"}[]); *$`t`-structures and perverse
sheaves* — see the overview and {bpref "PUR-fourier-concentration"}[];
*spectral sequences* — replaced everywhere by
{bpref "WT-filtration-bound"}[] applied to the composition filtration
of {bpref "SIX-rf-shriek"}[]. Every exclusion shrinks the realization
debt; none is a mathematical loss for the target theorem.
