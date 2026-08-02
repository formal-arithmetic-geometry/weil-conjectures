import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Deep geometric inputs" =>

The leaves of the realization layer: the SGA-scale theorems (proper base
change, finiteness, duality) and the four deep leaves of the weight
machinery (boundary monodromy, Jordan-block purity, local Fourier
theory, tame reduction, real-sheaf purity), each with the narrowest
statement that unlocks its consumers and an explicit elimination plan.
Also the scheme-theoretic reductions the devissage consumes. Every node
here is either a `deep-input` (planned temporary axiom with a
decomposition recorded for its eventual proof) or standard
scheme-theoretic `infrastructure`.

:::group "grp-geometric"
Deep realization theorems and scheme-theoretic reductions.
:::

:::group "grp-monodromy"
Boundary monodromy and local Fourier theory on curves.
:::

# SGA-scale realization theorems

:::theorem "GEO-proper-base-change" (parent := "grp-geometric") (uses := "ET-etale-site") (tags := "deep-input") (effort := "large")
Proper base change, finite coefficients: for a proper morphism
$`f \colon X \to Y` of schemes and a torsion abelian sheaf (or
$`\ZZ/\ell^\nu\ZZ`-sheaf) $`\mathcal{F}` on $`X`, the base-change map
$`(R^i f_* \mathcal{F})_{\bar y} \to H^i(X_{\bar y}, \mathcal{F}|)` is
an isomorphism for every geometric point $`\bar y` of $`Y`; more
generally $`g^* R^i f_* \cong R^i f'_* g'^*` for any cartesian square
with $`f` proper. Realization debt of {bpref "SIX-base-change"}[].
:::

:::proof "GEO-proper-base-change" (uses := "GEO-smooth-base-change")
Deep input (SGA 4 XII). Planned internal decomposition when attacked:
(1) reduce to $`Y` strictly henselian local, $`\mathcal{F}`
constructible; (2) the key case is $`f` projective, by Chow's lemma
plus the composition devissage; (3) for projective space, induct on
dimension via hyperplane pencils; (4) the crucial degree-$`0`-and-$`1`
computation for relative curves rests on the theorem on formal
functions or, in the Artin approach, on algebraization of étale covers
of henselian pairs; (5) smooth base change
({bpref "GEO-smooth-base-change"}[]) enters via the standard
limit/specialization arguments. The blueprint records these stages so
the eventual formalization can be planned; until then this leaf is the
largest single realization debt.
:::

:::theorem "GEO-smooth-base-change" (parent := "grp-geometric") (uses := "ET-etale-site") (tags := "deep-input") (effort := "large")
Smooth base change, finite coefficients (torsion prime to the residue
characteristics): $`g^* R^i f_* \cong R^i f'_* g'^*` for cartesian
squares with $`g` smooth. Not consumed directly by any weight node; it
is listed because the internal decompositions of
{bpref "GEO-proper-base-change"}[] and {bpref "GEO-finiteness"}[] use
it (specialization and acyclicity arguments), and because local
acyclicity of smooth maps is the geometric input behind the "formation
of $`j_*` commutes with the fibers" clause of
{bpref "GEO-tame-reduction"}[].
:::

:::proof "GEO-smooth-base-change"
Deep input (SGA 4 XVI): reduction to relative dimension one and to
henselian traits, then the explicit computation of nearby fibers of
$`\mathbb{A}^1`-families via the specialization of tame fundamental
groups. Recorded as a leaf with no current elimination plan — it is
scheduled together with {bpref "GEO-proper-base-change"}[].
:::

:::theorem "GEO-finiteness" (parent := "grp-geometric") (uses := "ET-etale-site, SH-constructible") (tags := "deep-input") (effort := "large")
Finiteness/constructibility: for $`f \colon X \to Y` separated of
finite type between finite-type $`\Fq`-schemes (or over any field) and
$`\mathcal{F}` constructible with finite coefficients,
$`R^i f_! \mathcal{F}` is constructible and vanishes for
$`i > 2\dim(X/Y)`; in particular all
$`H^i_c(X, \Lambda_\nu)` are finite, which feeds the ℓ-adic
finite-dimensionality ({bpref "ET-adic-formalism"}[]) and hence every
"finite-dimensional $`K`-space" in the interface.
:::

:::proof "GEO-finiteness" (uses := "GEO-proper-base-change, GEO-nagata")
Deep input (SGA 4½, Th. finitude). Decomposition: compactify
({bpref "GEO-nagata"}[]), reduce to proper $`f`; for proper $`f` use
proper base change {bpref "GEO-proper-base-change"}[] to compute
stalks as cohomology of proper fibers and devissage on stratifications;
the curve case is the concrete anchor (finiteness of
$`H^\bullet` of curves over algebraically closed fields, via the
Kummer/Artin–Schreier coverings and finiteness of Picard). The
cohomological-dimension bound comes from the curve fibration argument.
:::

:::theorem "GEO-duality-realization" (parent := "grp-geometric") (uses := "ET-etale-site, ET-tate-twist") (tags := "deep-input") (effort := "large")
Duality realization package: the cycle class/Gysin machinery producing
{bpref "DU-trace-map"}[], {bpref "DU-cup-pairing"}[],
{bpref "DU-poincare-duality"}[], and {bpref "DU-curve-duality"}[]:
Kummer class of a divisor; purity for smooth pairs
($`H^i_Z(X) \cong H^{i-2c}(Z)(-c)` for $`Z \subseteq X` smooth of
codimension $`c` — provable by deformation to the normal cone plus the
$`\mathbb{A}^1`-computations); the fundamental class; and the duality
pairing's perfectness by reduction to curves. This node groups the
*construction* debts; the four consumer statements remain separate
nodes so the graph shows exactly which of them each downstream result
needs.
:::

:::proof "GEO-duality-realization"
Deep input (SGA 4 XVIII / SGA 4½ Dualité). Planned order: Kummer
theory and the divisor class (elementary given
{bpref "ET-curve-computations"}[]); relative purity by deformation to
the normal cone (the algebraic families argument avoids resolution);
trace map by gluing the $`\mathbb{A}^d`-normalization; perfectness on
curves by explicit Ext-computations with inertia
({bpref "SIX-j-star-curves"}[]); perfectness in general by fibering
into curves and the projection formula. Poincaré duality is scheduled
*after* the trace formula chain since the main theorem consumes duality
only through the two statements already isolated.
:::

# Scheme-theoretic reductions

:::theorem "GEO-nagata" (parent := "grp-geometric") (tags := "infrastructure") (effort := "large")
Nagata compactification: a separated finite-type morphism of
qcqs schemes factors as an open immersion followed by a proper
morphism. Required exactly once — to *define* $`R f_!`
({bpref "SIX-rf-shriek"}[]) and know independence of the choice (any
two compactifications are dominated by a third). Mathlib status: not
present; substantial AG infrastructure.
:::

:::theorem "GEO-noether-normalization" (parent := "grp-geometric") (tags := "infrastructure") (effort := "medium")
Relative Noether normalization / fibration into curves: after shrinking
the base and the source, any dominant morphism of integral finite-type
schemes of relative dimension $`n` factors, over a dense open, into a
chain of $`n` morphisms each of relative dimension $`1` (composed with
a finite map). Consumer: devissage step (4) of
{bpref "PUR-weight-estimate"}[]. Mathlib has affine Noether
normalization for algebras; the geometric relative form over a dense
open is missing but standard.
:::

:::theorem "GEO-curve-compactification" (parent := "grp-geometric") (tags := "infrastructure") (effort := "medium")
Smooth compactification of curves: a smooth separated curve over a
field embeds as a dense open in a unique smooth projective curve
(normalization of the projective closure). Consumers:
{bpref "PUR-curve-estimate"}[], the statement of
{bpref "PUR-projective-curve"}[]. Mathlib status: function-field/curve
correspondence partially developed (`AlgebraicGeometry/Curve` bundle
still limited); flagged for verification when scheduled.
:::

:::theorem "GEO-finite-to-p1" (parent := "grp-geometric") (tags := "infrastructure") (effort := "medium")
Finite maps to $`\mathbb{P}^1`: every smooth projective curve over a
field admits a finite, generically étale morphism to
$`\mathbb{P}^1` (any non-constant separable rational function).
Consumer: reduction step (i) of {bpref "PUR-projective-curve"}[].
:::

:::theorem "GEO-zmt" (parent := "grp-geometric") (tags := "infrastructure") (effort := "large")
Zariski's main theorem (quasi-finite form): a separated quasi-finite
morphism of finite type factors as an open immersion followed by a
finite morphism. Consumer: devissage 6
({bpref "PUR-devissage-finite"}[]) — reduces all quasi-finite pieces
to the finite + open-immersion cases. Mathlib status: not present in
this form.
:::

:::theorem "GEO-tame-reduction" (parent := "grp-geometric") (tags := "deep-input, temporary-axiom") (effort := "large")
TAME — relative tame-curve normal form: given a relative curve
situation as produced by the devissage (family of affine curves with a
lisse pure sheaf), after shrinking the base, a finite radicial base
change, and a finite (generically étale) cover of the total space, the
situation embeds as a direct summand into the controlled normal form
of {bpref "PUR-relative-curve"}[]: smooth projective relative curve,
boundary divisor finite étale over the base, sheaf tame along the
boundary, and formation of $`j_*` commuting with passage to geometric
fibers.
:::

:::proof "GEO-tame-reduction"
Deep input; initially a temporary axiom. Internal content when
attacked: semistable-type curve geometry, Abhyankar's lemma (tameness
after prime-to-$`p` covers), generic local acyclicity (via
{bpref "GEO-smooth-base-change"}[]) for the commutation clause.
*Elimination plan (preferred)*: switch
{bpref "PUR-relative-curve"}[] to route (b) — fiberwise punctual
bounds via {bpref "PUR-curve-estimate"}[] plus the real-envelope
globalization ({bpref "PUR-real-envelope"}[],
{bpref "PUR-real-purity"}[] applied on strata of the base, using the
coprimality of the fiberwise numerators and denominators forced by the
weight gap between $`H^1_c` and $`H^2_c`). Route (b) trades TAME for a
second use of PUR; the lecture notes carry both, and the blueprint
keeps (a) as primary with (b) as the recorded elimination.
:::

# Boundary monodromy (MON)

:::theorem "MON-boundary-m1" (parent := "grp-monodromy") (uses := "SIX-j-star-curves, WT-sheaf-punctual") (tags := "deep-input, temporary-axiom") (effort := "large") (priority := "high")
M1 — boundary weights of inertia invariants: let
$`j \colon U_0 \hookrightarrow C_0` be a dense open immersion of
smooth curves over $`\Fq`, $`L_0` lisse punctually $`\iota`-pure of
weight $`w` on $`U_0`, $`s` a boundary closed point, $`V =
L_{\bar\eta}` the generic stalk with inertia $`I_s` and local
Frobenius $`F_s` acting on $`V^{I_s} = (j_* L)_{\bar s}`. Then
$`V^{I_s}` is $`\iota`-mixed of weights $`\leq w` (relative to
$`q_s`).
:::

:::proof "MON-boundary-m1" (uses := "TR-l-function, SIX-affine-curve-bounds, LA-locally-finite-products")
Deep input, *but with an elementary elimination already scripted in
the lecture notes* (semicontinuity capsule): for each $`m`, apply
$`\iota` to the L-function identity ({bpref "TR-l-function"}[]) for
the $`2m`-th tensor power of the middle extension on the *complete*
curve. The left side is a product of local factors with the boundary
factor $`\det(1 - t F_s | (V^{\otimes 2m})^{I_s})^{-1}` among them;
$`(V^{I_s})^{\otimes 2m} \subseteq (V^{\otimes 2m})^{I_s}`. The right
side has poles only from $`H^0` and $`H^2` of the complete curve,
whose weights are pinned by invariants/coinvariants
({bpref "SIX-affine-curve-bounds"}[]); comparing radii of the
$`\iota`-images (positivity of coefficients for the even powers makes
radius comparison legitimate factor by factor,
{bpref "LA-locally-finite-products"}[]) bounds every eigenvalue
$`\beta` of $`F_s` on $`V^{I_s}` by
$`\|\iota\beta\|^{2 \cdot 2m} \leq q_s^{2m w + O(1)}`; letting
$`m \to \infty` gives $`\|\iota\beta\|^2 \leq q_s^{w}`. Scheduled to
be proved (not axiomatized) as soon as {bpref "TR-l-function"}[] is
available.
:::

:::theorem "MON-r1j-m2" (parent := "grp-monodromy") (uses := "SIX-j-star-curves, WT-sheaf-punctual") (tags := "deep-input") (effort := "medium")
M2 — boundary weights of $`R^1 j_*`: in the situation of
{bpref "MON-boundary-m1"}[], the stalk
$`(R^1 j_* L)_{\bar s} = H^1(I_s, V)` is $`\iota`-mixed of weights
$`\geq w + 2`.
:::

:::proof "MON-r1j-m2" (uses := "MON-boundary-m1, DU-curve-duality, WT-twist-shift")
Local duality: $`H^1(I_s, V)` is dual to $`(V^\vee)^{I_s}(1)`
(inertia cohomology of a curve trait — the local component of
{bpref "DU-curve-duality"}[]). $`V^\vee` is pure of weight $`-w`, so
{bpref "MON-boundary-m1"}[] bounds $`(V^\vee)^{I_s}` by $`\leq -w`;
dualizing flips to $`\geq w` and the Tate twist $`(1)` in the pairing
adds $`+2` ({bpref "WT-twist-shift"}[]). So M2 is *not* an
independent axiom: it is M1 for the dual plus local duality.
:::

:::theorem "MON-jordan-purity" (parent := "grp-monodromy") (uses := "SIX-j-star-curves, WT-sheaf-punctual") (tags := "deep-input, temporary-axiom") (effort := "large")
M3 — Jordan-block purity (length two): let $`M` be the stalk at a
boundary point of a lisse sheaf pure of weight $`w'` on a punctured
neighbourhood, and suppose inertia acts on a quotient $`Q` of $`M`
unipotently through a single Jordan block of length two whose
invariants have been removed (the shape produced by
{bpref "LFT-stationary-phase"}[]). Then $`Q` is $`\iota`-pure of
weight $`w' + 1`.
:::

:::proof "MON-jordan-purity"
Deep input — the genuinely weight-monodromy-flavoured residue of the
route, kept as narrow as possible: only *tame, unipotent, length-two*
blocks, only on curves. (The general weight-monodromy conjecture is
far stronger and nowhere needed.) When attacked: the monodromy
filtration of a length-two unipotent action is
$`0 \subseteq \ker N \subseteq M`, $`N` the log of the unipotent
generator; $`N` induces a Frobenius-equivariant isomorphism
$`\operatorname{gr}_1 \xrightarrow{\sim} \operatorname{gr}_{-1}(-1)`
(twist by the cyclotomic action on tame inertia), which forces the two
graded weights to differ by exactly $`2` and to straddle $`w'`
symmetrically; combined with the upper bound $`\leq w'` on invariants
({bpref "MON-boundary-m1"}[]) this pins the quotient at $`w' + 1`.
Elimination scheduled after {bpref "LFT-stationary-phase"}[], whose
formal setting provides the $`N`-operator.
:::

:::lemma_ "MON-stationary-bookkeeping" (parent := "grp-monodromy") (uses := "WT-pure") (tags := "elementary-missing") (effort := "small")
Stationary-phase weight arithmetic (abstract): given a
Frobenius-equivariant exact sequence $`0 \to I \to M \to Q \to 0` of
modules over a point where $`M` is pure of an unknown weight $`w'`,
$`Q` is pure of weight $`w + 2` (computed independently), and $`Q` is
also pure of weight $`w' + 1` (from {bpref "MON-jordan-purity"}[]),
then $`w' = w + 1` and $`I` is mixed of weights $`\leq w + 1`.
:::

:::proof "MON-stationary-bookkeeping" (uses := "WT-separation")
$`Q \neq 0` pure of two weights forces $`w' + 1 = w + 2`
({bpref "WT-separation"}[] uniqueness), so $`w' = w + 1`; $`I
\subseteq M` inherits the eigenvalue bound $`\leq w' = w + 1`
(submodule eigenvalues inject). Pure module arithmetic only — three
lines in Lean once {bpref "WT-separation"}[] is in place, which it
already is.
:::

# Local Fourier theory (LFT)

:::theorem "LFT-stationary-phase" (parent := "grp-monodromy") (uses := "PUR-fourier-def, SIX-j-star-curves") (tags := "deep-input, temporary-axiom") (effort := "large")
Stationary phase for middle extensions on the affine line: let $`L_0`
be irreducible lisse on open dense $`U_0 \subseteq \mathbb{A}^1_{\Fq}`,
not geometrically constant, unramified at $`\infty`. Then
$`\operatorname{FT}_\psi((j_* L)[1]) \cong (j'_* L')[1]` for an
irreducible lisse $`L'` on $`\mathbb{A}^1{}' \setminus \{0'\}`
(unramified outside $`0'` and $`\infty'`), and at $`0'` there is a
Frobenius- and inertia-equivariant exact sequence
$$`0 \to H^1_c(\mathbb{A}^1, j_* L) \to L'_{\bar\eta_{0'}} \to L_\infty(-1) \to 0`
in which the first term is exactly the inertia invariants
$`(L'_{\bar\eta_{0'}})^{I_{0'}}`, the inertia action on the image of
the quotient map factors through a tame unipotent length-two block
structure (the shape consumed by {bpref "MON-jordan-purity"}[]), and
$`L_\infty` denotes the (unramified) stalk of $`L` at $`\infty` with
its Frobenius.
:::

:::proof "LFT-stationary-phase" (uses := "PUR-fourier-inversion, PUR-fourier-concentration")
Deep input (Laumon's local Fourier transform / stationary phase),
kept as one narrowly-scoped statement. Internal decomposition when
attacked: local transforms
$`\operatorname{FT}(0, \infty')`, $`\operatorname{FT}(\infty, 0')`
defined on henselian traits; the global-to-local decomposition of
$`\operatorname{FT}_\psi` of a middle extension (this is where a curve
$`t`-structure fragment appears — quarantined *inside* this leaf, per
the overview's perversity policy); the principle of stationary phase
identifying the local contribution at $`\infty` with the twist
$`L_\infty(-1)` and the unipotent block; irreducibility preservation
via inversion ({bpref "PUR-fourier-inversion"}[]). Alternative route:
Katz's explicit local analysis. Until eliminated, this axiom and
{bpref "MON-jordan-purity"}[] are consumed *only* by
{bpref "PUR-affine-line"}[].
:::

# Real-sheaf purity (PUR criterion)

:::theorem "PUR-real-purity" (parent := "grp-monodromy") (uses := "WT-iota-real, WT-sheaf-punctual") (tags := "deep-input, temporary-axiom") (effort := "large") (priority := "high")
Real-sheaf purity criterion: let $`C_0` be a smooth geometrically
connected curve over $`\Fq` and $`\mathcal{G}_0` a lisse
$`\iota`-real Weil sheaf. Then every irreducible lisse subquotient of
$`\mathcal{G}_0` is punctually $`\iota`-pure of some weight (equal to
its normalized determinant weight).
:::

:::proof "PUR-real-purity" (uses := "TR-l-function, SIX-affine-curve-bounds, PUR-rank-one")
Deep input with a largely elementary internal decomposition (the
positivity route of the lecture notes), recorded for elimination:
*(1) positivity* — for even tensor powers
$`\mathcal{G}^{\otimes 2m}`, the $`\iota`-images of all local
L-factors have non-negative real coefficients (power traces are sums
of $`2m`-th powers of conjugate pairs); *(2) radius comparison* —
in a product of series with non-negative coefficients, each factor
converges wherever the product does (Cauchy–Hadamard, elementary);
*(3) pole location* — the global L-function
({bpref "TR-l-function"}[]) of the middle extension on the completed
curve has poles only from $`H^0_c`/$`H^2_c`, pinned by
{bpref "SIX-affine-curve-bounds"}[]; no $`H^1`-estimate is used —
the non-circularity hinge of the whole project; *(4) limit* —
letting $`m \to \infty` yields the one-sided bound
$`\|\iota\alpha\| \leq q_x^{\beta/2 \cdot \deg x}` with $`\beta` the
maximal normalized determinant weight; *(5) duals* reverse the
bound for irreducible pieces; *(6) exterior-power block
separation* handles reducible $`\mathcal{G}` (constituents of a real
sheaf need not be real: one separates determinant-weight blocks by
exterior powers before applying (1)–(5)); *(7) rank one* — the
terminal sub-leaf {bpref "PUR-rank-one"}[] anchors the determinant
weights. Steps (1)–(6) are elementary given
{bpref "TR-l-function"}[]; the deep residue is exactly (7).
:::

:::theorem "PUR-rank-one" (parent := "grp-monodromy") (uses := "SH-weil-sheaf") (tags := "deep-input, temporary-axiom") (effort := "large")
Rank-one purity (Katz–Lang finiteness): a rank-one lisse Weil sheaf on
a smooth geometrically connected variety over $`\Fq` has, after a
constant-field (geometrically trivial) twist, finite order: its
monodromy character has finite image on the geometric fundamental
group. Consequently every rank-one lisse Weil sheaf is punctually
$`\iota`-pure of the weight of its constant twist.
:::

:::proof "PUR-rank-one"
Deep input: geometric class field theory — the abelianized geometric
fundamental group of a curve maps onto the points of the generalized
Jacobian, and Lang's theorem ($`G(\Fqbar) \to G(\Fqbar)`,
$`g \mapsto g^{-1}F(g)` surjective for connected algebraic groups
$`G/\Fq`) makes the Frobenius-coinvariants finite; hence any character
has finite geometric image up to twist. Internal decomposition when
attacked: Lang's theorem (an isolated, self-contained node about
algebraic groups — a good early target), generalized Jacobians, and
the reciprocity map. This is the arithmetic anchor of all weights: it
is where "Frobenius eigenvalues of determinants are $`q`-Weil numbers
of some weight" ultimately comes from.
:::
