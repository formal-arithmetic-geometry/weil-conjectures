import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Purity" =>

The purity branch proves interface hypothesis AX4. Root statement: for
smooth projective $`X/\Fq`, every eigenvalue of geometric Frobenius on
$`H^i(X_{\Fqbar}, \Ql)` is pure of weight $`i`. This is *not a leaf*:
following the lecture notes it decomposes as (1) a duality squeeze
reducing purity to a weight *upper bound* in all degrees; (2) the
Deligne–Laumon weight estimate for $`R^i f_!`, proved by (3) six explicit
devissages down to (4) a controlled relative curve, whose heart is (5)
the affine-line estimate proved with the Fourier–Deligne transform. The
deep leaves reached at the bottom — real-sheaf purity, boundary
monodromy, local Fourier theory, tame reduction — live in the
geometric-inputs chapter with explicit statements and elimination plans.
The route uses *no* induction on dimension via Lefschetz pencils, no
weak or hard Lefschetz, no vanishing cycles, no decomposition theorem,
and no perverse t-structure on the critical path (the customary perverse
step is replaced by the sheaf-level concentration lemma below).

:::group "grp-purity"
Deligne's purity theorem via the Fourier route: squeeze, weight
estimate, devissages, curve theorems, Fourier transform.
:::

# The target and the squeeze

:::theorem "PUR-smooth-proper" (parent := "grp-purity") (uses := "WT-universal, ET-etale-site") (tags := "deep-input") (effort := "large") (priority := "high")
Purity for smooth proper varieties (realizes AX4): let $`X_0` be smooth
and proper over $`\Fq`, pure of dimension $`d`, $`\ell \neq p`. For
every $`i`, every ring homomorphism $`\iota \colon \Qlbar \to \CC`, and
every eigenvalue $`\alpha` of geometric Frobenius on
$`H^i(X_{\Fqbar}, \Ql) \otimes \Qlbar`:
$$`\|\iota\alpha\|^2 = q^{i}.`
No algebraicity is asserted (that is Layer I's
{bpref "W-algebraicity"}[]). Properness suffices; projectivity is not
needed in this branch.
:::

:::proof "PUR-smooth-proper" (uses := "PUR-duality-squeeze")
Exactly the duality squeeze {bpref "PUR-duality-squeeze"}[] applied
with the upper bound {bpref "PUR-upper-bound"}[] in both degree $`i`
and degree $`2d - i`.
:::

:::theorem "PUR-duality-squeeze" (parent := "grp-purity") (uses := "WT-mixed, DU-poincare-duality") (tags := "elementary-missing") (effort := "small") (priority := "high")
Duality squeeze: suppose (a) for all $`j`, $`H^j := H^j(X_{\Fqbar},
\Ql)\otimes\Qlbar` is $`\iota`-mixed of weights $`\leq j` (upper bound
only), and (b) Poincaré duality
$`H^i \cong (H^{2d-i})^\vee(-d)` Frobenius-equivariantly. Then each
$`H^i` is $`\iota`-pure of weight $`i`.
:::

:::proof "PUR-duality-squeeze" (uses := "PUR-upper-bound, WT-twist-shift")
Let $`\alpha` be an eigenvalue on $`H^i`. Upper bound at $`i`:
$`\|\iota\alpha\|^2 \leq q^i`. By duality and the twist arithmetic
({bpref "WT-twist-shift"}[]), $`\alpha = q^d/\beta` for an eigenvalue
$`\beta` on $`H^{2d-i}`; the upper bound at $`2d - i` gives
$`\|\iota\beta\|^2 \leq q^{2d-i}`, whence
$`\|\iota\alpha\|^2 = q^{2d}/\|\iota\beta\|^2 \geq q^{2d - (2d-i)} =
q^i`. Both inequalities force equality. *The lower bound needs no new
theorem* — only the same upper bound in the complementary degree; this
is the pivot of the whole route.
:::

:::theorem "PUR-upper-bound" (parent := "grp-purity") (uses := "WT-sheaf-mixed") (tags := "elementary-missing") (effort := "small")
Absolute upper bound: for $`X_0` separated of finite type over $`\Fq`
and $`\mathcal{F}_0` a Weil sheaf, $`\iota`-mixed of weights $`\leq w`,
the module $`H^i_c(X, \mathcal{F})` is $`\iota`-mixed of weights
$`\leq w + i`. In particular for the constant sheaf ($`w = 0`) on
smooth proper $`X` (where $`H_c = H`): weights of $`H^i` are
$`\leq i`.
:::

:::proof "PUR-upper-bound" (uses := "PUR-weight-estimate, SIX-proper-comparison")
The case $`Y_0 = \Spec \Fq` of the relative weight estimate
{bpref "PUR-weight-estimate"}[], plus the proper comparison for the
application to $`H^i`. *Why the general-sheaf relative statement
cannot be avoided*: any attempted direct proof for the constant sheaf
fibers $`X` over lower-dimensional bases, and the higher direct images
along the fibers are *non-constant lisse sheaves* on the base strata —
the class of coefficients is forced to grow to mixed Weil sheaves, and
the induction vehicle is the relative statement.
:::

# The weight estimate and the six devissages

:::theorem "PUR-weight-estimate" (parent := "grp-purity") (uses := "WT-sheaf-mixed, SIX-rf-shriek") (tags := "deep-input") (effort := "large") (priority := "high")
Deligne–Laumon weight estimate: let
$`f \colon X_0 \to Y_0` be a separated morphism of finite-type
$`\Fq`-schemes and $`\mathcal{F}_0` a constructible Weil sheaf on
$`X_0`, $`\iota`-mixed of weights $`\leq w`. Then for every $`i`,
$`R^i f_! \mathcal{F}_0` is $`\iota`-mixed of weights $`\leq w + i` —
for every $`\iota` simultaneously.
:::

:::proof "PUR-weight-estimate" (uses := "PUR-devissage-exact, PUR-devissage-source, PUR-devissage-target, PUR-devissage-composition, PUR-devissage-homeo, PUR-devissage-finite, PUR-relative-curve, GEO-noether-normalization")
Induction on $`\dim X_0`. The six devissages reduce the general
statement to the controlled relative-curve normal form: (1) exact
sequences and the Serre-closure of mixedness reduce to
$`\mathcal{F}_0` irreducible-ish pieces
({bpref "PUR-devissage-exact"}[]); (2) source localization reduces to
a dense open of $`X_0` and its lower-dimensional complement
({bpref "PUR-devissage-source"}[]); (3) target localization to a dense
open of $`Y_0` ({bpref "PUR-devissage-target"}[]); (4) composition
splits $`f` through relative curves: by Noether normalization in
relative form ({bpref "GEO-noether-normalization"}[]), after
shrinking, $`f` factors as a chain of relative curves and finite maps,
and the composition devissage ({bpref "PUR-devissage-composition"}[])
reduces to one relative curve at a time; (5) universal homeomorphisms
(e.g. radicial base changes needed by the normal form) change nothing
({bpref "PUR-devissage-homeo"}[]); (6) finite morphisms are dimension
zero and handled directly ({bpref "PUR-devissage-finite"}[]). The
remaining case is {bpref "PUR-relative-curve"}[].
:::

:::lemma_ "PUR-devissage-exact" (parent := "grp-purity") (uses := "WT-sheaf-mixed, SIX-rf-shriek") (tags := "elementary-missing") (effort := "small")
Devissage 1 (exactness): if
$`0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0` is exact
and the estimate holds for $`\mathcal{F}'` and $`\mathcal{F}''`, it
holds for $`\mathcal{F}`; mixedness of weights $`\leq w` passes to
subsheaves, quotients, and extensions.
:::

:::proof "PUR-devissage-exact" (uses := "WT-filtration-bound")
The long exact sequence of $`R^\bullet f_!` exhibits
$`R^i f_! \mathcal{F}` between $`R^i f_! \mathcal{F}'` and
$`R^i f_! \mathcal{F}''`; apply the filtration bound
{bpref "WT-filtration-bound"}[] (two-step filtration by the image of
the first). Serre-closure of mixedness: concatenate/refine filtrations.
:::

:::lemma_ "PUR-devissage-source" (parent := "grp-purity") (uses := "WT-sheaf-mixed, SIX-localization-triangle") (tags := "elementary-missing") (effort := "small")
Devissage 2 (source localization): for
$`j \colon U_0 \hookrightarrow X_0` dense open with closed complement
$`i \colon Z_0 \hookrightarrow X_0`, if the estimate holds for
$`(f \circ j,\ j^*\mathcal{F})` and $`(f \circ i,\ i^*\mathcal{F})`, it
holds for $`(f, \mathcal{F})`.
:::

:::proof "PUR-devissage-source" (uses := "WT-filtration-bound")
$`0 \to j_! j^*\mathcal{F} \to \mathcal{F} \to i_* i^*\mathcal{F} \to 0`
({bpref "SIX-localization-triangle"}[]); $`R f_!` of the outer terms
computes $`R (f j)_!` and $`R (f i)_!` (composition with an immersion,
where the compactification definition makes this a tautology); conclude
by the long exact sequence and {bpref "WT-filtration-bound"}[]. This
is the devissage that drives the induction on $`\dim X_0` (the
complement has smaller dimension).
:::

:::lemma_ "PUR-devissage-target" (parent := "grp-purity") (uses := "WT-sheaf-mixed, SIX-base-change") (tags := "elementary-missing") (effort := "small")
Devissage 3 (target localization): weights of a sheaf on $`Y_0` are
detected pointwise, so the estimate for $`f` may be checked after
restricting $`Y_0` to a dense open and to its (lower-dimensional)
closed complement separately.
:::

:::proof "PUR-devissage-target" (uses := "WT-filtration-bound, SIX-localization-triangle")
Punctual purity is a stalkwise notion and the stalk of
$`R^i f_!\mathcal{F}` at $`\bar y` is $`H^i_c` of the fiber
({bpref "SIX-base-change"}[](i)), which only sees the base change of
$`f` over the part of $`Y_0` containing $`y`. Mixedness filtrations
glue from a decomposition of $`Y_0` by extending filtrations from the
open part and correcting on the closed part (a finite refinement
argument via {bpref "WT-filtration-bound"}[]).
:::

:::lemma_ "PUR-devissage-composition" (parent := "grp-purity") (uses := "WT-sheaf-mixed, SIX-rf-composition") (tags := "elementary-missing") (effort := "small")
Devissage 4 (composition): if the estimate holds for $`g` and for
$`h`, it holds for $`f = g \circ h`.
:::

:::proof "PUR-devissage-composition" (uses := "WT-filtration-bound")
$`R^n f_! \mathcal{F}` carries the finite Frobenius-stable filtration
with graded pieces subquotients of $`R^a g_! R^b h_! \mathcal{F}`,
$`a + b = n` ({bpref "SIX-rf-composition"}[]); by hypothesis
$`R^b h_! \mathcal{F}` is mixed $`\leq w + b` and then
$`R^a g_! (\cdot)` is mixed $`\leq w + b + a = w + n`; conclude by
{bpref "WT-filtration-bound"}[]. *No spectral sequence* — this is
the only consumer of the composition filtration.
:::

:::lemma_ "PUR-devissage-homeo" (parent := "grp-purity") (uses := "WT-sheaf-mixed") (tags := "elementary-missing") (effort := "small")
Devissage 5 (universal homeomorphisms): a universal homeomorphism
(e.g. Frobenius twists, radicial covers, normalization in purely
inseparable extensions) induces an equivalence of étale topoi
compatible with all operations and Weil structures; the estimate is
invariant under composing $`f` with such maps on either side.
:::

:::proof "PUR-devissage-homeo"
Topological invariance of the étale site (a universal homeomorphism
induces an equivalence of small étale sites — recorded as part of
{bpref "ET-etale-site"}[]'s interface); the induced identifications
match Frobenius structures because the $`q`-power endomorphism commutes
with everything. The devissage is bookkeeping once the equivalence is
in the interface.
:::

:::lemma_ "PUR-devissage-finite" (parent := "grp-purity") (uses := "WT-sheaf-mixed, SIX-finite-pushforward") (tags := "elementary-missing") (effort := "small")
Devissage 6 (relative dimension zero): for $`g` finite,
$`g_* = R^0 g_!` preserves "mixed of weights $`\leq w`". Combined with
Zariski's main theorem ({bpref "GEO-zmt"}[]: quasi-finite separated =
open immersion into finite), this settles all quasi-finite pieces of
the normal form.
:::

:::proof "PUR-devissage-finite"
Stalks of $`g_* \mathcal{F}` are sums over the fiber
({bpref "SIX-finite-pushforward"}[]). Weight arithmetic at a point
$`y` under $`x \mapsto y` with residue extension of degree $`e`:
$`q_x = q_y^e`, and the Frobenius $`F_y` on the summand indexed by
$`x` satisfies $`F_y^{e} = F_x` up to permutation of the $`e` embedded
copies; an eigenvalue $`\beta` of $`F_x` with
$`\|\iota\beta\|^2 \leq q_x^w` contributes eigenvalues $`\alpha` with
$`\alpha^e = \zeta\beta` (roots of unity from the permutation), so
$`\|\iota\alpha\|^2 = \|\iota\beta\|^{2/e} \leq q_x^{w/e} = q_y^w`.
Filtrations push forward exactly ($`g_*` exact), so mixedness is
preserved.
:::

# The curve theorems

:::theorem "PUR-relative-curve" (parent := "grp-purity") (uses := "WT-sheaf-mixed, SIX-rf-shriek") (tags := "elementary-missing") (effort := "large")
Controlled relative curve case: let
$`\bar f \colon \bar X_0 \to Y_0` be a smooth projective relative
curve, $`D_0 \subseteq \bar X_0` a divisor finite étale over $`Y_0`,
$`X_0 = \bar X_0 \setminus D_0`, $`f = \bar f|_{X_0}`, and
$`\mathcal{F}_0` lisse and punctually $`\iota`-pure of weight $`w` on
$`X_0`, tamely controlled along $`D_0` in the sense of the normal form
{bpref "GEO-tame-reduction"}[]. Then $`R^r f_! \mathcal{F}_0` is
$`\iota`-mixed of weights $`\leq w + r` for all $`r`.
:::

:::proof "PUR-relative-curve" (uses := "PUR-projective-curve, MON-boundary-m1, SIX-base-change, SIX-j-star-curves, PUR-devissage-exact, GEO-tame-reduction")
Route (a) of the lecture notes. On $`\bar X_0` consider
$`0 \to j_! \mathcal{F} \to j_* \mathcal{F} \to
i_* \mathcal{B} \to 0` where $`j \colon X_0 \hookrightarrow \bar X_0`,
$`i \colon D_0 \hookrightarrow \bar X_0`, and
$`\mathcal{B}` is the boundary sheaf of inertia invariants
({bpref "SIX-j-star-curves"}[]). Fiberwise over $`\bar y \in Y_0`:
$`H^r` of the compactified fiber with coefficients
$`j_* \mathcal{F}|` is pure of weight $`w + r` by projective-curve
purity ({bpref "PUR-projective-curve"}[]) — the tame control of
{bpref "GEO-tame-reduction"}[] guarantees the formation of
$`j_*\mathcal{F}` commutes with passage to fibers; the boundary term
is mixed of weights $`\leq w` by
{bpref "MON-boundary-m1"}[] and lives on the finite étale $`D_0`
({bpref "PUR-devissage-finite"}[]). The long exact sequence of
$`R^\bullet \bar f_*` (compact supports = ordinary, $`\bar f` proper)
and the stalkwise identification ({bpref "SIX-base-change"}[]) give
the bound for $`R^r f_! \mathcal{F} = R^r \bar f_*(j_!\mathcal{F})`
via {bpref "PUR-devissage-exact"}[]. *Recorded alternative — route
(b)*: replace {bpref "GEO-tame-reduction"}[] by fiberwise punctual
bounds from the curve estimate plus the real-envelope argument
({bpref "PUR-real-envelope"}[] and {bpref "PUR-real-purity"}[] on
strata of $`Y_0`); this eliminates the TAME leaf at the cost of using
PUR on strata — the planned elimination path for
{bpref "GEO-tame-reduction"}[].
:::

:::theorem "PUR-curve-estimate" (parent := "grp-purity") (uses := "WT-sheaf-mixed") (tags := "elementary-missing") (effort := "medium")
Absolute curve estimate: for $`C_0` any finite-type curve over
$`\Fq` and $`\mathcal{F}_0` mixed of weights $`\leq w`,
$`H^i_c(C, \mathcal{F})` is mixed of weights $`\leq w + i`.
:::

:::proof "PUR-curve-estimate" (uses := "PUR-projective-curve, MON-boundary-m1, PUR-devissage-exact, PUR-devissage-source, PUR-devissage-finite, GEO-curve-compactification")
Devissage (source localization + finite maps + exactness) reduces to
$`C_0` smooth affine and $`\mathcal{F}_0` lisse punctually pure of
weight $`w`. Compactify $`j \colon C_0 \hookrightarrow \bar C_0`
({bpref "GEO-curve-compactification"}[]); the boundary sequence as in
{bpref "PUR-relative-curve"}[] with base a point: middle term pure of
weight $`w + i` by {bpref "PUR-projective-curve"}[], boundary mixed
$`\leq w` by {bpref "MON-boundary-m1"}[]; conclude with the long exact
sequence. ($`i = 0, 2` are the trivial cases
{bpref "SIX-affine-curve-bounds"}[]: $`H^0_c` vanishes,
$`H^2_c` = coinvariants$`(-1)`, of weight $`\leq w + 2` since
coinvariants are a quotient.)
:::

:::theorem "PUR-projective-curve" (parent := "grp-purity") (uses := "WT-sheaf-punctual, SIX-j-star-curves") (tags := "elementary-missing") (effort := "large") (priority := "high")
Projective-curve purity for middle extensions: let $`\bar C_0` be a
smooth projective curve over $`\Fq`,
$`j \colon U_0 \hookrightarrow \bar C_0` dense open, $`L_0` lisse and
punctually $`\iota`-pure of weight $`w` on $`U_0`. Then
$`H^i(\bar C, j_* L)` is $`\iota`-pure of weight $`w + i`
($`i = 0, 1, 2`).
:::

:::proof "PUR-projective-curve" (uses := "PUR-affine-line, PUR-irreducible-reduction, PUR-constant-case, DU-curve-duality, MON-boundary-m1, MON-r1j-m2, PUR-devissage-finite, GEO-finite-to-p1")
(i) *Reduce to $`\mathbb{P}^1`*: choose a finite generically étale map
$`\bar C_0 \to \mathbb{P}^1` ({bpref "GEO-finite-to-p1"}[]); finite
pushforward preserves middle extensions over the locus where it is
étale (shrink $`U_0`) and preserves purity bounds
({bpref "PUR-devissage-finite"}[]). (ii) *Upper bound suffices*: the
dual sheaf $`L^\vee` is pure of weight $`-w`; curve duality
({bpref "DU-curve-duality"}[]) identifies
$`H^i(\bar C, j_* L) \cong H^{2-i}(\bar C, j_* L^\vee)^\vee(-1)`, so an
upper bound $`\leq -w + (2 - i)` for the dual gives a lower bound
$`\geq w + i` — purity follows from upper bounds alone.
(iii) *Irreducible reduction* is {bpref "PUR-irreducible-reduction"}[].
(iv) *Geometrically constant case* is {bpref "PUR-constant-case"}[].
(v) *Irreducible non-constant case*: first apply
{bpref "PUR-move-infinity"}[] so that (after a harmless base
extension and coordinate change) $`L` is unramified at $`\infty`.
Writing $`k \colon \mathbb{A}^1 \hookrightarrow \mathbb{P}^1` and
$`\mathcal{G} = j_* L` on $`\mathbb{P}^1`, the localization sequence
({bpref "SIX-localization-triangle"}[]) for
$`0 \to k_!(\mathcal{G}|_{\mathbb{A}^1}) \to \mathcal{G} \to
i_{\infty *}\mathcal{G}_{\infty} \to 0` gives (audited direction!)
that $`H^1(\mathbb{P}^1, \mathcal{G})` is a *quotient* of
$`H^1_c(\mathbb{A}^1, j_* L)` (the next term is $`H^1` of a
skyscraper, which vanishes); upper weight bounds pass to quotients,
so {bpref "PUR-affine-line"}[] gives weights $`\leq w + 1`.
$`H^0` and $`H^2` are invariants resp. coinvariants, handled
directly.
:::

:::lemma_ "PUR-irreducible-reduction" (parent := "grp-purity") (uses := "WT-sheaf-punctual, SIX-j-star-curves") (tags := "elementary-missing") (effort := "small")
Weight-gap exactness: for a short exact sequence
$`0 \to L' \to L \to L'' \to 0` of lisse sheaves punctually pure *of
the same weight* $`w` on $`U_0`, the sequence of middle extensions
$`0 \to j_* L' \to j_* L \to j_* L'' \to 0` on $`\bar C_0` is exact;
hence the projective-curve purity statement for $`L', L''` implies it
for $`L`, and one may assume $`L` irreducible as a lisse sheaf.
:::

:::proof "PUR-irreducible-reduction" (uses := "MON-boundary-m1, MON-r1j-m2, WT-separation")
$`j_*` is left exact; the obstruction to right exactness at a boundary
point $`s` is the connecting map
$`(j_* L'')_{\bar s} \to (R^1 j_* L')_{\bar s}`. Source has weights
$`\leq w` ({bpref "MON-boundary-m1"}[]); target has weights
$`\geq w + 2` ({bpref "MON-r1j-m2"}[]); a Frobenius-equivariant map
between modules with disjoint weight ranges vanishes
({bpref "WT-separation"}[] applied to the graph… precisely: any
equivariant map sends generalized eigenspaces to generalized
eigenspaces of the same eigenvalue, and no eigenvalue is shared). So
the connecting map is zero and the sequence is exact. This five-line
argument is the lecture notes' replacement for semisimplicity
assumptions.
:::

:::lemma_ "PUR-constant-case" (parent := "grp-purity") (uses := "WT-sheaf-punctual") (tags := "elementary-missing") (effort := "small")
Geometrically constant case: if $`L_0` is lisse, punctually pure of
weight $`w`, and geometrically constant (trivial geometric monodromy —
$`L` pulled back from the point up to Weil twist), then purity of
$`H^i(\bar C, j_* L) = H^i(\bar C, L)` reduces to the curve
computations with constant coefficients.
:::

:::proof "PUR-constant-case" (uses := "ET-curve-computations, SIX-projection-formula")
A geometrically constant Weil sheaf is $`M \otimes \Qlbar`-twist of the
pullback of a Frobenius module $`M` from the point; the projection
formula ({bpref "SIX-projection-formula"}[]) gives
$`H^i(\bar C, L) = M \otimes H^i(\bar C, \Qlbar)`, and
$`H^i(\bar C)` is pure of weight $`i` by the explicit computations
({bpref "ET-curve-computations"}[]: weights $`0, 1, 2` with the
$`H^1` case reduced to $`\mathbb{P}^1`-covers or handled by the
Jacobian-free Kummer description — for $`\mathbb{P}^1` itself $`H^1 =
0`, and step (i) of {bpref "PUR-projective-curve"}[] reduced
everything to $`\mathbb{P}^1`). Tensoring multiplies weights
({bpref "WT-twist-shift"}[]): total weight $`w + i`. *No Künneth*:
the projection formula does all the work.
:::

Audited proof-dependency corrections in this section: the target
localization devissage also consumes the localization triangle, and
the affine-line estimate consumes the middle-extension node — the
edges below reflect this.

# The Fourier transform and the affine-line estimate

:::lemma_ "PUR-move-infinity" (parent := "grp-purity") (uses := "WT-sheaf-punctual") (tags := "elementary-missing") (effort := "small")
Reduction to "unramified at $`\infty`" (exposed by the audit): let
$`L_0` be lisse punctually $`\iota`-pure on a dense open
$`U_0 \subseteq \mathbb{P}^1_{\Fq}`. After a finite extension
$`\Fq \to \Fqn{m}` (harmless by {bpref "WT-base-extension"}[]) there
is a rational point $`u \in U(\Fqn{m})`, and an automorphism of
$`\mathbb{P}^1` over $`\Fqn{m}` moves $`u` to $`\infty`. After this
change of coordinates, $`\infty` lies in the lisse locus of $`L`, so
$`L` is unramified at $`\infty` — the hypothesis of
{bpref "PUR-affine-line"}[]. Without this step the affine-line
estimate would only cover middle extensions with an unramified point
at $`\infty`, and a general middle extension on $`\mathbb{P}^1` has
no reason to present itself in that coordinate.
:::

:::proof "PUR-move-infinity" (uses := "WT-base-extension")
$`U_0` is a nonempty open of $`\mathbb{P}^1`, hence has closed
points; a closed point of degree $`m` becomes rational after the
extension of degree $`m`. $`\operatorname{PGL}_2` acts transitively
on rational points. Punctual purity and all weight bounds are
invariant under the base extension and under coordinate
automorphisms ({bpref "WT-base-extension"}[]; automorphisms are
isomorphisms of the situation). Elementary once stated — the audit
point is that it must be *stated*, because it silently changes
$`(q, F)` to $`(q^m, F^m)`.
:::

:::theorem "PUR-affine-line" (parent := "grp-purity") (uses := "WT-sheaf-punctual, SIX-artin-schreier") (tags := "elementary-missing") (effort := "large") (priority := "high")
Affine-line estimate (the heart): let
$`j \colon U_0 \hookrightarrow \mathbb{A}^1_{\Fq}` be open dense,
$`L_0` lisse on $`U_0`, irreducible as a lisse sheaf, punctually
$`\iota`-pure of weight $`w`, *not* geometrically constant, and
unramified at $`\infty`. Then $`H^1_c(\mathbb{A}^1, j_* L)` is
$`\iota`-mixed of weights $`\leq w + 1`.
:::

:::proof "PUR-affine-line" (uses := "PUR-fourier-def, PUR-fourier-concentration, PUR-ft-middle-extension, LFT-stationary-phase, PUR-real-envelope, PUR-reality-transport, PUR-real-purity, MON-boundary-m1, MON-jordan-purity, MON-stationary-bookkeeping")
The Fourier argument, following the lecture notes step by step.
*Admissibility*: $`j_* L` has no Artin–Schreier subquotient
$`\mathcal{L}_{\psi(a\cdot)}`: for $`a = 0` this would contradict
non-constancy, for $`a \neq 0` unramifiedness at $`\infty` (Swan
conductors differ). *Transform*: by the concentration lemma
({bpref "PUR-fourier-concentration"}[]) the Fourier transform of
$`j_* L` is (up to shift) a single sheaf; by middle-extension
preservation ({bpref "PUR-ft-middle-extension"}[]) that sheaf is the
middle extension $`j'_* L'` of an irreducible lisse $`L'`; local
Fourier theory ({bpref "LFT-stationary-phase"}[]) pins its lisse
locus to $`\mathbb{A}^1{}' \setminus \{0'\}` and provides the
Frobenius-and-inertia-equivariant exact sequence
$$`0 \to H^1_c(\mathbb{A}^1, j_* L) \to L'_{\bar\eta_{0'}} \to L_\infty(-1) \to 0`
whose first term is exactly the inertia invariants of the middle
term, and whose quotient carries a length-two unipotent Jordan-block
structure. *Purity of the transform*: the real envelope
({bpref "PUR-real-envelope"}[]) embeds $`L` in an $`\iota`-real sheaf
whose transform is again $`\iota`-real
({bpref "PUR-reality-transport"}[]); the real-sheaf purity criterion
({bpref "PUR-real-purity"}[]) makes $`L'` punctually pure of *some*
weight $`w'`. *Bookkeeping*: the Jordan-block purity input
({bpref "MON-jordan-purity"}[]) fixes the quotient's weight as
$`w' + 1`; since $`L_\infty(-1)` has weight $`w + 2`, the abstract
short-exact-sequence arithmetic
({bpref "MON-stationary-bookkeeping"}[]) yields $`w' = w + 1`;
finally the invariants $`H^1_c = (L'_{\bar\eta_{0'}})^{I_{0'}}` have
weights $`\leq w' = w + 1` by the boundary bound
({bpref "MON-boundary-m1"}[]) applied on the dual line.
:::

:::definition "PUR-fourier-def" (parent := "grp-purity") (uses := "SIX-artin-schreier, SIX-rf-shriek, SIX-base-change") (tags := "infrastructure") (effort := "medium")
Fourier–Deligne transform: for
$`K` on $`\mathbb{A}^1_{\Fq}` (bounded constructible, in practice a
sheaf placed in one degree),
$$`\operatorname{FT}_\psi(K) := R p_{2!}\bigl(p_1^* K \otimes m^* \mathcal{L}_\psi\bigr)[1]`
on the dual line, where $`p_1, p_2` are the projections of
$`\mathbb{A}^1 \times \mathbb{A}^1{}'` and $`m` the multiplication
(pairing) map. Stalk formula (from
{bpref "SIX-base-change"}[](ii)):
$`\operatorname{FT}_\psi(K)_{\bar a} \cong
R\Gamma_c(\mathbb{A}^1, K \otimes \mathcal{L}_{\psi(a\,\cdot)})[1]`.
:::

:::theorem "PUR-fourier-concentration" (parent := "grp-purity") (uses := "PUR-fourier-def") (tags := "elementary-missing") (effort := "medium")
Concentration lemma (perversity-free): if $`L_0` is as in
{bpref "PUR-affine-line"}[] (irreducible, not geometrically constant,
unramified at $`\infty`, extended by $`j_*`), then for every
$`a`, $`H^i_c(\mathbb{A}^1, j_* L \otimes \mathcal{L}_{\psi(a\cdot)})`
vanishes for $`i \neq 1`; hence $`\operatorname{FT}_\psi(j_* L [1])`
is a single sheaf placed in degree $`0` after the shift — the
transform of the shifted middle extension is a plain sheaf. *Audit
note*: this lemma alone replaces only the *degree* half of the
customary perverse statement; the *shape* half (that the resulting
sheaf is again a middle extension) is the separate node
{bpref "PUR-ft-middle-extension"}[], which earlier versions of this
blueprint had concealed inside the local Fourier axiom.
:::

:::proof "PUR-fourier-concentration" (uses := "SIX-affine-curve-bounds, SIX-artin-schreier")
$`H^0_c` vanishes for any sheaf with no sections supported on points
({bpref "SIX-affine-curve-bounds"}[](ii) after removing the finite
$`j_*`-boundary, where the twisted sheaf remains without punctual
sections). $`H^2_c` is the coinvariants
({bpref "SIX-affine-curve-bounds"}[](iii)) of
$`j_* L \otimes \mathcal{L}_{\psi(a\cdot)}`, which vanish: for
$`a \neq 0` the tensor factor has wild ramification at $`\infty` while
$`L` is tame there (unramified even), so the product has no trivial
quotient; for $`a = 0` irreducibility and non-constancy of $`L` kill
the coinvariants. All statements are sheaf-level; no perverse
formalism enters.
:::

:::theorem "PUR-ft-middle-extension" (parent := "grp-purity") (uses := "PUR-fourier-def, SIX-j-star-curves") (tags := "elementary-missing") (effort := "medium") (priority := "high")
Middle-extension preservation (exposed by the audit): in the situation
of {bpref "PUR-affine-line"}[], the sheaf
$`\mathcal{G}` with $`\operatorname{FT}_\psi(j_* L[1]) =
\mathcal{G}[1]` (a plain sheaf by
{bpref "PUR-fourier-concentration"}[]) satisfies: (i) $`\mathcal{G}`
is lisse on a dense open $`V' \subseteq \mathbb{A}^1{}'`; (ii)
$`\mathcal{G}` has no nonzero punctual subsheaf; (iii) at every point
of $`\mathbb{A}^1{}' \setminus V'` the stalk of $`\mathcal{G}` equals
the inertia invariants of its generic part — i.e.
$`\mathcal{G} = j'_*(\mathcal{G}|_{V'})` is the middle extension of
its lisse restriction; and (iv) $`\mathcal{G}|_{V'}` is irreducible as
a lisse sheaf.
:::

:::proof "PUR-ft-middle-extension" (uses := "PUR-fourier-inversion, SIX-as-orthogonality, SH-constructible, GEO-finiteness, PUR-fourier-concentration")
Perversity-free route (Katz-style, via inversion). (i) $`\mathcal{G}`
is constructible ({bpref "SIX-rf-shriek"}[] constructibility via
{bpref "GEO-finiteness"}[]), and a constructible sheaf on a curve is
lisse on a dense open directly from the definition of
constructibility ({bpref "SH-constructible"}[]). (ii) A punctual
subsheaf supported at $`a'` would, under the inverse transform
({bpref "PUR-fourier-inversion"}[]), produce a nonzero map from a
geometrically constant twist
$`\mathcal{L}_{\psi(a'\cdot)}(-1)`-type sheaf into $`j_* L` (the
transform of a skyscraper is a rank-one Artin–Schreier twist —
computed by {bpref "SIX-as-orthogonality"}[]); irreducibility and the
admissibility of $`L` (no Artin–Schreier constituent) forbid this.
(iii) The adjunction map $`\mathcal{G} \to j'_*(\mathcal{G}|_{V'})`
is injective by (ii) (its kernel is punctual); its cokernel $`Q` is
punctual, and applying the inverse transform to
$`0 \to \mathcal{G} \to j'_* (\mathcal{G}|_{V'}) \to Q \to 0` again
produces an Artin–Schreier-twist quotient of (a twist of) $`j_* L`,
excluded as in (ii) — so $`Q = 0`. (iv) A proper nonzero lisse
subsheaf of $`\mathcal{G}|_{V'}` middle-extends to a proper subobject
whose inverse transform is a proper subobject of $`j_* L[1]`'s
sheaf-part, contradicting irreducibility of $`L` (sub-middle
extensions of $`j_* L` correspond to monodromy subrepresentations of
$`L`). *Why the previous graph concealed this*: the statement had
been folded into the temporary axiom
{bpref "LFT-stationary-phase"}[]; splitting it out shows that this
half of the customary perverse package has an elementary proof from
inversion and orthogonality, while only the genuinely local analysis
at $`0'` and $`\infty'` remains deep.
:::

:::theorem "PUR-fourier-inversion" (parent := "grp-purity") (uses := "PUR-fourier-def") (tags := "infrastructure") (effort := "medium")
Fourier inversion:
$`\operatorname{FT}_{\psi^{-1}}\operatorname{FT}_\psi(K) \cong
a^* K(-1)` where $`a` is the antipode $`x \mapsto -x`. Consequently
$`\operatorname{FT}_\psi` is an equivalence on the relevant categories
and preserves irreducibility (used inside
{bpref "LFT-stationary-phase"}[] and the reality transport).
:::

:::proof "PUR-fourier-inversion" (uses := "SIX-base-change, SIX-projection-formula, SIX-as-orthogonality")
Kernel computation, written out in the lecture notes' appendix as a
six-step named-isomorphism chain: composing the two transforms gives
the kernel
$`R p_{13!}(\mathcal{L}_{\psi(y(x + z))})[2]` on
$`\mathbb{A}^1 \times \mathbb{A}^1`; fiberwise in $`(x, z)`, the inner
integral is $`R\Gamma_c(\mathbb{A}^1_y, \mathcal{L}_{\psi((x+z)y)})[2]`,
which by Artin–Schreier orthogonality
({bpref "SIX-as-orthogonality"}[]) vanishes off the antidiagonal
$`x + z = 0` and equals $`\Qlbar(-1)` there; base change and the
projection formula ({bpref "SIX-base-change"}[],
{bpref "SIX-projection-formula"}[]) assemble this into
$`a^* K(-1)`. Each of the six isomorphisms must be a *named* map (not
"there is an isomorphism") for the Frobenius-equivariance bookkeeping
to go through — recorded as a formalization requirement.
:::

:::lemma_ "PUR-real-envelope" (parent := "grp-purity") (uses := "WT-iota-real, SH-weil-sheaf") (tags := "elementary-missing") (effort := "small")
Real envelope: for $`L_0` lisse punctually $`\iota`-pure of weight
$`w`, the Weil sheaf
$`\mathcal{E}_0 := L_0 \oplus (L_0^\vee \otimes \Qlbar^{(b)})` is
$`\iota`-real, where $`\Qlbar^{(b)}` is the geometrically constant
Weil twist with $`\iota(b) = q^w`. ($`\mathcal{E}_0` generally does
*not* descend to an honest sheaf on $`X_0` — the twist is a genuine
Weil sheaf; this is why the entire branch works with Weil sheaves.)
:::

:::proof "PUR-real-envelope"
At each closed point the local factor of $`\mathcal{E}` is
$`\det(1 - tF_x | L)\cdot\det(1 - tF_x | L^\vee \otimes b^{\deg x})`;
the eigenvalues of the second factor are
$`b^{\deg x}/\bar{\phantom{\alpha}}`-partners: for each eigenvalue
$`\alpha` of the first, $`\iota(b^{\deg x} \alpha^{-1}) =
q_x^w \overline{\iota\alpha}/\|\iota\alpha\|^2 = \overline{\iota\alpha}`
by purity. So the $`\iota`-image of the local factor is
$`\prod (1 - \iota\alpha\, t)(1 - \overline{\iota\alpha}\, t)`, which
has real coefficients.
:::

:::lemma_ "PUR-reality-transport" (parent := "grp-purity") (uses := "WT-iota-real, PUR-fourier-def") (tags := "elementary-missing") (effort := "medium")
Reality transport: if $`\mathcal{E}_0` is $`\iota`-real and its
transforms under $`\operatorname{FT}_\psi` and
$`\operatorname{FT}_{\psi^{-1}}` are (shifts of) lisse-on-open sheaves,
then the direct sum of the two transforms is $`\iota`-real.
:::

:::proof "PUR-reality-transport" (uses := "TR-l-function")
Trace functions: the trace function of $`\operatorname{FT}_\psi
\mathcal{E}` at a point $`a` is
$`-\sum_x \psi(ax)\, t_{\mathcal{E}}(x)` (Grothendieck trace formula
{bpref "TR-l-function"}[] on the fibers), and complex conjugation
under $`\iota` exchanges $`\psi \leftrightarrow \psi^{-1}` while
fixing $`\iota t_{\mathcal{E}}` (reality of $`\mathcal{E}`). So the
$`\iota`-images of the trace functions of the two transforms are
complex conjugates, and their sum — hence every symmetric function of
local Frobenius eigenvalues, via Newton's identities over the
$`\QQ`-algebra generated — is real. Local characteristic polynomials
of the direct sum therefore have real $`\iota`-image.
:::
