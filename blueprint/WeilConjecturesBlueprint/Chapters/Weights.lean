import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Weights" =>

Weight predicates at two levels. At the *module* level (used by the final
assembly) weights are eigenvalue bounds for a single Frobenius module —
several of these nodes are already formalized and sorry-free. At the
*sheaf* level (used by the purity branch) mixedness is a filtration
condition on Weil sheaves, with punctual purity fiber by fiber. The
comparison lemma and the filtration weight bound (the spectral-sequence
surrogate) connect the two levels.

:::group "grp-weights"
Purity and mixedness predicates for Frobenius modules and Weil sheaves;
weight separation, stability, and the filtration bound.
:::

# Module-level predicates

:::definition "WT-pure" (parent := "grp-weights") (uses := "LA-eigenvalue") (lean := "Weil.IsPureWeight") (tags := "existing-project")
$`\iota`-purity: for a ring homomorphism $`\iota \colon K \to \CC`,
$`q \in \mathbb{N}`, $`w \in \ZZ`, the Frobenius module $`(V, f)` is
*$`\iota`-pure of weight $`w`* if every eigenvalue $`\alpha` of $`f`
satisfies $`\|\iota\alpha\|^2 = q^w` (squared convention — no square
roots). Formalized as `Weil.IsPureWeight`, sorry-free.
:::

:::definition "WT-mixed" (parent := "grp-weights") (uses := "WT-pure") (lean := "Weil.IsMixedLE") (tags := "existing-project")
Mixedness bounds: $`(V, f)` is *mixed of weight $`\leq w`*
(`Weil.IsMixedLE`: every eigenvalue has $`\|\iota\alpha\|^2 \leq q^w`)
resp. $`\geq w` (`Weil.IsMixedGE`), with monotonicity in $`w`
(`IsMixedLE.mono`, sorry-free) and the equivalence "pure ⟺ mixed
$`\leq w` and $`\geq w`". At module level mixedness is an *eigenvalue
bound*, not a filtration; over algebraically closed $`K` the two agree
({bpref "WT-module-filtration"}[]).
:::

:::definition "WT-universal" (parent := "grp-weights") (uses := "WT-pure") (lean := "Weil.IsUnivPureWeight") (tags := "existing-project")
Universal purity: pure of weight $`w` for *every* ring homomorphism
$`\iota \colon K \to \CC` (`Weil.IsUnivPureWeight`, sorry-free). The
universal quantifier is what makes weight classes stable under all
automorphisms of $`K` ({bpref "WT-aut-stability"}[]) — a single
$`\iota` would not suffice for the descent pipeline.
:::

:::lemma_ "WT-separation" (parent := "grp-weights") (uses := "WT-pure") (lean := "Weil.IsPureWeight.not_isEigenvalue_of_ne") (tags := "existing-project")
Weight separation: for $`q \geq 2` and $`w \neq w'`, an
$`\iota`-pure module of weight $`w` and one of weight $`w'` share no
eigenvalue; a nonzero module is pure of at most one weight
(`IsPureWeight.weight_eq`, `IsUnivPureWeight.weight_eq`). Formalized,
sorry-free.
:::

:::proof "WT-separation"
A common eigenvalue would give $`q^w = \|\iota\alpha\|^2 = q^{w'}`,
and $`n \mapsto (q : \RR)^n` is injective on $`\ZZ` for $`q \geq 2`
(strict monotonicity of `zpow` for base $`> 1`). Already kernel-checked
in the repository; consumers: {bpref "W-no-cancellation"}[] and the
weight-gap exactness trick {bpref "PUR-irreducible-reduction"}[].
:::

:::lemma_ "WT-aut-stability" (parent := "grp-weights") (uses := "WT-universal") (tags := "elementary-missing") (effort := "small")
Automorphism stability: if $`\sigma` is a ring automorphism of $`K` and
$`\alpha \in K` is universally pure of weight $`w` (as an eigenvalue —
equivalently the one-dimensional module $`(K, \alpha)` is), then
$`\sigma\alpha` is universally pure of weight $`w`; and no
$`\alpha \neq 0` is universally pure of two distinct weights.
:::

:::proof "WT-aut-stability"
For $`\iota \colon K \to \CC`, the composite $`\iota \circ \sigma` is
again a ring homomorphism $`K \to \CC`, so
$`\|\iota(\sigma\alpha)\|^2 = \|(\iota\sigma)(\alpha)\|^2 = q^w` — the
universal quantifier absorbs the automorphism. Uniqueness of the weight
is {bpref "WT-separation"}[] applied at any single $`\iota`
(existence by {bpref "LA-embedding-extension"}[]). Consumer:
{bpref "W-rational-coefficients"}[].
:::

:::lemma_ "WT-module-filtration" (parent := "grp-weights") (uses := "WT-mixed") (tags := "elementary-missing") (effort := "small")
Module-level comparison: over algebraically closed $`K`, $`(V, f)` is
mixed of weight $`\leq w` (eigenvalue bound) iff it admits a finite
$`f`-stable filtration whose graded pieces are $`\iota`-pure of weights
$`\leq w`. (One direction extracts eigenvectors repeatedly; the other
is {bpref "WT-filtration-bound"}[].) This is the bridge between the
module predicates and the sheaf-level filtration definition.
:::

:::proof "WT-module-filtration" (uses := "LA-eigenvalue-exists, LA-charpoly-rev-mult")
Given the bound, build a full flag: pick an eigenvector
({bpref "LA-eigenvalue-exists"}[]), quotient, recurse — each graded
piece is one-dimensional, pure of the weight of its eigenvalue, all
$`\leq w`. Conversely a filtration with mixed-$`\leq w` pieces gives
the eigenvalue bound because the eigenvalue multiset of $`f` is the
union over graded pieces ({bpref "LA-charpoly-rev-mult"}[]).
:::

:::lemma_ "WT-filtration-bound" (parent := "grp-weights") (uses := "WT-mixed") (tags := "elementary-missing") (effort := "small") (priority := "high")
Filtration weight bound (the spectral-sequence surrogate): if a
Frobenius module $`H` has a finite $`F`-stable filtration whose graded
pieces are subquotients of modules that are mixed of weights
$`\leq w`, then $`H` is mixed of weights $`\leq w`. Likewise for
$`\geq` and for purity ranges.
:::

:::proof "WT-filtration-bound" (uses := "LA-charpoly-rev-mult")
Eigenvalues of a filtered endomorphism form the union (with
multiplicity) of the eigenvalues on the graded pieces, and eigenvalues
of sub- or quotient modules inject into those of the ambient module —
both by {bpref "LA-charpoly-rev-mult"}[]. Chain the two facts. *Role:*
this three-line lemma is what every "Leray spectral sequence" in the
lecture notes compiles to; combined with
{bpref "SIX-rf-composition"}[] it eliminates spectral sequences from
the entire project.
:::

:::lemma_ "WT-twist-shift" (parent := "grp-weights") (uses := "WT-pure") (tags := "elementary-missing") (effort := "small")
Weight arithmetic: if $`(V, f)` is $`\iota`-pure of weight $`w` then
the Tate twist $`V(m)` (Frobenius $`q^{-m} f`) is pure of weight
$`w - 2m`; duals have weight $`-w`; tensor products of pure modules add
weights; and the similitude transport of
{bpref "DU-reciprocal-transport"}[] sends weight-$`w` modules to
weight-$`(2d - w)` modules (eigenvalues $`q^d/\alpha`).
:::

:::proof "WT-twist-shift"
Direct from the definitions:
$`\|\iota(q^{-m}\alpha)\|^2 = q^{-2m}\|\iota\alpha\|^2`;
eigenvalues of the dual are inverses; eigenvalues of a tensor product
of triangularizable operators are products; and
$`\|\iota(q^d/\alpha)\|^2 = q^{2d}/q^w`. Consumers: every step of the
purity bookkeeping, in particular {bpref "PUR-duality-squeeze"}[] and
{bpref "MON-stationary-bookkeeping"}[].
:::

:::lemma_ "WT-base-extension" (parent := "grp-weights") (uses := "WT-pure") (tags := "elementary-missing") (effort := "small")
Base-extension invariance (exposed by the audit): let
$`\mathcal{F}_0` be a Weil sheaf on $`X_0/\Fq` and
$`X_m = X_0 \times_{\Fq} \Fqn{m}` the base extension, with pulled-back
Weil sheaf $`\mathcal{F}_m`. If $`\mathcal{F}_0` is punctually
$`\iota`-pure of weight $`w` (resp. mixed $`\leq w`), then so is
$`\mathcal{F}_m` — with the *same* weight, in the local normalization
of {bpref "WT-sheaf-punctual"}[]. Likewise weight bounds on
$`H^i_c(X, \mathcal{F})` are unchanged by replacing $`(X_0, q)` with
$`(X_m, q^m)` (the Frobenius is replaced by its $`m`-th power).
:::

:::proof "WT-base-extension"
A closed point $`x'` of $`X_m` over a closed point $`x` of $`X_0`
has $`\kappa(x') = \kappa(x) \cdot \Fqn{m}`, and the local geometric
Frobenius satisfies $`F_{x'} = F_x^{e}` with
$`e = \deg(x')\, m / \deg(x) = [\kappa(x') : \kappa(x)]`, so
$`q_{x'} = q_x^{e}`; eigenvalues are raised to the $`e`-th power and
$`\|\iota(\alpha^e)\|^2 = (q_x^{w})^{e} = q_{x'}^{w}`. Filtrations
pull back. On global cohomology, base extension replaces $`F` by
$`F^m` and $`q` by $`q^m`: eigenvalues are $`m`-th powers, weights
(normalized to the new $`q^m`) unchanged. *Why the audit added
this*: the devissages quietly extend the base field (radicial
base changes in {bpref "PUR-devissage-homeo"}[], the rational-point
choice in {bpref "PUR-move-infinity"}[], the covers in
{bpref "GEO-tame-reduction"}[]); without this lemma those steps do
not literally return to the original statement.
:::

# Sheaf-level definitions

:::definition "WT-sheaf-punctual" (parent := "grp-weights") (uses := "SH-weil-sheaf, WT-pure") (tags := "infrastructure") (effort := "small")
Punctual purity: a Weil sheaf $`\mathcal{F}_0` on $`X_0/\Fq` is
*punctually $`\iota`-pure of weight $`w`* if for every closed point
$`x` of $`X_0`, the Frobenius module
$`(\mathcal{F}_{\bar x}, F_x)` is $`\iota`-pure of weight $`w`
relative to $`q_x = q^{\deg x}` — note the *local* normalization by
$`q_x`, which makes the notion invariant under finite extension of the
base field.
:::

:::definition "WT-sheaf-mixed" (parent := "grp-weights") (uses := "WT-sheaf-punctual") (tags := "infrastructure") (effort := "small")
Sheaf-level mixedness: $`\mathcal{F}_0` is *$`\iota`-mixed of weights
$`\leq w`* if it admits a finite filtration by Weil subsheaves whose
graded pieces are punctually $`\iota`-pure of weights $`\leq w`.
*Filtration form is essential at sheaf level* (a stalkwise eigenvalue
bound is not known to globalize and is never used); the module-level
comparison {bpref "WT-module-filtration"}[] holds only over a point. A
complex has weights $`\leq w` if $`\mathcal{H}^j` is mixed of weights
$`\leq w + j` for all $`j`.
:::

:::definition "WT-iota-real" (parent := "grp-weights") (uses := "SH-weil-sheaf") (tags := "infrastructure") (effort := "small")
$`\iota`-real sheaves: a lisse Weil sheaf $`\mathcal{G}_0` is
*$`\iota`-real* if for every closed point $`x`, the polynomial
$`\iota\bigl(\det(1 - t F_x \mid \mathcal{G}_{\bar x})\bigr)` has real
coefficients. Stable under direct sums and tensor products; the input
notion of the real-sheaf purity criterion
({bpref "PUR-real-purity"}[]) and the reason the whole branch works
with Weil sheaves ({bpref "PUR-real-envelope"}[] twists by
non-descending scalars).
:::
