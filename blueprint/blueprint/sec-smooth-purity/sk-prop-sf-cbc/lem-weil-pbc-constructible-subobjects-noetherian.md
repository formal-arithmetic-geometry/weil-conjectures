+++
id = "lem-weil-pbc-constructible-subobjects-noetherian"
kind = "lemma"
title = "Subsheaves of a constructible sheaf on a Noetherian scheme"
order = 1538
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-site", "lem-weil-pbc-flat-lfp-open", "lem-weil-pbc-noetherian-finite-components", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-geometric-stalks-exact"]
+++
Let $T$ be Noetherian and $\Lambda$ a finite commutative ring. Every
subsheaf of a constructible $\Lambda$-module sheaf on the small etale site
is constructible.

*Source note:* this is Stacks Project, Section 59.74, Constructible sheaves
on Noetherian schemes ([Tag 03RY](https://stacks.math.columbia.edu/tag/03RY)),
whose Proposition 59.74.1 (3) states that for a Noetherian scheme $X$ and a
Noetherian ring $\Lambda$ every submodule and quotient module of a
constructible sheaf of $\Lambda$-modules on $X_{\Et}$ is constructible (the
weak Serre input being Lemma 59.71.6, [Tag
03RZ](https://stacks.math.columbia.edu/tag/03RZ)). The blueprint's statement
is the same assertion for a finite commutative ring $\Lambda$, which is
Noetherian, on the small etale site of a Noetherian $T$, and it adds a
self-contained proof by Noetherian induction on geometric stalks in place of
Stacks' proof through a finite partition into locally constant pieces.

## Proof

Let $G\subset F$, with $F$ constructible. For a constant finite module sheaf
$\underline M$ on an irreducible scheme $W$, and a subsheaf
$H\subset\underline M$, put
$$
 W_m=\{w:\ m\text{ belongs to }H_{\bar w}\subset M\}
 \qquad(m\in M).
$$
This is independent of the choice of geometric point above $w$. It is open.
Indeed, membership is represented by a section of $H$ on an etale
neighbourhood whose image in $\underline M$, after refinement, is the
constant section $m$. Its image in $W$ is open because a flat, locally
finitely presented morphism is open. Such images cover exactly $W_m$. The
local lifts of $m$ glue uniquely, because $H\to\underline M$ is injective.

Every nonempty $W_m$ contains the generic point of $W$. The finite
intersection $W^\circ$ of the nonempty $W_m$'s is therefore nonempty and
open. On it membership in $H$ is the fixed submodule
$M'=H_{\bar\eta}\subset M$. The glued sections give
$\underline{M'}\to H|_{W^\circ}$, and this is an isomorphism on all stalks,
hence an isomorphism by conservativity of geometric stalks.

We now use Noetherian induction on closed subsets of $T$. Pullback to any
such subset preserves the injection, by exactness of geometric stalks, and
preserves the finite partition defining constructibility. Reducible closed
subsets are handled by their finitely many components, using the
finitely-many-components lemma for Noetherian schemes and removing the
preceding components from each partition. For a reduced irreducible closed
subset, choose a nonempty open on which $F$ is lisse, and an etale
trivialization near its generic point. Removing the other irreducible
components of this Noetherian trivializing scheme gives a nonempty
irreducible open $W$. It still dominates the chosen base open: the image of
a nonempty etale open is open and contains its generic point. The preceding
calculation gives $W^\circ$ on which $G$ is constant. Its image $O$ in the
base is nonempty and open; $W^\circ\to O$ is an etale cover, so $G|_O$ is
finite locally constant. Induction supplies a finite lisse partition on the
proper closed complement. Adjoin $O$ to obtain a partition of the whole
subset. At $T$ this proves the assertion. This is the strong subobject
assertion of [Stacks Project, Section
59.74](https://stacks.math.columbia.edu/tag/03RY), with its Noetherian
hypothesis retained.
