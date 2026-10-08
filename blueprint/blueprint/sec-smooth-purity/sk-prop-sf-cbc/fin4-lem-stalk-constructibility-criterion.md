+++
id = "fin4-lem-stalk-constructibility-criterion"
kind = "lemma"
title = "Constructibility from the cardinalities of finite stalks"
order = 1608
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-flat-lfp-open", "lem-weil-pbc-noetherian-finite-components", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-geometric-stalks-exact"]
+++
Let $X$ be a Noetherian
scheme and let $F$ be an
abelian etale sheaf on $X$
with finite geometric stalks.
For $n\geq1$ put $C_n=\{x\in X:|F_{\bar x}|=n\}$.
Then $F$ is constructible
if and only if every $C_n$ is a constructible subset of $X$.
For an abelian sheaf, constructibility here means a finite locally
closed partition with finite locally constant restrictions.

## Proof

If $F$ is constructible, refine its finite partition and its finite
etale trivializations so that stalk cardinality is constant on each
part. Each $C_n$ is a finite union of these parts, by
[def-weil-pbc-constructible-complexes].

Conversely use Noetherian induction on closed subsets of $X$.
Pullback to a closed subset preserves stalks by
[prop-weil-pbc-geometric-stalks-exact]; the new level sets are
intersections with $C_n$, hence are constructible.
It suffices to find a nonempty open where $F$ is finite locally
constant. Choose an irreducible component with generic point $\eta$.
Remove the other finitely many components, using
[lem-weil-pbc-noetherian-finite-components], to obtain a nonempty
irreducible open $X_0$. Put $M=F_{\bar\eta}$ and $m=|M|$.
The constructible subset $C_m\cap X_0$ contains $\eta$, hence
contains a nonempty open $U$ of $X_0$: among its finitely many
locally closed pieces one contains $\eta$, and that piece's closed
factor must be all of $X_0$.

A finite abelian group has finitely many generators and relations.
By [def-weil-pbc-geometric-stalks], lift its generators to
sections on one pointed affine etale neighbourhood $V\to U$ of
$\bar\eta$. The relations have zero germs; finitely many further
refinements make all of them zero as sections. Thus we obtain
$\varphi:\underline M_V\to F|_V$ inducing the identity on $M$.
The chosen point over $\eta$ is generic in a component of $V$:
an etale morphism is flat with zero-dimensional fibres, so a point
over a generic point is itself generic. Remove the other components
to make $V$ irreducible, retaining this point.

For $a\ne0$ in $M$, the zero-germ locus of $\varphi(a)$ is
open in $V$. A zero germ is represented by the zero section on an
etale neighbourhood; the images of these neighbourhoods are open by
[lem-weil-pbc-flat-lfp-open], and their union is that locus.
It omits the generic point because $\varphi_{\bar\eta}$ is injective.
An open subset of irreducible $V$ omitting its generic point is
empty. Consequently $\varphi$ is injective at every geometric
stalk. Both sides have $m$ elements at each stalk, so it is an
isomorphism by [lemma-weil-pbc-geometric-stalk-conservative].
The image $W$ of $V\to X$ is nonempty and open by
[lem-weil-pbc-flat-lfp-open], and the etale cover $V\to W$
trivializes $F|_W$. Induction supplies a finite partition on
$X\setminus W$; adjoining $W$ proves constructibility.
This also proves finiteness of the image of $x\mapsto|F_{\bar x}|$;
it was not inferred from an infinite union of constructible subsets.
The classical statement is
[SGA 4,
Exposition IX, Proposition 2.13(iii)](https://grothendiecksga.com/read/sga4/en/IX-2.html).
