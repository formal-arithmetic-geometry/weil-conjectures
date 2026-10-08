+++
id = "lemma-weil-pbc-derived-exchange-replacement"
kind = "lemma"
title = "Derived exchange replacement independence"
order = 1043
lean = ["AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_ext", "AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app"]
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-underived-exchange", "lem-weil-pbc-derived-exchange-termwise", "lemma-weil-pbc-underived-exchange-naturality"]
+++
The K-injective replacement used in Definition
[def-weil-pbc-derived-exchange] gives a well-defined derived exchange
map, independent of all replacement choices.

## Proof

Given two K-injective replacements $J^\bullet$ and $J'^\bullet$, the identity
of $g'^{-1}I^\bullet$ lifts to maps $J^\bullet\to J'^\bullet$ and
$J'^\bullet\to J^\bullet$ because K-injective complexes are homotopically
injective. Their composites are homotopic to the identities by lifting the
homotopies of the replacement quasi-isomorphisms. Applying $f'_*$ preserves
chain homotopies. The two resulting maps from
$g^{-1}f_*I^\bullet$ therefore define the same morphism in the derived
category. A comparison of two injective resolutions of $K$ is handled by
the same lifting argument, and naturality of the underived exchange map
commutes with the comparison maps. Thus the class is canonical.

## Detailed form

Let $K\to I$ and $K\to J$ be two K-injective resolutions
[def-weil-pbc-kinjective-resolutions]. Every comparison $I\to J$ over $K$
gives the same derived exchange morphism of the derived exchange morphism
[def-weil-pbc-derived-exchange], and two such comparisons are
chain-homotopic. Consequently $\Ex_{\square,K}$ is independent of the
resolution and is natural in $K$.

## Proof

The comparison lemma for K-injective resolutions stated in
[def-weil-pbc-kinjective-resolutions] supplies the chain maps and their
homotopy uniqueness; by [lem-weil-pbc-derived-exchange-termwise] the termwise
underived exchange on such a resolution computes the derived exchange
morphism $\Ex_{\square,K}$ of [def-weil-pbc-derived-exchange], so
any two comparisons over $K$ give the same morphism of the derived category,
and the naturality of $\Ex_{\square,K}$ in $K$ follows from the naturality of
the underived exchange.
