+++
id = "lem-fin-normal-generic-constant"
kind = "lemma"
title = "A generic constant sheaf on a normal Noetherian scheme"
order = 1606
uses = ["def-sbc-normal-dominant-galois", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "lem-fin-etale-normal-components", "lem-weil-pbc-flat-lfp-open"]
+++
Let $V$ be Noetherian, normal and integral in the sense of
[def-sbc-normal-dominant-galois], with generic inclusion
$e:\operatorname{Spec}K\to V$. For a finite abelian group $M$,
the natural map of etale sheaves
$\underline M_V\to e_*\underline M_K$ is an isomorphism, where
$e_*$ is the direct image.

## Proof

Evaluate on an affine etale $W\to V$.
By [lem-fin-etale-normal-components], $W$ has finitely many
normal integral open-and-closed components $W_a$.
Every nonempty $W_a$ dominates $V$, since its image is a nonempty
open by [lem-weil-pbc-flat-lfp-open].
Its generic fibre is the spectrum of one finite separable field
extension of $K$: it is integral and etale of finite type over $K$,
so its coordinate algebra is a zero-dimensional finite-type domain,
hence a finite separable field. Thus $W$ and $W_K$ have the
same finite set of connected components.
The sections of a constant sheaf $M$ on a connected scheme are
$M$, by [def-weil-pbc-etale-sheaves]; equivalently a section is
a locally constant function to the finite discrete set $M$.
Both groups of sections here are therefore $\prod_aM$, and
restriction is the identity on each factor.
By [def-weil-pbc-direct-image] these are precisely the maps
defining the asserted isomorphism, on a covering basis of the site.
