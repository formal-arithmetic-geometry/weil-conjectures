+++
id = "lem-fin-normal-constant-open-image"
kind = "lemma"
title = "A constant sheaf across a dense normal open"
order = 1906
uses = ["def-sbc-normal-dominant-galois", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-fin-etale-normal-components", "lem-weil-pbc-flat-lfp-open"]
+++
Let $Y$ be a Noetherian
normal integral
scheme, let $v:V\hookrightarrow Y$ be a nonempty
open immersion,
and let $M$ be a finite module. The canonical map
$\underline M_Y\to v_*\underline M_V$, with
direct image on the
etale sites, is an isomorphism.

## Proof

It suffices to evaluate on affine etale objects $W\to Y$.
By [lem-fin-etale-normal-components], they are finite
disjoint unions of open-and-closed components, each integral
in the sense of
[def-sbc-normal-dominant-galois].
Every such component meets $W\times_YV$: its nonempty
image is open in the integral $Y$ by
[lem-weil-pbc-flat-lfp-open], hence meets $V$.
Its intersection with $W\times_YV$ is a nonempty open
of an irreducible scheme and is therefore irreducible.
Thus restriction gives a bijection of the connected
components of $W$ and $W\times_YV$.

Sections of a constant finite sheaf on a scheme are
locally constant functions on its underlying space:
a section selects an open-and-closed partition labelled
by the finite set, as is seen by gluing a trivializing
etale cover. Consequently restriction is the identity
$M^{\pi_0(W)}\to M^{\pi_0(W\times_YV)}$ under the
component bijection. By the section formula for
[def-weil-pbc-direct-image], this is exactly the map
in the statement. The identifications respect restriction
maps, hence define a sheaf isomorphism. Compare
[Stacks
Project, Tag 09Z5](https://stacks.math.columbia.edu/tag/09Z5).
