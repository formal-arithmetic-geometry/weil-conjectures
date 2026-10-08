+++
id = "lem-amb-etale-compact-comparisons"
kind = "lemma"
title = "The etale compact-support comparisons"
order = 1564
uses = ["def-amb-etale-compact-support", "def-asd-compactifiable", "def-weil-compactifications-refinements", "lem-weil-derived-direct-image-composition", "lem-weil-pbc-proper-open-comparison-composition", "lem-weil-pbc-proper-open-comparison-iso", "prop-weil-proet-finite-proper-base-change", "thm-nagata-compactification"]
+++
The proper-refinement comparisons for
[def-amb-etale-compact-support] are coherent
isomorphisms. Thus they identify its candidates canonically.
These identifications provide the usual composition
isomorphism $Rg_!Rf_!\cong R(gf)_!$ for composable
compactifiable separated finite-type morphisms between
Noetherian schemes.

## Proof

The etale refinement map is the map of
[lem-weil-pbc-proper-open-comparison-iso]; its
bounded-below proof tests only the open where it is
the identity and the complement, where proper base
The argument applies verbatim to bounded-below complexes, which is
the coefficient range in which the cited comparison lemmas of
the compactification-comparison chapter are stated; that is the range used below, and no
assertion is made here for complexes unbounded below.
[lem-weil-pbc-proper-open-comparison-composition]
likewise applies to them and proves identity and
composition for refinements. Given two compactifications,
the closure of the diagonal copy of $X$ in their
fibre product gives a common proper refinement of
the kind in [def-weil-compactifications-refinements].
Passing to a further such refinement compares any two
choices; the already-proved composition identity makes
the result independent of all choices.

Here is the composition construction. Compactify
$g:Y\to S$ as $Y\xrightarrow{v}\overline Y\to S$,
and compactify the map $vf:X\to\overline Y$ as
$X\xrightarrow{a}\overline X\xrightarrow{p}\overline Y$,
using [thm-nagata-compactification] if necessary.
Write $V=\overline X\times_{\overline Y}Y$, with
open immersion $b:V\to\overline X$ and proper map
$p_Y:V\to Y$. Then $X\hookrightarrow V\to Y$
is a compactification of $f$. For every bounded-below complex
$N$ on $V$, the map

$$
v_!Rp_{Y*}N\longrightarrow Rp_*b_!N
$$

is an isomorphism: over $Y$ it is proper base
change, and at a geometric point outside $Y$
both sides vanish, since the corresponding fibre
misses $V$. These assertions use
[prop-weil-proet-finite-proper-base-change], with the same
finite-amplitude extension as above. Apply this map
to the extension by zero of a complex on $X$,
then apply the proper direct image $R\overline g_*$.
Open extension by zero composes termwise, and proper
derived direct image composes
([lem-weil-derived-direct-image-composition], item (5)) by its adjunction to
the composite exact inverse image. The result is
$Rg_!Rf_!\cong R(gf)_!$. For three morphisms,
choose one common refinement of all compactifications;
the two composite maps restrict to the same identity
over the source and use the same proper base-change
maps on each Cartesian rectangle. Their pasting
identity, followed by the refinement composition
identity above, proves associativity.
