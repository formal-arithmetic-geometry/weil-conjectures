+++
id = "lem-fin-normal-open-lisse-image"
kind = "lemma"
title = "A lisse sheaf on a normal open has constructible direct image"
order = 1908
uses = ["def-sbc-normal-dominant-galois", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "fin2-lem-lisse-trivialized-finite-etale", "lem-fin-finite-constant-pushforward", "lem-fin-normal-constant-open-image", "lem-fin-normalization-extends-cover", "lem-weil-pbc-constructible-subobjects-noetherian", "lemma-weil-pbc-finite-stalk-formula"]
+++
Let $X$ be integral of finite type over a field, let
$k:V\hookrightarrow X$ be a nonempty
normal open,
and let $L$ be a finite locally constant module sheaf
over a finite ring. Then the
direct image $k_*L$
is constructible.

## Proof

Choose a finite etale surjective $p:P\to V$ trivializing
$L$, by [fin2-lem-lisse-trivialized-finite-etale].
Write $P=\coprod P_a$ for its finitely many connected
components and write the corresponding constant module as
$M_a$. The adjunction unit
$L\to p_*p^*L$ is injective: the finite stalk formula
of [lemma-weil-pbc-finite-stalk-formula] identifies it
with a diagonal into a nonempty finite product of copies
of the original stalk. Direct image is left exact, so

$$
k_*L\hookrightarrow\prod_a(kp_a)_*\underline{M_a}.
$$

Extend $P_a$ to the normalization $g_a:Y_a\to X$
using [lem-fin-normalization-extends-cover], and let
$v_a:P_a\hookrightarrow Y_a$ be the resulting nonempty
open. The source $Y_a$ is normal integral. By
[lem-fin-normal-constant-open-image],
$v_{a,*}\underline{M_a}=\underline{M_a}_{Y_a}$.
Direct-image composition, evaluated on objects as in
[def-weil-pbc-direct-image], therefore gives
$(kp_a)_*\underline{M_a}=g_{a,*}\underline{M_a}$.
Each of these sheaves is constructible by
[lem-fin-finite-constant-pushforward]; so is their
finite product, by a common finite lisse partition.
The subobject theorem
[lem-weil-pbc-constructible-subobjects-noetherian]
now proves constructibility of $k_*L$.
