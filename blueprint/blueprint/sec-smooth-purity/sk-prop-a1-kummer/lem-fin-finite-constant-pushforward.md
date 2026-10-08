+++
id = "lem-fin-finite-constant-pushforward"
kind = "lemma"
title = "Finite pushforwards of constant sheaves"
order = 1903
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-finite-pushforward-constructible-noetherian", "lemma-weil-pbc-finite-stalk-formula", "sbc-def-coefficient-conventions"]
+++
Let $g:V\to S$ be finite
with $S$ of finite type over $k$, and let $M$ be a finite abelian
group. Then $g_*\underline M$ is
constructible on
$S_{{\mathrm{et}}}$.

## Proof

The finite constant abelian sheaf $\underline M$ is constructible
by [def-weil-pbc-etale-sheaves]. The Noetherian finite-image
theorem [lem-weil-pbc-finite-pushforward-constructible-noetherian]
therefore applies directly. Its proof obtains a dense lisse open
by an explicit finite-algebra calculation, and treats the closed
complement by Noetherian induction and finite base change. In
particular it does not infer that the original finite morphism
becomes etale merely by ignoring inseparable contributions.
