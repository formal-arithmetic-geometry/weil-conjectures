+++
id = "lem-kun-projective-implies-proper"
kind = "lemma"
title = "Projective morphisms are proper"
order = 1708
uses = ["def-kun-projective", "def-weil-pbc-scheme-conventions", "lem-chow-closed-model", "lem-weil-pbc-closed-immersion-proper", "lem-weil-pbc-proper-composition"]
+++
Every projective morphism is
proper (the structural
morphism $\mathbf P^N_Y\to Y$ is proper, and closed immersions are
proper; the class of proper morphisms is closed under composition).

## Proof

By [def-kun-projective] the morphism $f$ is the composite of a
closed immersion $i:X\hookrightarrow\mathbf P^N_Y$ with the
structural projection $q:\mathbf P^N_Y\to Y$. Closed immersions are
proper by [lem-weil-pbc-closed-immersion-proper], and
$q:\mathbf P^N_Y\to Y$ is proper as the base change of
$\mathbf P^N_{\mathbf Z}\to\Spec\mathbf Z$, which is proper (Stacks
Project,
[Tag `01WC`](https://stacks.math.columbia.edu/tag/01WC),
quoted in the proper-base-change chapter,
[lem-chow-closed-model]). Hence $f=q\circ i$
is proper by lem:weil-pbc-proper-composition.
