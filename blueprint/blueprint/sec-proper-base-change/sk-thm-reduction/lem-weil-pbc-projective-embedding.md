+++
id = "lem-weil-pbc-projective-embedding"
kind = "lemma"
title = "Projective embedding over the source"
order = 1197
uses = ["def-weil-pbc-scheme-conventions", "lem-weil-pbc-proper-immersion-closed", "lem-weil-pbc-proper-to-separated", "lemma-weil-pbc-chow-factorization"]
+++
With the notation of [lemma-weil-pbc-chow-factorization], the map

$$
 i_X=(\pi,i_Y):\widetilde X\longrightarrow
 X\times_Y\mathbf P^n_Y\simeq\mathbf P^n_X
$$

is a closed immersion over $X$.

## Proof

The map $i_X$ is an immersion by the graph construction applied to the two
maps supplied by [lemma-weil-pbc-chow-factorization]. Its source is proper over $X$ and its
target is separated over $X$, so $i_X$ is proper; a proper immersion is a
closed immersion.
