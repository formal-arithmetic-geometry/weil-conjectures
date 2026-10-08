+++
id = "lem-pc-projective-curve-finite-projection"
kind = "lemma"
title = "A finite map from an integral projective curve to the projective line"
order = 654
uses = ["def-pc-curve", "def-pc-linear-pair-morphism", "def-pc-morphism-conventions", "def-pc-projective-morphism", "def-sc-p1-standard", "lem-pc-linear-pair-morphism-finite", "lem-pc-linear-pair-morphism-gluing", "lem-pc-projective-coordinate-model", "lem-pc-projective-curve-linear-pair"]
+++
Let $k$ be an infinite field and $X$ a
projective
curve over $k$.
There exists a finite morphism
$X\to\mathbf P^1_k$.

## Proof

Choose a closed immersion $X\hookrightarrow\mathbf P^n_k$ from
[def-pc-projective-morphism]. The coordinate model
[lem-pc-projective-coordinate-model] identifies $X$ with
$\operatorname{Proj}(S)$ for an integral standard graded algebra.
Choose $l_0,l_1$ by [lem-pc-projective-curve-linear-pair] and
form $\pi_{l_0,l_1}$ as in [def-pc-linear-pair-morphism], which
exists by [lem-pc-linear-pair-morphism-gluing].
It is finite by [lem-pc-linear-pair-morphism-finite].
