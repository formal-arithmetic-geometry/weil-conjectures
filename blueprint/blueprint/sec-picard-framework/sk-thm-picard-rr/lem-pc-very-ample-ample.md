+++
id = "lem-pc-very-ample-ample"
kind = "lemma"
title = "Ample line bundles from projective embeddings"
order = 731
uses = ["def-pc-morphism-conventions", "def-sc-ample", "def-sc-invertible-module", "lem-pc-closed-imm-base-change"]
+++
Let $k$ be a field, let $i:X\hookrightarrow\mathbf{P}^n_k$ be a closed immersion
and let $\mathcal{L}:=i^*\mathcal{O}_{\mathbf{P}^n}(1)$. Then $\mathcal{L}$ is
ample on $X$; in particular the base change
$\mathcal{L}\otimes_k K$ is ample on $X_K$ for every field extension $K/k$.

## Proof

The scheme $\mathbf{P}^n_k$ is the union of the affine opens $D_+(x_j)$,
$j=0,\dots,n$ (as usual via the homogeneous coordinates $x_0,\dots,x_n$);
hence with $s_j:=i^*x_j\in H^0(X,\mathcal{L})$ we have
$X_{s_j}=X\cap D_+(x_j)$, which is affine (a closed subscheme of an
affine scheme is affine: closed immersions are affine morphisms, Schemes,
Lemma 26.8.2, Tag [01IH](https://stacks.math.columbia.edu/tag/01IH)),
and $\bigcup_jX_{s_j}=X$ as the $D_+(x_j)$ cover $\mathbf{P}^n_k$ and $i$ is
injective. Thus the affine open sets $X_s$ form a basis of the topology,
so $\mathcal{L}$ is ample by Properties, Proposition 28.27.13 (Tag
[01Q3](https://stacks.math.columbia.edu/tag/01Q3)), condition (4)
$\Rightarrow$ (1). The last assertion follows since the same argument
applies to the base-changed closed immersion
$i_K:X_K\hookrightarrow\mathbf{P}^n_K$ (base change of a closed immersion, see
Lemma [lem-pc-closed-imm-base-change])
and the very ample module $\mathcal{O}_{\mathbf{P}^n_K}(1)$.
