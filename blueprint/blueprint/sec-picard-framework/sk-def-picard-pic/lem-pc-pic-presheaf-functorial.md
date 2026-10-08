+++
id = "lem-pc-pic-presheaf-functorial"
kind = "lemma"
title = "The Picard presheaf is a functor"
order = 803
uses = ["def-pc-base-change", "def-pc-picard-presheaf", "def-sc-invertible-module", "lem-pc-tensor-dual-invertible"]
+++
Let $f:X\to S$ be a morphism of schemes. The assignment of
Definition [def-pc-picard-presheaf]
$T\mapsto\operatorname{Pic}(X_T)$ is a functor
$(\mathit{Sch}/S)^{\mathrm{op}}\to\textit{Sets}$: for $g:T'\to T$ with
$g_X:X_{T'}\to X_T$ the map $\mathcal{L}\mapsto g_X^*\mathcal{L}$ sends invertible
modules to invertible modules, respects isomorphisms and satisfies
$(g_1\circ g_2)^*=g_2^*g_1^*$ and $(\mathrm{id})^*=\mathrm{id}$.

## Proof

If $\mathcal{L}$ is invertible on $X_T$, then $g_X^*\mathcal{L}$ is invertible on
$X_{T'}$: local on $X_{T'}$, $g_X^*\mathcal{L}$ is the base change of a locally
free rank one module (trivializing by an open cover and using that
$g_X^*$ preserves admits an exactness: $g_X^*$ of a free module of rank
one is free of rank one). The two functoriality equations are the
standard $(g_1g_2)^*=g_2^*g_1^*$ and $(\mathrm{id})^*=\mathrm{id}$ for the pullback
functor (a straightforward identity of the corresponding module
sections), and isomorphisms are sent to isomorphisms, so the map is
well defined on isomorphism classes.
