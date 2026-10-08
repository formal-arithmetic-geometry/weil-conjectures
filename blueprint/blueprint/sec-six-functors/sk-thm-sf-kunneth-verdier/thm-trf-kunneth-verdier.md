+++
id = "thm-trf-kunneth-verdier"
kind = "theorem"
title = "Kunneth–Verdier isomorphism; the $\\kappa$ map"
order = 2228
uses = ["def-sf-kv-maps", "def-trf-admissibility", "def-trf-dualizing-complex", "prop-trf-exceptional-kunneth", "prop-trf-external-hom"]
+++
Let $X,Y$ be separated finite-type schemes with dualizing complexes as
in [def-trf-dualizing-complex] (so the structure morphism $a_Y$ satisfies
the exceptional-adjoint admissibility of [def-trf-admissibility]), assume
that the product projection $p_X=\operatorname{id}_X\times a_Y:X\times Y\to X$
satisfies it as well, so that $p_X^!$ and the map
$\alpha_{\operatorname{id}_X,a_Y}$ of [def-sf-kv-maps] (ii) are defined, and
let $p_X,p_Y$ be the projections of $X\times Y$. For
$M\in D^b_{ctf}(X,A)$, $N\in D^b_{ctf}(Y,A)$, the canonical
comparison of [def-sf-kv-maps] (iv), formed with the geometric operations, is an isomorphism:

$$
\kappa_{M,N}:M\boxtimes_A^{\mathrm L}D_YN
\xrightarrow{\ \sim\ }
\RHom_A\bigl(p_Y^*N,\,p_X^!M\bigr),
$$

where $D_YN=\RHom_A(N,\omega_Y)$ is the dualizing functor of
[def-trf-dualizing-complex].

## Proof

Apply the external Hom [prop-trf-external-hom] to the pairs
$(A_X,M)$ and $(N,\omega_Y)$, followed by
$\RHom(1,\alpha)$ from [prop-trf-exceptional-kunneth] for the
identification $M\boxtimes_A^{\mathrm L}\omega_Y\simeq p_X^!M$ of
[def-trf-dualizing-complex]. Their composite is exactly
$\kappa_{M,N}$, and both factors are isomorphisms, so $\kappa_{M,N}$
is an isomorphism.
