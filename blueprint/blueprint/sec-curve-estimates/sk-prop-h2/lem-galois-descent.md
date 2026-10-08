+++
id = "lem-galois-descent"
kind = "lemma"
title = "Effective etale descent for finite etale morphisms"
order = 964
uses = ["def-galois-categories", "def-weil-pbc-scheme-conventions", "lem-galois-glue"]
+++
Let $Y'\to Y$ be a surjective etale morphism with $Y'=\coprod_iY_i$,
and put $Y''=Y'\times_YY'$, $Y'''=Y'\times_YY'\times_YY'$. Then the
category of finite etale $Y$-schemes is equivalent to the category of
finite etale $Y'$-schemes $P'$ endowed with a descent datum, i.e. an
isomorphism $\varphi:p_1^*P'\cong p_2^*P'$ over $Y''$ satisfying
$p_{13}^*\varphi=p_{23}^*\varphi\circ p_{12}^*\varphi$ over $Y'''$.

**Status.** proved below from [lem-galois-glue] and the Zariski
locality of "finite etale" on the target; no stack-theoretic input is
used.

## Proof

Step 1: full faithfulness. For objects $P,Q$ of
$\mathrm{F\acute Et}(Y)$ as in [def-galois-categories], i.e. finite etale $Y$-schemes in the conventions of
[def-weil-pbc-scheme-conventions], the diagram

$$
\operatorname{Hom}_Y(P,Q)\to\operatorname{Hom}_{Y'}(P',Q')
\rightrightarrows\operatorname{Hom}_{Y''}(P'',Q'')
$$

is exact: a $Y'$-morphism compatible with the descent data descends,
because its graph $\Gamma\subseteq P'\times_{Y'}Q'$ is a closed subscheme
whose two pullbacks to $Y''$ agree and closed subschemes are determined
by their pullback along the surjective flat $Y''\to Y'$ — affine-locally
this is the exactness of $A\to A'\rightrightarrows A''$ for faithfully
flat $A\to A'$.
Step 2: effectivity. Write $P_i=P'\times_{Y'}Y_i$, finite etale over
$Y_i$. The datum gives isomorphisms
$\varphi_{ij}:P_i\times_YY_j\to P_j\times_YY_i$, and its cocycle condition
over $Y'''$ implies the cocycle condition over
$Y_i\times_YY_j\times_YY_k$ by Step 1 applied over the relevant double
intersection. By [lem-galois-glue] the $P_i$ glue to a $Y$-scheme
$P$ with $P\times_YY_i\cong P_i$.
Step 3: $P\to Y$ is finite etale. Both properties are Zariski-local on
the target and hold after the base change $Y_i\to Y$; since the $Y_i$
cover $Y$, the morphism $P\to Y$ is finite and etale. Step 4: the
construction is inverse to base change by Steps 1–3.
