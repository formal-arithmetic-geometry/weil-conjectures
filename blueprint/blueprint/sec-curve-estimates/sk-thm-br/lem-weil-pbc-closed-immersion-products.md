+++
id = "lem-weil-pbc-closed-immersion-products"
kind = "lemma"
title = "Closure of the closed-immersion and finite-type properties"
order = 904
uses = ["def-weil-pbc-scheme-conventions"]
+++
The composite of closed immersions [def-weil-pbc-scheme-conventions] is a
closed immersion, and a product (over a common base) of closed immersions is
a closed immersion. An open immersion is of finite type.

## Proof

A composite of closed immersions is affine and is induced locally by a
composite of surjective ring homomorphisms, hence a closed immersion. The
base change of a closed immersion is a closed immersion, since tensoring a
surjective ring homomorphism is surjective (right exactness of tensor), and
the product over a common base of closed immersions $Z_i\hookrightarrow W_i$
is the composite of two such base changes (the closed subscheme
$Z_1\times_YZ_2\subseteq W_1\times_YW_2$ is the intersection of the two
base-changed subschemes). An open immersion $j:U\hookrightarrow Y$ is locally
of finite type: around $x\in U$ choose an affine $V\subseteq Y$ and a
principal affine $D(f)\subseteq U\cap V$ containing $x$, which is affine of
finite type over $V$; with quasi-compact source it is therefore of finite
type by [def-weil-pbc-scheme-conventions], which is the case used in this
blueprint (the open subschemes in question are quasi-compact).
