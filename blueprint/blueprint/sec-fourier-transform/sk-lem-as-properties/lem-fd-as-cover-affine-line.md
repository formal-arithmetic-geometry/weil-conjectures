+++
id = "lem-fd-as-cover-affine-line"
kind = "lemma"
title = "The affine-line Artin–Schreier cover"
order = 2681
uses = ["def-fd-artin-schreier-sheaf", "lem-fd-as-cover"]
+++
Over $X_0=\mathbf A^1_{k_0}=\operatorname{Spec}k_0[x]$ with $f=x$, the covering of [lem-fd-as-cover] is $Y\cong\mathbf A^1_{k_0}=\operatorname{Spec}k_0[y]$ via $T\mapsto y$; under this isomorphism $\pi$ is $y\mapsto x=y^p-y$ and the $\mathbf F_p$-action is $y\mapsto y+a$.

## Proof

By [lem-fd-as-cover] for $f=x$, the covering ring of the Artin–Schreier
sheaf family [def-fd-artin-schreier-sheaf] is
$k_0[T]/(T^p-T-x)$; the $k_0[x]$-algebra map $k_0[T]/(T^p-T-x)\to k_0[y]$, $T\mapsto y$, is well defined because $y^p-y=x$, and it is surjective. Both sides are free of rank $p$ over $k_0[x]$: the source is free by definition; for the target, the relation $y^p=x+y$ expresses every element as $\sum_{i<p}c_i(x)y^i$ with $c_i\in k_0[x]$, and such a sum vanishes only if all $c_i=0$, since the terms have leading degrees $p\deg c_i+i$, which are pairwise distinct modulo $p$ and hence cannot cancel (the map $k_0[x]\to k_0[y]$, $x\mapsto y^p-y$, is injective). A surjective $k_0[x]$-linear map between free modules of the same finite rank is injective, so the map is an isomorphism. The formulas for $\pi$ and for the action $T\mapsto T+a$ read off as $x=y^p-y$ and $y\mapsto y+a$.
