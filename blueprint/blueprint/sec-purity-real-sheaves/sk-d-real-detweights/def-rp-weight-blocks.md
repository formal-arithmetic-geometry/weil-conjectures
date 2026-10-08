+++
id = "def-rp-weight-blocks"
kind = "definition"
title = "Rank-counted determinant weights and weight blocks"
order = 2637
uses = ["def-mg-determinantal-weight-multiset", "def-mg-weil-composition-series", "def-real-weil-representation-operations", "def-wf-determinantal-weight", "lem-mg-jordan-holder"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, fix
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$, and let $\mathcal F_0$ be a
nonzero lisse Weil sheaf on $X_0$. Choose a composition series of
$\mathcal F_0$ in the sense of [def-mg-weil-composition-series], with
irreducible factors $V_1,\ldots,V_t$, and put
$r_a=\operatorname{rank}V_a$.

1. The *constituent determinant weights* of $\mathcal F_0$ are the
   numbers $\dw_\iota(V_a)$ of [def-wf-determinantal-weight], counted
   once for each factor; this is the determinantal-weight multiset of
   [def-mg-determinantal-weight-multiset].
2. The *rank-counted list* of determinant weights of $\mathcal F_0$ is
   the multiset in which $\dw_\iota(V_a)$ is repeated exactly $r_a$
   times, for $a=1,\ldots,t$. It has $\operatorname{rank}\mathcal F_0$
   entries.
3. Suppose $\mathcal S$ is semisimple, $\mathcal S=\bigoplus_aV_a$ with
   $V_a$ irreducible of rank $r_a$ (direct sums and irreducibility of
   Weil representations as in [def-real-weil-representation-operations]). For $\gamma\in\mathbf R$ the
   *weight block* of weight $\gamma$ of $\mathcal S$, and the rank and
   weight sum above it, are

$$
\mathcal S(\gamma)=\bigoplus_{\dw_\iota(V_a)=\gamma}V_a,\qquad
N_\gamma=\sum_{\dw_\iota(V_a)>\gamma}r_a,\qquad
B_\gamma=\sum_{\dw_\iota(V_a)>\gamma}r_a\,\dw_\iota(V_a).
$$

These notions do not depend on the choices made. By
[lem-mg-jordan-holder] the factors $V_a$ are determined up to
permutation, isomorphism and multiplicity by $\mathcal F_0$; for a
semisimple $\mathcal S=\bigoplus_aV_a$ the partial sums
$V_1\oplus\cdots\oplus V_b$ form a composition series, so the same
applies to any two decompositions into irreducible summands. Moreover
$\dw_\iota$ is an isomorphism invariant, since isomorphic sheaves have
isomorphic determinant lines; so the lists in 1 and 2, and the numbers
$N_\gamma$ and $B_\gamma$, depend only on $\mathcal F_0$ resp.
$\mathcal S$. In terms of the rank-counted list, $N_\gamma$ is the
number of entries $>\gamma$ and $B_\gamma$ is their sum. Finally
$\mathcal S(\gamma)$ is the sum inside $\mathcal S$ of all irreducible
subsheaves $W$ with $\dw_\iota(W)=\gamma$, hence a well-defined
subsheaf: each $V_a$ with $\dw_\iota(V_a)=\gamma$ is such a $W$;
conversely, for such a $W$ the projection $W\to V_a$ is zero unless
$W\cong V_a$ (Schur's lemma, both being irreducible), so $W$ lies in
the sum of the $V_a$ isomorphic to $W$, all of which have
$\dw_\iota(V_a)=\dw_\iota(W)=\gamma$. In particular
$\mathcal S=\bigoplus_{\gamma}\mathcal S(\gamma)$, the sum running over
the finitely many distinct constituent determinant weights, and
$\operatorname{rank}\mathcal S(\gamma)$ is the number of entries equal
to $\gamma$ in the rank-counted list.
