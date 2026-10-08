+++
id = "lem-sc-curves-quasi-projective"
kind = "lemma"
title = "Curves are quasi-projective"
order = 922
uses = ["def-sc-curves", "def-sc-quasi-projective", "lem-chow-segre", "lem-sc-dim0-finite", "lem-sc-positive-degree-ample"]
+++
Every smooth separated curve over a field
$k$ is quasi-projective: there
is a locally closed immersion $C\hookrightarrow\mathbf P^N_k$.

## Proof

Since $C$ is a separated scheme of finite type over $k$, it is
covered by finitely many affine open subschemes $U_1,\dots,U_r$,
each a closed subscheme of some $\mathbf A^{n_i}\subset\mathbf P^{n_i}$ (finite type over $k$ means each $U_i$ is
$\operatorname{Spec}$ of a finitely generated $k$-algebra).
We prove by induction on $i$ that
$V_i:=U_1\cup\cdots\cup U_i$ admits a locally closed immersion into a
projective space; the case $i=r$ is the claim. Suppose
$V_{i-1}\hookrightarrow\mathbf P^N$ is a locally closed immersion with
dense image in its closure, and $U_i\hookrightarrow\mathbf A^M$ is
a closed immersion; put $W:=V_{i-1}\cap U_i$. Since $\dim C\leq1$,
the complement $V_{i-1}\setminus W$ is a finite set of closed
points ([lem-sc-dim0-finite]). The classical gluing step
constructs the embedding of $V_i$ as follows; this is the argument
of Stacks Project, Varieties, Lemma 33.43.3, [Tag 0A25](https://stacks.math.columbia.edu/tag/0A25), which asserts
that every separated scheme of finite type of dimension at most one
over a field is H-quasi-projective (here proven directly). On each irreducible
component of $V_{i-1}$, choose a line bundle together with
sections that separate the finitely many points of
$V_{i-1}\setminus W$ (and their tangent directions) from one
another and from $W$, using the very-ample construction of
[lem-sc-positive-degree-ample] on the compactification of the
component; the closed diagonal of $C$ (separatedness) lets one
choose these sections compatibly with the affine embedding of $U_i$
on $W$. Combining the embedding of $V_{i-1}$ into
$\mathbf P^N$, the embedding of $U_i$ into $\mathbf A^M$, and
these sections gives an embedding of $V_i$ into
$\mathbf P^N\times\mathbf P^M$, hence into a single projective
space via the Segre embedding ([lem-chow-segre]). After $r$ steps one obtains a
locally closed immersion $C\hookrightarrow\mathbf P^{N'}_k$.
