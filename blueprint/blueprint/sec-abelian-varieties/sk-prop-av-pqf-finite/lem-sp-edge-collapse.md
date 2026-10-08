+++
id = "lem-sp-edge-collapse"
kind = "lemma"
title = "Edge collapse and edge maps"
order = 514
uses = ["def-sp-convergence", "def-sp-exact-couple"]
+++
Let $(D,E,\alpha,f,g)$ be an exact couple [def-sp-exact-couple] whose
spectral sequence converges [def-sp-convergence] to a filtration of an object
$A$ with a finite, exhaustive, separated filtration, and suppose that for
some $r_0$ all entries $E_{r_0}^{p,q}$, $p\ne0$, vanish. Then every
differential $d_r$ with $r\geq r_0$ vanishes, all pages equal $E_{r_0}$,
$E_\infty=E_{r_0}$, and the edge map

$$
 A^n\longrightarrow E_{r_0}^{0,n}
$$

is an isomorphism in each degree $n$.

## Proof

By [def-sp-exact-couple], the differentials are $d_r=g_r\circ f_r$, of
bidegree $(r,1-r)$, so every differential out of an entry of the $p=0$ column
has target in a bidegree with positive first index and every incoming
differential has source with negative first index. Both vanish by hypothesis,
so each $d_r$, $r\geq r_0$, vanishes; hence every page equals $E_{r_0}$ and
the intersection/union formulas of [def-sp-convergence] give
$E_\infty=E_{r_0}$. The convergence identifies $\operatorname{gr}^0A^n\cong
E_\infty^{0,n}$; only $p=0$ survives, and the canonical map $A^n\to
\operatorname{gr}^0A^n=E_\infty^{0,n}$ is an isomorphism: the vanishing of
all other graded pieces, with the finite exhaustive separated filtration,
gives $F^0A^n=A^n$ and $F^1A^n=0$.
