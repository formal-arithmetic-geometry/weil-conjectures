+++
id = "def-sp-convergence"
kind = "definition"
title = "Convergence of a couple"
order = 510
uses = ["def-sp-exact-couple", "def-sp-filtration"]
+++
In the situation of [def-sp-exact-couple], regard all cycle and boundary
objects as subobjects of the initial page $E_2$. Set $Z_2=E_2$, $B_2=0$.
Given $E_r=Z_r/B_r$, define $Z_{r+1}\subseteq Z_r$ as the inverse image of
$\ker d_r$, and $B_{r+1}\subseteq Z_r$ as the inverse image of
$\operatorname{im}d_r$ under $Z_r\twoheadrightarrow E_r$, component by
component. Thus $E_{r+1}=Z_{r+1}/B_{r+1}$, the $Z_r$ decrease, and the $B_r$
increase inside $E_2$. When these limits exist, put
$Z_\infty=\bigcap_rZ_r$, $B_\infty=\bigcup_rB_r$, and
$E_\infty=Z_\infty/B_\infty$. The couple is *regular* if each
$B_r^{p,q}\subseteq E_2^{p,q}$ is eventually constant. It is *complete* if
the subobjects $\operatorname{im}(\alpha^r:D^{p+r,q-r}\to D^{p,q})$ have zero
intersection for every $(p,q)$. It *converges to the filtration
[def-sp-filtration] of an object $A$* if

$$
 E_\infty^{p,q}\cong\operatorname{gr}^pA^{p+q}
$$

compatibly with the structure maps (the *abutment*).
