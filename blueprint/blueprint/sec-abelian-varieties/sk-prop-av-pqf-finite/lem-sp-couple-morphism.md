+++
id = "lem-sp-couple-morphism"
kind = "lemma"
title = "Morphisms of couples give morphisms of spectral sequences"
order = 513
uses = ["def-sp-convergence", "def-sp-exact-couple", "def-sp-filtration", "thm-sp-half-plane-convergence"]
+++
A morphism $(t_D,t_E):(D,E,\alpha,f,g)\to(D',E',\alpha',f',g')$ of exact
couples [def-sp-exact-couple] (two maps compatible with all structure maps)
induces, for every $r$, a morphism $E_r\to E'_r$ of the spectral sequences,
compatible with the differentials. If both couples satisfy the hypotheses of
[thm-sp-half-plane-convergence], then the map $t_D:D^{0,n}\to D'^{0,n}$ of
their canonical abutments respects the filtrations
[def-sp-filtration] constructed there, and induces $t_E$ on the associated
graded pieces.

## Proof

The derived couple construction is functorial in the couple
([def-sp-exact-couple]): $t_D$ and $t_E$ induce maps on $D'$ and $E'$
commuting with the induced structure maps; iterating gives maps on all $E_r$,
compatible with the differentials $d_r=g_r\circ f_r$. At infinity $t_E$
restricts to $Z_\infty$ and maps $B_\infty$ into $B'_\infty$, giving a map on
$E_\infty$ by [def-sp-convergence]. Under the hypotheses of
[thm-sp-half-plane-convergence], the map on abutments is already supplied by
$t_D^{0,n}$. Commutation with every power of $\alpha$ sends
$\operatorname{im}(D^{n-q,q}\to D^{0,n})$ into
$\operatorname{im}(D'^{n-q,q}\to D'^{0,n})$, proving that it preserves the
image filtration. The associated graded identification is obtained from the
same derived-couple exact sequences, so its map is precisely the one induced
by $t_E$. All these constructions commute with composition of morphisms of
couples.
