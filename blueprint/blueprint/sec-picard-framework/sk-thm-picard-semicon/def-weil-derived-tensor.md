+++
id = "def-weil-derived-tensor"
kind = "definition"
title = "Derived tensor notation"
order = 663
uses = ["def-weil-pbc-proetale-site"]
+++
Fix a scheme $Y$ and a commutative ring $A$, and use the small pro-etale site
[def-weil-pbc-proetale-site] $Y_{\mathrm{proet}}$. A complex $P$
of $A_Y$-modules is *K-flat* if tensoring it with every acyclic complex
preserves acyclicity. For complexes $K_1,K_2$ of $A_Y$-modules, choose a
quasi-isomorphism $P\to K_1$ with $P$ K-flat and define

$$
 K_1\otimes_A^L K_2=P\otimes_A K_2
$$

in $D(Y_{\mathrm{proet}},A)$. For a ring map $A\to B$ and a complex $K_1$,
write $K_1\otimes_A^L B$ for derived tensor with the constant $B_Y$-module.
