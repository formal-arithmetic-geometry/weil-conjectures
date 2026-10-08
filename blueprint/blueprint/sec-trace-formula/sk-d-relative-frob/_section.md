+++
id = "sk-d-relative-frob"
kind = "section"
title = "The relative Frobenius factorization"
order = 2359
uses = ["sk-d-setup", "sk-d-weil"]
lean = ["AlgebraicGeometry.ProEtale.relativeFrobenius"]
+++
*Definition (sketch).*

For a map $f_0:X_0\to Y_0$ of
finite-type separated schemes over $\mathbf F_q$,
write $f:X\to Y$ for its geometric base change and put

$$
X'_m=Y\times_{\Phi_{Y,m},Y,f}X,
\quad p_m:X'_m\to X,\quad f'_m:X'_m\to Y,
\quad r_m=(f,\Phi_{X,m}):X\to X'_m.
$$

Here the maps $\Phi$ are the Frobenius maps;
$p_mr_m=\Phi_{X,m}$ and $f'_mr_m=f$.

Uses: [sk-d-setup], [sk-d-weil]
