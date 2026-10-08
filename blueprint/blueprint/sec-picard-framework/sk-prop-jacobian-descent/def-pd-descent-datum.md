+++
id = "def-pd-descent-datum"
kind = "definition"
title = "Descent datum for a scheme along a morphism"
order = 859
uses = ["def-pc-base-change", "def-pc-morphism-conventions"]
+++
Let $X\to Y$ be a morphism of schemes and let $V$ be a scheme over $X$. Write
$X_2=X\times_YX$ and $X_3=X\times_YX\times_YX$ for the
fibre products over $Y$, with the projections
$\mathrm{pr}_0,\mathrm{pr}_1:X_2\to X$ and
$\mathrm{pr}_{01},\mathrm{pr}_{02},\mathrm{pr}_{12}:X_3\to X_2$. A
*descent datum on $V$ over $X/Y$* is an isomorphism
$\varphi:\mathrm{pr}_0^*V\to\mathrm{pr}_1^*V$ of schemes over $X_2$ satisfying
the cocycle condition
$\mathrm{pr}_{02}^*\varphi =\mathrm{pr}_{12}^*\varphi\circ\mathrm{pr}_{01}^*\varphi$
over $X_3$ (Stacks Project, Descent, Definition 35.34.1, Tag
[023V](https://stacks.math.columbia.edu/tag/023V)). The datum is
*effective* if there are a scheme $V_0$ over $Y$ and an isomorphism
$V\cong V_0\times_YX$ over $X$ whose pullback to $X_2$ recovers $\varphi$.
