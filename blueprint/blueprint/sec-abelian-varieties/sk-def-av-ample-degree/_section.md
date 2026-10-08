+++
id = "sk-def-av-ample-degree"
kind = "section"
title = "Ample modules and the Hilbert degree"
lean = ["AlgebraicGeometry.IsAmple", "AlgebraicGeometry.Scheme.Hom.degree"]
order = 435
+++
*Definition (sketch).*

Let $X$ be a proper scheme of dimension $g$ over a field $k$. An
invertible $\cO_X$-module $\cM$ is *ample* if $\cM^{\otimes m}$ is
very ample for some $m\ge1$, i.e. if it is the pullback of
$\cO(1)$ along a closed immersion $X\hookrightarrow\mathbf P^N_k$ for
some $m$. For ample $\cM$ the function $m\mapsto \chi(X,\cM^{\otimes m})$ is a numerical polynomial of degree at most
$g$ (the Hilbert polynomial), and the *degree of $X$ with respect
to $\cM$* is

$$
\deg_{\cM}(X):=g!\cdot\bigl(\text{leading coefficient of }
m\mapsto\chi(X,\cM^{\otimes m})\bigr).
$$
