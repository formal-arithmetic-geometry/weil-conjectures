+++
id = "def-sc-p1-standard"
kind = "definition"
title = "The standard affine cover and the twists on $\\mathbf P^1_k$"
order = 612
+++
Let $k$ be a field and
$\mathbf P^1_k=\operatorname{Proj}k[x_0,x_1]$. The
*standard affine cover* is

$$
U_0:=D(x_0)=\operatorname{Spec}k[t],\quad t:=x_1/x_0,
\qquad
U_1:=D(x_1)=\operatorname{Spec}k[s],\quad s:=x_0/x_1,
$$

$$
U_{01}:=U_0\cap U_1=\operatorname{Spec}k[t,t^{-1}].
$$

For $d\in\mathbf Z$, a *twisted structure sheaf*
$\mathcal O(d)$ on $\mathbf P^1_k$ is an
$\mathcal O_{\mathbf P^1_k}$-module together with generating
sections $g_0\in\Gamma(U_0,\mathcal O(d))$ and
$g_1\in\Gamma(U_1,\mathcal O(d))$ that trivialize it over $U_0$
and over $U_1$ and satisfy the glueing relation

$$
g_0=t^{-d}g_1\qquad\text{over }U_{01}.
$$

For $d=1$ we take $g_0=x_0$ and $g_1=x_1$, so that
$\mathcal O(1)$ is the tautological bundle with the glueing
$x_0=t^{-1}x_1$.
