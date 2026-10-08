+++
id = "lem-pc-projective-space-twist-quotient"
kind = "lemma"
title = "A finite quotient by twists"
order = 626
uses = ["def-pc-projective-space-twist", "lem-pc-section-clearing-denominators", "pqf-def-coherent", "pqf-lem-coherent-ft-locnoeth"]
+++
Let $A$ be Noetherian, $P=\mathbf P^n_A$, and $\mathcal F$ a
coherent module on $P$.
There are integers $m_1,\ldots,m_r\ge0$ and a surjection

$$
\bigoplus_{j=1}^r\mathcal O_P(-m_j)\longrightarrow\mathcal F,
$$

where the summands are the
twisting modules.
Its kernel is coherent.

## Proof

On every standard affine $U_i=D_+(x_i)$, choose finitely many
generators $t_{ia}$ of $\mathcal F|_{U_i}$, using the finite-module
description in [pqf-lem-coherent-ft-locnoeth].
The space $P$ is separated over $\operatorname{Spec}(A)$: on each
$U_i\times_A U_j$, its diagonal is the closed subscheme given by
the equations $x_a y_b=x_b y_a$ for all $a,b$, where $x_i=y_j=1$.
For example $x_jy_i=1$ identifies that subscheme with the affine
intersection $U_i\cap U_j$. Thus the clearing-denominators lemma
applies to $P$ and its standard finite affine cover.
Apply [lem-pc-section-clearing-denominators] to the section
$x_i$ of $\mathcal O_P(1)$ from
[def-pc-projective-space-twist]. It gives an exponent $m_{ia}$
and a global section $u_{ia}$ of $\mathcal F(m_{ia})$ with
$u_{ia}|_{U_i}=t_{ia}\otimes x_i^{m_{ia}}$.
Tensoring the section map $\mathcal O_P\to\mathcal F(m_{ia})$
by $\mathcal O_P(-m_{ia})$ defines a map
$\mathcal O_P(-m_{ia})\to\mathcal F$.
On $U_i$, its image contains the chosen generator $t_{ia}$,
because $x_i^{m_{ia}}$ is a basis of the twisting module there.
The finite direct sum of all these maps is therefore surjective
on every $U_i$, hence on $P$.

The coordinate rings of the standard charts are polynomial rings
over the Noetherian ring $A$, and are Noetherian by the Hilbert
basis theorem. The kernel on each chart is a submodule of a finite
free module over such a ring, hence is finite. Kernels of maps
of quasi-coherent modules are quasi-coherent by exactness of
localization. By [pqf-lem-coherent-ft-locnoeth] these kernels
form a coherent sheaf on $P$.
