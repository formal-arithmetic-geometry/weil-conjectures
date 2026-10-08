+++
id = "sk-prop-av-cube"
kind = "section"
title = "The theorem of the cube"
lean = ["AlgebraicGeometry.nonempty_iso_cube"]
order = 479
uses = ["sk-def-av", "sk-def-av-pic"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety over a field $k$ and let $\cL$ be an
invertible $\cO_A$-module. For $1\le i_1<\dots<i_t\le3$ let
$m_{i_1\dots i_t}:A\times_kA\times_kA\to A$ be the partial sum map
$(x_1,x_2,x_3)\mapsto x_{i_1}+\dots+x_{i_t}$. Then

$$
m_{123}^*\cL\otimes m_1^*\cL\otimes m_2^*\cL\otimes m_3^*\cL
\;\cong\;
m_{12}^*\cL\otimes m_{13}^*\cL\otimes m_{23}^*\cL
$$

on $A\times_kA\times_kA$.

## Proof

Apply the general cube theorem (`0BF4`) with $X=Y=Z=A$ over
$S=\Spec k$ and the unit sections $x=y=e$ to

$$
\cM=m_{123}^*\cL\otimes m_1^*\cL\otimes m_2^*\cL\otimes m_3^*\cL
\otimes m_{12}^*\cL^{-1}\otimes m_{13}^*\cL^{-1}\otimes m_{23}^*\cL^{-1}.
$$

Its hypotheses hold: $A\to\Spec k$ is flat, proper, of finite
presentation with geometrically integral fibres (smooth, proper and
connected over $k$, hence geometrically integral since $k$ is a field),
and $A$ is connected, so it has the $k$-point $e$. On the three faces
$A\times A\times e$, $A\times e\times A$, $e\times A\times A$ the
restriction of $\cM$ is $\cO$: all seven factors cancel there, since
the partial sums collapse to $n_{12},n_1,n_2$ and $e^*\cL\cong\cO$.
Hence $\cM\cong\cO$, which is the displayed relation.

Uses: [sk-def-av]
