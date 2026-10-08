+++
id = "def-wf-abelian-tate-module"
kind = "definition"
title = "The Tate module used in the curve argument"
lean = ["AlgebraicGeometry.IsAbelianScheme.tateModule"]
order = 470
uses = ["def-sc-abelian-variety", "def-sc-mult-n", "def-tate-module-abelian-group"]
+++
Let $A$ be an abelian variety over an
algebraically closed field of characteristic different from $\ell$. For
the torsion subgroup
$A[\ell^n]=\ker([\ell^n]:A\to A)$, define

$$
T_\ell A:=\varprojlim_n A[\ell^n](\overline k),
\qquad
V_\ell A:=T_\ell A\otimes_{\mathbf Z_\ell}\mathbf Q_\ell,
$$

where the transition map from level $n+1$ to level $n$ is
multiplication by $\ell$. Every endomorphism of $A$, and every
semilinear automorphism of $A$ over an automorphism of the ground field,
acts componentwise on these inverse limits; for the geometric Jacobian of a
curve these semilinear automorphisms are supplied by the next lemma.
The abelian-variety and torsion-subgroup conventions are those of
[def-sc-abelian-variety], [def-sc-mult-n].

In the notation of [def-tate-module-abelian-group], $T_\ell A=T_\ell\bigl(A(\overline k)\bigr)$ and $V_\ell A=V_\ell\bigl(A(\overline k)\bigr)$: the definition above is the Tate module of the abelian group $A(\overline k)$.
