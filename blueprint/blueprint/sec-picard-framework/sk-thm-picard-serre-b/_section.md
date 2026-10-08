+++
id = "sk-thm-picard-serre-b"
kind = "section"
title = "Serre's theorem B: vanishing after a twist"
order = 622
uses = ["sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist"]
+++
*Theorem (sketch).*

Let $X\subseteq\PP^n_k$ be a closed subscheme and $\cF$ coherent on
$X$. Then $H^q(X,\cF\otimes\cO_X(m))=0$ for all $q>0$ and
$m\gg0$.

## Proof

Let $i:X\hookrightarrow\PP^n_k$ be the inclusion. Since $i$ is a closed
immersion, $i_*\cF$ is coherent on $\PP^n_k$,
$i_*(\cF\otimes\cO_X(m))=(i_*\cF)(m)$ and
$H^q(X,\cF\otimes\cO_X(m))=H^q(\PP^n_k,(i_*\cF)(m))$, so we may assume
$X=\PP^n_k$.

*Step 1 (a finite presentation by twists).* On each standard
chart $D_+(x_j)$ choose finitely many generators of $\cF$; for each such
generator $t$, clearing denominators (multiply by a power $x_j^{e}$;
the overlaps of the standard cover are affine, $\PP^n_k$ being separated
over $k$) extends $t\otimes x_j^{e}$ to a global section of $\cF(e)$.
The resulting finitely many maps $\cO(-e_\nu)\to\cF$ give a surjection
$\bigoplus_\nu\cO(-e_\nu)\to\cF$ with coherent kernel $\mathcal R$.

*Step 2 (descending induction on $q$).* We prove, for all
coherent $\cF$ at once, that $H^q(\cF(m))=0$ for $m\gg0$, by descending
induction on $q\ge1$. For $q>n$ this holds for every $m$: the
Čech complex of the standard cover computes $H^*(\PP^n_k,\cF(m))$ by
[sk-lem-picard-cech-computes] and has only $n+1$ members. For
$1\le q\le n$ the twisted sequence
$0\to\mathcal R(m)\to\bigoplus_\nu\cO(m-e_\nu)\to\cF(m)\to0$ gives the exact
sequence

$$
\textstyle\bigoplus_\nu H^q(\PP^n_k,\cO(m-e_\nu))\to H^q(\PP^n_k,\cF(m))
\to H^{q+1}(\PP^n_k,\mathcal R(m)),
$$

whose left term vanishes for $m\ge\max_\nu e_\nu-n$ by the two vanishing
clauses of [sk-thm-picard-pn] ($H^q(\PP^n_k,\cO(d))=0$ for
$q\notin\{0,n\}$, and $H^n(\PP^n_k,\cO(d))=0$ for $d\ge-n$), and whose
right term vanishes for $m\gg0$ by the induction hypothesis applied to
$\mathcal R$. The detailed forms are Blueprint 50,
`lem-pc-projective-space-twist-quotient`,
`lem-pc-projective-space-serre-vanishing` and
`lem-pc-serre-vanishing`.
