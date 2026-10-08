+++
id = "sk-prop-av-mult-finite"
kind = "section"
title = "Finiteness of the fibres of the multiplication map"
lean = ["AlgebraicGeometry.isFinite_npow_id"]
order = 551
uses = ["sk-def-av", "sk-def-av-mult-n", "sk-prop-av-ample-positive", "sk-prop-av-mult-hom", "sk-prop-av-mult-n-pullback", "sk-prop-av-pqf-finite", "sk-prop-av-symmetric-ample"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety over $k$ and $n\ge1$. Then $[n]:A\to A$
is finite; in particular $A[n]=\ker[n]$ is a finite group scheme.

## Proof

By [sk-prop-av-symmetric-ample] there is an ample $\cN$ with
$[-1]^*\cN\cong\cN$, and by [sk-prop-av-mult-n-pullback]
$[n]^*\cN\cong\cN^{\otimes n^2}$. We first reduce to $k$
algebraically closed, as [sk-prop-av-ample-positive] requires. Let
$\bar k$ be an algebraic closure of $k$. Then $A_{\bar k}$ is an abelian
variety over $\bar k$ ($A$ is connected with a rational point, hence
geometrically connected, `04KV`), $[n]$ base-changes to $[n]$ of
$A_{\bar k}$, the isomorphism $[n]^*\cN\cong\cN^{\otimes n^2}$
base-changes, and $\cN_{\bar k}$ is ample (a closed immersion
$A\hookrightarrow\mathbf P^N_k$ with $\cN^{\otimes m}\cong\cO(1)|_A$
base-changes to one of $A_{\bar k}$). If all fibres of $[n]_{\bar k}$
are finite, so are those of $[n]$: the fibre of $[n]$ over $y\in A$ is
the image of the fibre of $[n]_{\bar k}$ over any point $\bar y$ above
$y$, the latter being the base change of the former along
$\kappa(y)\subseteq\kappa(\bar y)$, and such a base change is surjective.
So assume $k=\bar k$. As the quasi-finite locus of $[n]$ is open and
$A$ is Jacobson, it suffices to treat the fibres over closed points $y$,
which are closed subschemes of $A$. If such a fibre $[n]^{-1}(y)$ had
positive dimension it would contain a proper curve $C$ on which $[n]$
is constant, so $\cO_C\cong[n]^*\cN|_C\cong\cN^{\otimes n^2}|_C$; but
the restriction of an ample module to a closed subscheme is ample and
an ample module on a proper curve has positive degree
([sk-prop-av-ample-positive]), hence is not trivial — contradiction.
Thus every fibre of $[n]$ is finite; since $[n]$ is proper ($A$ is
proper and $A$ is separated) and quasi-finite, it is finite by
[sk-prop-av-pqf-finite]. The kernel is the fibre over $e$.

Uses: [sk-def-av-mult-n], [sk-def-av], [sk-prop-av-ample-positive], [sk-prop-av-mult-hom], [sk-prop-av-mult-n-pullback], [sk-prop-av-pqf-finite], [sk-prop-av-symmetric-ample]
