+++
id = "sk-prop-av-isogeny"
kind = "section"
title = "The multiplication-by-$n$ isogeny"
lean = ["AlgebraicGeometry.isIsogeny_npow_id"]
order = 559
uses = ["sk-def-av", "sk-def-av-ample-degree", "sk-def-av-isogeny", "sk-def-av-mult-n", "sk-prop-av-deg-pullback", "sk-prop-av-isogeny-degree", "sk-prop-av-mult-finite", "sk-prop-av-mult-hom", "sk-prop-av-mult-n-pullback", "sk-prop-av-mult-surjective", "sk-prop-av-projective", "sk-prop-av-symmetric-ample"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety of dimension $g$ over a field $k$ and let
$n\ge1$. Then $[n]:A\to A$ of [sk-def-av-mult-n] is a finite flat
surjective homomorphism, hence an isogeny, of degree $n^{2g}$, and its
kernel $A[n]$ is a finite flat group scheme over $k$ of order $n^{2g}$.

## Proof

$[n]$ is a homomorphism by [sk-prop-av-mult-hom] and
[sk-cor-av-commutative], finite by [sk-prop-av-mult-finite] and
surjective by [sk-prop-av-mult-surjective]; it is flat with
$[n]_*\cO_A$ locally free of rank $\deg[n]$, and $\deg[n]$ is the order
of the kernel, by [sk-prop-av-isogeny-degree]. So $[n]$ is an isogeny.

For the degree, take the ample symmetric $\cN$ of
[sk-prop-av-projective] and [sk-prop-av-symmetric-ample]. By
[sk-prop-av-mult-n-pullback] $[n]^*\cN\cong\cN^{\otimes n^2}$; hence

$$
\deg_{\cN^{\otimes n^2}}(A)=n^{2g}\deg_{\cN}(A),
$$

because replacing $\cN$ by $\cN^{\otimes n^2}$ replaces
$\chi(A,\cN^{\otimes m})$ by $\chi(A,\cN^{\otimes mn^2})$, which
multiplies the leading coefficient of the numerical polynomial, and
with it the degree of [sk-def-av-ample-degree], by $n^{2g}$. On the
other hand [sk-prop-av-deg-pullback] applied to the finite surjective
$[n]:A\to A$ gives

$$
\deg_{[n]^*\cN}(A)=\deg([n])\cdot\deg_{\cN}(A).
$$

The two left-hand sides agree, and $\deg_{\cN}(A)\neq0$: for an ample
module on a proper $g$-dimensional variety over a field the degree is
positive (Stacks `0BEV`), and here $g=\dim A$. Comparing gives
$\deg[n]=n^{2g}$, and the order of $A[n]$ is $\deg[n]$ by
[sk-prop-av-isogeny-degree]. Flatness of the kernel over $k$ is the
flatness of the finite morphism $[n]$.

Uses: [sk-def-av-ample-degree], [sk-def-av-isogeny], [sk-def-av-mult-n], [sk-def-av], [sk-prop-av-deg-pullback], [sk-prop-av-isogeny-degree], [sk-prop-av-mult-finite], [sk-prop-av-mult-hom], [sk-prop-av-mult-n-pullback], [sk-prop-av-mult-surjective], [sk-prop-av-projective], [sk-prop-av-symmetric-ample]
