+++
id = "lemma-nagata-composite-valuation-ring"
kind = "lemma"
title = "Composite of two valuation rings"
order = 274
lean = ["ValuationSubring.comapResidue"]
+++
Let $A'$ be a valuation ring with maximal ideal $\mathfrak m'$, and let
$A''$ be a valuation subring of the residue field
$k'=A'/\mathfrak m'$. The inverse image

$$
C=\{a\in A'\mid a\bmod\mathfrak m'\in A''\}
$$

is a valuation ring. Its fraction field is the fraction field of $A'$,
$\mathfrak m'\subseteq C$, and $C/\mathfrak m'\cong A''$.

## Proof

Let $x$ be a nonzero element of $\operatorname{Frac}(A')$. Since
$A'$ is a valuation ring, either $x\in A'$ or $x^{-1}\in A'$. If
exactly one lies in $A'$, that element lies in $C$ whenever its residue
is zero. If both are units of $A'$, compare their nonzero residue classes
in $k'$; the valuation-ring property of $A''$ puts one of the two
residues in $A''$, and hence puts $x$ or $x^{-1}$ in $C$. Thus
$C$ is a valuation ring. If $\mathfrak m'=0$, then $A'=k'$ is a field,
$C=A''$, and $\operatorname{Frac}(C)=k'=A'$. If
$\mathfrak m'\ne0$, choose $0\ne t\in\mathfrak m'$. For every $a\in A'$,
both $at$ and $t$ lie in $\mathfrak m'\subseteq C$, so
$a=(at)/t\in\operatorname{Frac}(C)$. Hence in this case also
$\operatorname{Frac}(C)=\operatorname{Frac}(A')$. The restricted residue
map $C\to A''$ is surjective by the inverse-image definition, and its
kernel is $\mathfrak m'$, giving $C/\mathfrak m'\cong A''$.
