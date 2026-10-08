+++
id = "prop-sf-pf-coherence"
kind = "theorem"
title = "Coherence of the projection formula"
order = 2102
tags = ["latex:proposition"]
uses = ["def-sf-datum", "def-sf-pf", "fix-prop-adjunctions", "prop-sf-pf-reduction", "thm-sf-pf-field", "thm-sf-pf-proetale", "thm-sf-comp-composition"]
+++
In the setting of [def-sf-datum], the projection transformations
satisfy: naturality in $K$, $L$, $f$ and the coefficient ring; the identity
for $f=\operatorname{id}$; the associativity pentagon for composable
$f,g$, compatible with the composition law (A4), i.e. the isomorphism
$\alpha_{g,f}:Rg_!Rf_!\cong R(gf)_!$ of [thm-sf-comp-composition]; independence of the chosen
compactification; the identification with the direct-image projection
formula through $Rf_!\cong Rf_*$ for proper $f$; compatibility with base
change, i.e. for a Cartesian square $(f',g',f,g)$ the square

$$
\begin{array}{ccc}
Lg^*\bigl(Rf_!K\otimes^L_\Lambda L\bigr)&\xrightarrow{\ Lg^*\operatorname{PF}_{f,K,L}\ }&
Lg^*Rf_!\bigl(K\otimes^L_\Lambda Lf^*L\bigr)\\
{\scriptstyle \operatorname{Ex}_!\otimes1}\downarrow&&\downarrow{\scriptstyle \operatorname{Ex}_!}\\
Rf'_!Lg'^*K\otimes^L_\Lambda Lg^*L&\xrightarrow{\ \operatorname{PF}_{f',Lg'^*K,Lg^*L}\ }&
Rf'_!\bigl(Lg'^*K\otimes^L_\Lambda Lf'^*Lg^*L\bigr)
\end{array}
$$

commutes, with $\operatorname{Ex}_!$ the exchange of axiom (A2) and the
vertical arrows read through the monoidality isomorphisms
$Lg^*(M\otimes^LN)\cong Lg^*M\otimes^LLg^*N$ and $Lg'^*Lf^*\cong Lf'^*Lg^*$
(the projection formula commutes with base change; SGA 4, XVII, §5.2); and
compatibility with finite reduction, scalar extension and the pro-étale
realization.

## Proof

All projection transformations appearing below are those of
[def-sf-pf].
Naturality is the naturality of the mate construction, which uses only the
natural units and counits of the axioms; for $f=\operatorname{id}$ the two
adjunctions are the identity adjunction and the mate of the identity is the
identity. The pentagon: both sides are mates of the same composite of the
two component mate constructions, because the units and counits of composite
adjunctions are the pasted ones by [fix-prop-adjunctions], item (3)
(through the composition isomorphism of [thm-sf-comp-composition]),
and pasting of mates is associative; the associativity of the derived tensor
product identifies the two tensor reassociations. Independence of the
compactification is the compatibility of the refinement comparisons with
the counits and with $j_!$, together with naturality. The proper case is
(A4). Compatibility with base change: choose a compactification
$f=p\circ j$ and base change it along $g$ to $f'=p'\circ j'$, with
$\bar g':\overline X'\to\overline X$ over $g$; by (A2) and (A4),
$\operatorname{Ex}_!$ is the identification $L\bar g'^*j_!\cong j'_!Lg'^*$
followed by the proper-base-change exchange $\operatorname{Ex}_*$ for $p$.
On the $j_!$ factor both composites take values in the essential image of
$j'_!$, where a map is determined by its restriction to $X'$, and both
restrict to the identity. On the $p$ factor, for $M$ on $\overline X$:
$\operatorname{PF}_{p,M,L}$ is the transpose under $Lp^*\dashv Rp_*$ of
$\varepsilon_p\otimes1$ ($\varepsilon_p$ the counit) read through the
monoidality of $Lp^*$, and $\operatorname{Ex}_*$ is the mate of
$L\bar g'^*Lp^*\cong Lp'^*Lg^*$ under $Lp^*\dashv Rp_*$ and
$Lp'^*\dashv Rp'_*$; transposing the two composites
$Lg^*(Rp_*M\otimes^LL)\to Rp'_*(L\bar g'^*M\otimes^LLp'^*Lg^*L)$ under
$Lp'^*\dashv Rp'_*$ gives, by the pasting compatibility of mates
([lem-sf-mate]) and the triangle identity for $p$, one and the same map
$Lp'^*Lg^*(Rp_*M\otimes^LL)\to L\bar g'^*M\otimes^LLp'^*Lg^*L$, namely
$L\bar g'^*\varepsilon_p\otimes1$ read through the monoidality isomorphisms;
so the two composites are mates of the same composite. The same computation
with an arbitrary $L'$ on $Y'$ in place of $Lg^*L$ identifies
$\operatorname{PF}_{p'}\circ(\operatorname{Ex}_*\otimes1)$ with the
transpose of $L\bar g'^*\varepsilon_p\otimes1$, which is the form used for
the symmetry of the relative product. The last clause is
[prop-sf-pf-reduction], [thm-sf-pf-field] and [thm-sf-pf-proetale].
