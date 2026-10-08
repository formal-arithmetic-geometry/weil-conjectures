+++
id = "sk-prop-sf-pf-coherence"
kind = "section"
title = "Coherence of the projection formula"
order = 2101
uses = ["sk-lem-sf-mate", "sk-prop-sf-comp-proper", "sk-prop-sf-pf-reduction", "sk-thm-sf-pf-field", "sk-thm-sf-pf-finite", "sk-thm-sf-pf-proetale"]
lean = ["AlgebraicGeometry.Etale.hasProjectionFormula_id", "AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp", "AlgebraicGeometry.Etale.hasProjectionFormula_comp", "AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_iff"]
+++
*Proposition (sketch).*

The projection transformations are natural in $K$, $L$, $f$ and the
coefficient ring; the transformation for $f=\mathrm{id}$ is the identity; the
associativity pentagon for composable $f,g$ commutes and is compatible with
the composition law of def:compact-support-direct-image; the
transformation is independent of the chosen compactification; for proper $f$
it agrees with the direct-image projection formula through $Rf_!\cong Rf_*$;
it is *compatible with base change*: for a Cartesian square
$(f',g',f,g)$ as in [sk-def-sf-exchanges], $K\in\Dbc(X,\Lambda)$ and
$L\in\Dctf(Y,\Lambda)$ (pullback preserves both classes) the square

$$
\begin{array}{ccc}
Lg^*\bigl(Rf_!K\otimes^L_\Lambda L\bigr)&\xrightarrow{\ Lg^*\operatorname{PF}_{f,K,L}\ }&
Lg^*Rf_!\bigl(K\otimes^L_\Lambda Lf^*L\bigr)\\
{\scriptstyle \operatorname{Ex}_!\otimes1}\downarrow&&\downarrow{\scriptstyle \operatorname{Ex}_!}\\
Rf'_!Lg'^*K\otimes^L_\Lambda Lg^*L&\xrightarrow{\ \operatorname{PF}_{f',Lg'^*K,Lg^*L}\ }&
Rf'_!\bigl(Lg'^*K\otimes^L_\Lambda Lf'^*Lg^*L\bigr)
\end{array}
$$

commutes, the vertical arrows being read through the monoidality
isomorphisms $Lg^*(M\otimes^LN)\cong Lg^*M\otimes^LLg^*N$ and
$Lg'^*Lf^*\cong Lf'^*Lg^*$ (the projection formula commutes with base
change; SGA 4, XVII, §5.2);
and it is compatible with finite reduction, scalar extension and the
pro-étale realization. Every one of these assertions is an identity between
natural transformations of the functors typed in [sk-def-sf-operations] and
[sk-def-sf-exchanges], at the categories written there.

## Proof

Naturality is that of the mate construction, which uses only the natural units
and counits. For $f=\mathrm{id}$ the two adjunctions are the identity
adjunction and the mate of the identity is the identity. In the pentagon both
sides are mates of the same composite of the two component mate constructions,
because the units and counits of composite adjunctions are the pasted ones and
pasting of mates is associative; the associativity of the derived tensor
product identifies the two tensor reassociations. Independence of the
compactification is the compatibility of the refinement comparisons with the
counits and with $j_!$, together with naturality and
prop:compactification-coherence. Compatibility with base change: choose
a compactification $f=p\circ j$ and base change it along $g$ to
$f'=p'\circ j'$, with $\bar g':\overline X'\to\overline X$ over $g$; by
[sk-def-sf-exchanges] and [sk-prop-sf-comp-proper], $\operatorname{Ex}_!$
is the identification $L\bar g'^*j_!\cong j'_!Lg'^*$ followed by the
proper-base-change exchange $\operatorname{Ex}_*$ for $p$. On the $j_!$
factor both composites take values in the essential image of $j'_!$, where a
map is determined by its restriction to $X'$, and both restrict to the
identity. On the $p$ factor, for $M$ on $\overline X$:
$\operatorname{PF}_{p,M,L}$ is the transpose under $Lp^*\dashv Rp_*$ of
$\varepsilon_p\otimes1$ ($\varepsilon_p$ the counit) read through the
monoidality of $Lp^*$, and $\operatorname{Ex}_*$ is the mate of
$L\bar g'^*Lp^*\cong Lp'^*Lg^*$ under $Lp^*\dashv Rp_*$ and
$Lp'^*\dashv Rp'_*$; transposing the two composites
$Lg^*(Rp_*M\otimes^LL)\to Rp'_*(L\bar g'^*M\otimes^LLp'^*Lg^*L)$ under
$Lp'^*\dashv Rp'_*$ gives, by the pasting compatibility of mates
([sk-lem-sf-mate]) and the triangle identity for $p$, one and the same map
$Lp'^*Lg^*(Rp_*M\otimes^LL)\to L\bar g'^*M\otimes^LLp'^*Lg^*L$, namely
$L\bar g'^*\varepsilon_p\otimes1$ read through the monoidality isomorphisms;
so the two composites are mates of the same composite. (The same computation
with an arbitrary $L'\in\Dctf(Y',\Lambda)$ in place of $Lg^*L$ identifies
$\operatorname{PF}_{p'}\circ(\operatorname{Ex}_*\otimes1):
Lg^*Rp_*M\otimes^LL'\to Rp'_*(L\bar g'^*M\otimes^LLp'^*L')$ with the
transpose of $L\bar g'^*\varepsilon_p\otimes1$; this is the form used for the
symmetry of the relative product in [sk-thm-sf-kunneth-relative].) The
last clause is [sk-prop-sf-pf-reduction], [sk-thm-sf-pf-field] and
[sk-thm-sf-pf-proetale].

Uses: `\Cref{lem-sf-mate}`, `\Cref{sk-prop-sf-comp-proper}`, `\Cref{prop-sf-pf-reduction}`, `\Cref{thm-sf-pf-field}`, `\Cref{thm-sf-pf-finite}`, `\Cref{thm-sf-pf-proetale}`
