+++
id = "sk-prop-sf-comp-proper"
kind = "section"
title = "Proper coincidence"
order = 1875
uses = ["sk-def-sf-exchanges", "sk-prop-sf-cbc", "sk-prop-sf-comp-coherence", "sk-thm-properbasechange"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar"]
+++
*Proposition (sketch).*

Let $f:X\to Y$ be proper. Then $(\operatorname{id}_X,f)$ is an object of
$\operatorname{Comp}(f)$, and the resulting canonical identification

$$
Rf_!\ \xrightarrow{\ \sim\ }\ Rf_*
$$

is independent of the compactification. Under it the exchange
$\operatorname{Ex}_!$ of [sk-def-sf-exchanges] is the proper-base-change
exchange $\operatorname{Ex}_*$; consequently [sk-prop-sf-cbc] specializes to
[sk-thm-properbasechange] for proper $f$, and the two clauses of
[sk-thm-sf-package] (2) agree on proper morphisms.

## Proof

The identity is a quasi-compact open immersion and $f$ is proper, so
$(\operatorname{id}_X,f)$ is an object of $\operatorname{Comp}(f)$ in the sense
of [sk-prop-nagata-sketch-comp-category]; on this model
$Rf_!=Rf_*\circ\operatorname{id}_!=Rf_*$. By
[sk-prop-sf-comp-coherence] this agrees with the value at any other
compactification. For $j=\operatorname{id}$ the extension-by-zero
identification entering the construction of $\operatorname{Ex}_!$ in
[sk-def-sf-exchanges] is the identity, so $\operatorname{Ex}_!$ reduces to
the exchange map $\operatorname{Ex}_*$ attached to the proper $f$, which is the
one appearing in [sk-thm-properbasechange].

Uses: `\Cref{sk-def-sf-exchanges}`, `\Cref{sk-prop-sf-cbc}`, `\Cref{sk-prop-sf-comp-coherence}`, `\Cref{sk-thm-properbasechange}`
