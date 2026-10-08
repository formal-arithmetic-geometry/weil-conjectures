+++
id = "sk-p-rankone"
kind = "section"
title = "Rank-one factorization"
order = 2531
uses = ["sk-d-ab-rankone"]
lean = ["SemidirectProduct.eq_finitePart_mul_degreeCharacter", "SemidirectProduct.finitePart_inrOfAddOne", "SemidirectProduct.range_finitePart", "SemidirectProduct.finite_range_finitePart"]
+++
*Proposition (sketch).*

Let $\chi:W\to E^\times$ be a
rank-one character with finite geometric image.
The candidate functions $\chi_z$ and
$\chi_{\mathrm{fin}}$ are characters, and

$$
\chi(w)=\chi_{\mathrm{fin}}(w)z^{\deg(w)}
$$

for every $w\in W$. Moreover,
$\chi_{\mathrm{fin}}(\gamma)=1$ and
$\chi_{\mathrm{fin}}(W)=\chi(P)$, so $\chi_{\mathrm{fin}}$ has
finite image.

## Proof

The degree in [sk-d-ab-rankone] is additive, so
$w\mapsto z^{\deg(w)}$ is a character. Since $E^\times$ is abelian,
its quotient with $\chi$ is again a character. For the unique normal
form $w=u\gamma^n$, multiplicativity gives
$\chi_{\mathrm{fin}}(w)=\chi(u)z^nz^{-n}=\chi(u)$.
Thus its image is exactly the assumed finite set $\chi(P)$.
Its value at $\gamma$ is $1$, and the displayed factorization follows
by cancellation.

Uses: [sk-d-ab-rankone]
