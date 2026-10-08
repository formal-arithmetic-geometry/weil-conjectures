+++
id = "d-ab-rankone"
kind = "definition"
title = "A split cyclic extension and rank-one characters"
order = 2530
uses = ["d-monodromy"]
lean = ["SemidirectProduct.inrOfAddOne", "SemidirectProduct.degreeCharacter", "SemidirectProduct.finitePart"]
+++
Let $(W,\deg,\gamma)$ be a degree datum in the sense of [d-monodromy],
with $P=\ker(\deg)$. Conjugation by $\gamma$ is an automorphism
$\alpha$ of $P$, and $(u,n)\mapsto u\gamma^n$ identifies $W$ with the
split cyclic extension $P\rtimes_\alpha\mathbf Z$, whose multiplication is

$$
(u,n)(v,m)=(u\alpha^n(v),n+m),\qquad
\gamma=(1,1),\qquad \deg(u,n)=n;
$$

conversely, for any group $P$ and automorphism $\alpha$ this formula
defines a degree datum $(P\rtimes_\alpha\mathbf Z,\deg,(1,1))$ with kernel
$P\times\{0\}$. Every element has a unique form $u\gamma^n$ with $u\in P$
and $n=\deg(u\gamma^n)$. For a field $E$, a rank-one character is a homomorphism
$\chi:W\to E^\times$. It has finite geometric image if $\chi(P)$ is
finite, and finite image if $\chi(W)$ is finite. These are distinct
conditions; no topology is needed for the following factorization.
For such a character, set $z=\chi(\gamma)$ and define the functions

$$
\chi_z(w)=z^{\deg(w)},\qquad
\chi_{\mathrm{fin}}(w)=\chi(w)z^{-\deg(w)}\qquad(w\in W),
$$

so that $\chi(w)=\chi_{\mathrm{fin}}(w)\chi_z(w)$ by construction.
def:ab-cyclic-extension;def:ab-finite-character;def:ab-finite-part

Uses: [d-monodromy]
