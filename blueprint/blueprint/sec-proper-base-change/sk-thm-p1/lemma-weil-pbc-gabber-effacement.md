+++
id = "lemma-weil-pbc-gabber-effacement"
kind = "lemma"
title = "Affine Gabber effacement"
order = 1133
uses = ["lemma-weil-pbc-constructible-approximation", "lemma-weil-pbc-constructible-finite-pushforward", "lemma-weil-pbc-finite-cover-killing", "lemma-weil-pbc-pushout-monicity"]
+++
For an affine henselian pair $(T,T_0)$ and a torsion sheaf $F$ on $T_{\mathrm{et}}$,
every class $c\in H^q(T_0,F_0)$ with $q>0$ admits a monomorphism
$F\hookrightarrow F'$ such that the image of $c$ in $H^q(T_0,F'_0)$ is zero.

## Proof

Apply constructible approximation to obtain $C\hookrightarrow F$ through
which $c$ factors, and use finite-pushforward reduction to choose

$$
C\hookrightarrow D_0=\bigoplus_{i=1}^r(h_i)_*\underline{M_i}.
$$

Let $c_i$ be the image of $c$ in
$H^q(T_0,(h_i)_*\underline{M_i}|_{T_0})$. Finite direct-image exactness
identifies $c_i$ with a class on the closed fibre of $h_i$. Apply finite-cover
killing to each $c_i$ and take the fibre product of the resulting finite
covers over $T$; after replacing by one finite-presentation stage, call the
common finite cover $h:V\to T$. Every component of $h_0^*c$ is zero.
The composite unit

$$
C\hookrightarrow D_0\longrightarrow h_*h^*D_0=:D
$$

is monic by the finite stalk product formula. Form the pushout square

$$
\begin{CD}
C @>>> D\\
@VVV @VVV\\
F @>>> F':=F\amalg_C D.
\end{CD}
$$

Pushout monicity makes $F\to F'$ injective. The image of $c$ in
$H^q(T_0,D_0)$ is carried to zero in $H^q(T_0,D)$ because its pullback to
$V_0$ is zero and $h_*$ is exact. The pushout square therefore carries $c$
to zero in $H^q(T_0,F'_0)$. This displays both the common dominating cover
and the null-homotopy square and closes Tag `09ZE`'s effacement step.
