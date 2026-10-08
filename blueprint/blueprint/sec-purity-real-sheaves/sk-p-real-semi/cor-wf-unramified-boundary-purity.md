+++
id = "cor-wf-unramified-boundary-purity"
kind = "theorem"
title = "Purity at an unramified boundary point"
order = 2656
tags = ["latex:corollary"]
uses = ["d-real-setup", "def-weil-frobenius-module-weights", "def-weil-punctual-weights", "lem-a1-lisse-middle-extension", "lem-wf-boundary-semicontinuity", "lem-wf-boundary-stalk-invariants"]
+++
Let $\mathcal F$ be lisse and $\iota$-pure of weight $w$ on a
punctured smooth curve, and let $x$ be the missing point. If the
local inertia action at $x$ is trivial, then the extended stalk
$(j_*\mathcal F)_{\bar x}$ is pure of weight $w$.

Consequently, if $j:U_0\hookrightarrow C_0$ is a dense open in a curve
in the sense of [d-real-setup] and $\mathcal G$ is a lisse Weil sheaf
on $C_0$ whose restriction $j^*\mathcal G$ is punctually $\iota$-pure
of weight $w$ on $U_0$, then $\mathcal G$ is punctually $\iota$-pure
of weight $w$ on all of $C_0$.

## Proof

By [lem-wf-boundary-stalk-invariants], trivial inertia identifies
the boundary stalk with the full local representation.
Apply [lem-wf-boundary-semicontinuity] on an affine neighbourhood
of the missing point to $\mathcal F$, and then to
$\mathcal F^\vee$. The latter is punctually pure of weight $-w$,
since duality inverts local eigenvalues, by
[def-weil-punctual-weights].
Because inertia is trivial, the extended dual stalk is the linear dual
of the extended stalk. The two bounds are therefore
$|\iota(\alpha)|^2\leq q_x^w$ and
$|\iota(\alpha^{-1})|^2\leq q_x^{-w}$.
Together they give equality, namely purity in
[def-weil-frobenius-module-weights].

For the consequence, the closed points of $U_0$ are covered by the
hypothesis; let $x\in C_0\setminus U_0$ (a finite set, $U_0$ being
dense in the curve $C_0$). Since $\mathcal G$ is lisse on $C_0$, its
geometric generic stalk is a representation of the fundamental group
of $C_0$, so the local inertia $I_x$ acts trivially on
$(j^*\mathcal G)_{\bar\eta}$. Removing the other points of
$C_0\setminus U_0$ from $C_0$ does not change the stalk of
$j_*j^*\mathcal G$ at $\bar x$, so the first part, applied to the lisse
sheaf $j^*\mathcal G$, pure of weight $w$, shows that
$(j_*j^*\mathcal G)_{\bar x}$ is pure of weight $w$. By
[lem-a1-lisse-middle-extension] the adjunction
$\mathcal G\to j_*j^*\mathcal G$ is an isomorphism; being a morphism of
Weil sheaves, it identifies $\mathcal G_{\bar x}$ with
$(j_*j^*\mathcal G)_{\bar x}$ compatibly with $F_x$. Hence every
eigenvalue of $F_x$ on $\mathcal G_{\bar x}$ has $\iota$-weight $w$,
which is punctual purity of weight $w$ at $x$ in
[def-weil-punctual-weights].
