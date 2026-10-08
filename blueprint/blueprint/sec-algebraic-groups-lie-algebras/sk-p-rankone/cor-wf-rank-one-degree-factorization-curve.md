+++
id = "cor-wf-rank-one-degree-factorization-curve"
kind = "theorem"
title = "Finite-order part times a degree character"
order = 2533
tags = ["latex:corollary"]
uses = ["d-ab-rankone", "d-monodromy", "def-weil-pbc-scheme-conventions", "def-wf-weil-group", "lem-wf-weil-group-exact-sequence"]
+++
Let $U_0/\mathbf F_q$ be normal, geometrically connected,
separated and of finite type, pure of dimension one; put
$U=U_0\times_{\mathbf F_q}\overline{\mathbf F}_q$ and
$\Pi=\pi_1(U,\bar u)$; let $\ell\nmid q$, let $E/\mathbf Q_\ell$ be finite, and let
$\chi:\hyperref[def-wf-weil-group]{W(U_0,\bar u)}\to E^\times$ be a
continuous character with finite geometric image $\chi(\Pi)$. Choose $s$ with $\deg(s)=1$ and put
$c=\chi(s)$. Then $(W(U_0,\bar u),\deg,s)$ is a degree datum in the sense
of [d-monodromy] with $P=\Pi$, and for it the function
$\varepsilon=\chi_{\mathrm{fin}}$ of [d-ab-rankone] (with $\gamma=s$ and
$z=c$), namely $\varepsilon(w)=\chi(w)c^{-\deg(w)}$, is a finite-order
character $\varepsilon:W(U_0,\bar u)\to E^\times$ with
$\varepsilon(s)=1$, $\varepsilon(W(U_0,\bar u))=\chi(\Pi)$, and

$$
\chi(w)=\varepsilon(w)c^{\deg(w)}
\qquad(w\in W(U_0,\bar u)).
$$

The scheme and Weil-group conventions are those of
[def-weil-pbc-scheme-conventions], [def-wf-weil-group].

## Proof

The degree homomorphism $\deg:W(U_0,\bar u)\to\mathbf Z$ of
[def-wf-weil-group] is surjective with kernel $\Pi$ by
[lem-wf-weil-group-exact-sequence], and $\deg(s)=1$, so
$(W(U_0,\bar u),\deg,s)$ is a degree datum of [d-monodromy] with
$P=\Pi$. In the notation of [d-ab-rankone], $z=\chi(s)=c$,
$\chi_z(w)=c^{\deg(w)}$ and $\varepsilon=\chi_{\mathrm{fin}}$.
Since $\deg$ is additive, $\chi_z$ is a character, and since
$E^\times$ is abelian, the quotient $\varepsilon=\chi\chi_z^{-1}$ is again a
character. If $n=\deg(w)$, then $g=ws^{-n}$ has degree zero and hence
lies in $\Pi$; multiplicativity gives

$$
\varepsilon(w)=\chi(g)\chi(s)^nc^{-n}=\chi(g)\in\chi(\Pi),
$$

and conversely $\varepsilon(g)=\chi(g)$ for $g\in\Pi$, so
$\varepsilon(W(U_0,\bar u))=\chi(\Pi)$, and $\varepsilon(s)=\chi(s)c^{-1}=1$.
The group $\chi(\Pi)$ is finite by hypothesis. Thus the image of
$\varepsilon$ is finite, so $\varepsilon$ is of finite order, and the
displayed factorization $\chi=\varepsilon\chi_z$ holds by the definition of
$\chi_{\mathrm{fin}}$ in [d-ab-rankone].
