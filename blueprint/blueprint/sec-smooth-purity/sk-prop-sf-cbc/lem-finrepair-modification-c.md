+++
id = "lem-finrepair-modification-c"
kind = "lemma"
title = "Proper modification transfer without an amplitude claim"
order = 1595
uses = ["def-finrepair-property-c", "def-weil-pbc-extension-by-zero", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lem-fin-closed-immersion", "lem-fin-extension-by-zero", "lem-finrepair-modification-extension-zero", "lem-weil-pbc-grothendieck-spectral-sequence", "lemma-weil-pbc-geometric-stalk-conservative", "thm-constructible-serre"]
+++
Let $f:X\to S$ and $\pi:Y\to X$ be proper finite-type morphisms,
and suppose $\pi$ is an isomorphism over the open $U\subset X$.
Let $i:Z=X\setminus U\hookrightarrow X$ have the reduced closed
structure. If $\mathcal C(f\pi)$ and $\mathcal C(fi)$ hold,
then $\mathcal C(f)$ holds, with the conventions of
[def-finrepair-property-c], [def-weil-pbc-scheme-conventions].

## Proof

For a constructible $F$ on $X$, put $G=F|_U$.
The stalk descriptions of
[def-weil-pbc-extension-by-zero], [def-weil-pbc-inverse-image],
with [lemma-weil-pbc-geometric-stalk-conservative], give

$$
0\longrightarrow j_!G\longrightarrow F
\longrightarrow i_*i^*F\longrightarrow0.
$$

With $j':\pi^{-1}(U)\hookrightarrow Y$ and $G'$ the pullback
of $G$, the sheaf $j'_!G'$ is constructible by
[lem-fin-extension-by-zero]. The identity and acyclicity of
[lem-finrepair-modification-extension-zero], combined with
[lem-weil-pbc-grothendieck-spectral-sequence], give

$$
A_q:=R^qf_*j_!G\simeq R^q(f\pi)_*j'_!G'.
$$

These are constructible by $\mathcal C(f\pi)$ in
[def-finrepair-property-c]. The same composition spectral
sequence and the exact closed direct image of
[lem-fin-closed-immersion] identify
$B_q:=R^qf_*i_*i^*F$ with $R^q(fi)_*i^*F$;
these are constructible by $\mathcal C(fi)$.
The long exact sequence yields

$$
0\to\operatorname{coker}(B_{q-1}\to A_q)
\to R^qf_*F\to\ker(B_q\to A_{q+1})\to0,
\qquad B_{-1}=0.
$$

All four sheaves defining the kernel and cokernel are constructible.
The kernel, cokernel, and extension clauses of
[thm-constructible-serre] prove $\mathcal C(f)$.
