+++
id = "lem-exc-closed-amplitude"
kind = "lemma"
title = "Closed-support amplitude"
order = 1911
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-exc-closed-ambient", "lem-exc-closed-support-triangle", "thm-constructible-serre"]
+++
Let $i:Z\hookrightarrow T$ be a
closed immersion, with open
complement $j$, and let $A$ be finite. Suppose that
direct image on the etale sites
satisfies $R^qj_*M=0$ for every module sheaf $M$ and every
$q>c$, where $c\geq0$. Then, in the
ordinary derived categories,

$$
Ri^!D^{[a,b]}(T_{\mathrm{et}},A)
\subseteq D^{[a,b+c+1]}(Z_{\mathrm{et}},A).
$$

If additionally every $R^qj_*F$ is
constructible for
constructible $F$, the same assertion holds with constructible
cohomology on both sides.

## Proof

The finite hypercohomology spectral sequence
$R^pj_*\mathcal H^q(j^*K)\Rightarrow \mathcal H^{p+q}(Rj_*j^*K)$ has $0\leq p\leq c$ and
$a\leq q\leq b$. Its abutment is therefore supported in
$[a,b+c]$. Apply the cohomology long exact sequence to the triangle
of [lem-exc-closed-support-triangle], for the right adjoint
$Ri^!$ of [lem-exc-closed-ambient]. Since its first term is
$\operatorname{Cone}(K\to Rj_*j^*K)[-1]$, its possible degrees lie
in $[a,b+c+1]$. The exact and faithful $i_*$ detects precisely
the same bounds on $Ri^!K$.

Under the additional direct-image finiteness condition, the spectral
sequence has constructible entries and a finite filtration in each
degree. The Serre closure of
[thm-constructible-serre] makes its abutment constructible
in the sense of [def-weil-pbc-constructible-complexes].
The long exact sequence then makes the cohomology of $i_*Ri^!K$
constructible. Apply the exact $i^*$, which pulls a finite
constructible stratification back to one on $Z$.
