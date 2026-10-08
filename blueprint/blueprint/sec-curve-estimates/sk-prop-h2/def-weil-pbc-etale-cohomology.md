+++
id = "def-weil-pbc-etale-cohomology"
kind = "definition"
title = "Etale cohomology of sheaves"
order = 935
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-kinjective-resolutions"]
+++
Let $T$ be a scheme and let $F$ be an etale abelian sheaf on the small etale
site [def-weil-pbc-etale-site] of $T$. The *(etale) cohomology groups* of $F$
are

$$
 H^q(T_{\Et},F)=\mathcal H^q\bigl(\Gamma(T,I^\bullet)\bigr)
 \qquad(q\geq0),
$$

where $F\to I^\bullet$ is a K-injective resolution
[def-weil-pbc-kinjective-resolutions] and $\Gamma(T,-)$ is the functor of
global sections. For $K\in\Dplus(T_{\Et})$, write

$$
 \RGamma(T_{\Et},K)=\Gamma(T,\operatorname{Kinj}(K)),\qquad
 H^q(T_{\Et},K)=\mathcal H^q\bigl(\RGamma(T_{\Et},K)\bigr)
$$

for the derived global sections and the derived cohomology groups.
