+++
id = "def-weil-pbc-constructible-complexes"
kind = "definition"
title = "Constructible finite-coefficient complexes"
order = 1108
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site"]
+++
Let $\Lambda$ be a finite commutative ring. A sheaf of $\Lambda_T$-modules on
the small etale site [def-weil-pbc-etale-site] $T_{\Et}$ is *lisse* if it is
locally constant with finite stalks [def-weil-pbc-etale-sheaves], and
*constructible* if $T$ admits a finite partition by locally closed
constructible subschemes on each of which the restriction is lisse. A complex
$K\in D(T_{\Et},\Lambda)$ is *bounded constructible* if every $\mathcal
H^i(K)$ is constructible and there are integers $a\leq b$ with $\mathcal
H^i(K)=0$ for $i\notin[a,b]$. The corresponding full subcategory
is denoted

$$
 \Dbc(T_{\Et},\Lambda)\subset D(T_{\Et},\Lambda).
$$
