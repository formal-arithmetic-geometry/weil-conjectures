+++
id = "def-kun-cd"
kind = "definition"
title = "Cohomological dimension"
order = 1532
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions"]
+++
For a
quasi-compact
quasi-separated scheme $T$, the torsion etale
*cohomological dimension* $\kuncd(T)$ is the least
$d\in\mathbf Z_{\ge0}$ with $H^q(T_{\Et},F)=0$ for every
torsion etale sheaf $F$ and
every $q>d$; it is $+\infty$ if no such $d$ exists. For a
quasi-compact quasi-separated morphism $f:X\to Y$, $\kuncd(f)$ is
the least $d$ such that $R^qf_*F=0$ for every torsion etale sheaf
$F$ on $X_{\Et}$ and every $q>d$. The equivalent description of this
vanishing by the strict local test schemes over a geometric point of
$Y$, that is, by the corresponding filtered colimits of cohomology
groups over the pointed etale neighbourhoods, is
[lem-kun-cd-stalk-criterion].
