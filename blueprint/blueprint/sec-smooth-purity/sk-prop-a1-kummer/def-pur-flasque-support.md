+++
id = "def-pur-flasque-support"
kind = "definition"
title = "Supported sections and flasque objects"
order = 1929
uses = ["def-pur-conventions", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Let $s:Z\hookrightarrow X$ be a
closed immersion, and
let $j:U\hookrightarrow X$ be its open complement. Work with
$\Lambda$-module sheaves on the
small pro-etale sites in the
finite coefficient conventions.
For a sheaf $M$ define its subsheaf of sections supported on $Z$ by

$$
\mathcal G_ZM=\ker(M\longrightarrow j_*j^*M).
$$

Regarded as a sheaf on $Z$, it is
$s^!M:=s^{-1}\mathcal G_ZM$; thus $s_*s^!M=\mathcal G_ZM$.
Here $s^!$ is a left exact functor, distinct from the ordinary
restriction $s^{-1}$. A sheaf $I$ is *flasque for this pair*
if $I\to j_*j^*I$ is an epimorphism.
