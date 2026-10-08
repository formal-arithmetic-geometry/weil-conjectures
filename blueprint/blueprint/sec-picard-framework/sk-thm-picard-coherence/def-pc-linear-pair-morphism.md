+++
id = "def-pc-linear-pair-morphism"
kind = "definition"
title = "The morphism determined by two linear forms"
order = 649
uses = ["def-pc-proj", "def-pc-standard-graded-algebra", "def-sc-p1-standard"]
+++
Let $S$ be a standard graded
$k$-algebra, and let $l_0,l_1\in S_1$ satisfy
$D_+(l_0)\cup D_+(l_1)=\operatorname{Proj}(S)$.
The morphism $\pi_{l_0,l_1}:\operatorname{Proj}(S)\to \hyperref[def-sc-p1-standard]{\mathbf P^1_k}$
is obtained on $D_+(l_0)$ from the ring map
$k[t]\to S_{(l_0)}$, $t\mapsto l_1/l_0$, and on $D_+(l_1)$ from
$k[t^{-1}]\to S_{(l_1)}$, $t^{-1}\mapsto l_0/l_1$.
