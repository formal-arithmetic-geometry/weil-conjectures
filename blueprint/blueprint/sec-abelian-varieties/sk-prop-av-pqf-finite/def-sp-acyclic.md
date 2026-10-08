+++
id = "def-sp-acyclic"
kind = "definition"
title = "Acyclic objects for a left exact functor"
order = 503
uses = ["def-sp-left-exact-additive"]
+++
Let $v:\mathcal A\to\mathcal B$ be a left exact additive
[def-sp-left-exact-additive] functor. An object $X\in\mathcal A$ is
$v$-*acyclic* if $R^nv(X)=0$ for every $n>0$, where $R^nv$ is the right
derived functor [def-sp-left-exact-additive] of $v$. In the sheaf case
relevant to the proper-base-change chapter: for the etale direct image
$v=f_*$, $f_*$-acyclic means $R^qf_*(X)=0$ for $q>0$.
