+++
id = "lem-sc-p1-twist-sections"
kind = "lemma"
title = "Sections of the twists"
order = 637
uses = ["def-sc-p1-standard"]
+++
Let $k$ be a field, $d\in\mathbf Z$, and let $\mathcal O(d)$
be a twisted structure sheaf as in [def-sc-p1-standard], with
generating section $g_0$ over $U_0=\Spec k[t]$ and generating
section $g_1$ over $U_1=\Spec k[s]$, $s=1/t$. Then the
sections of $\mathcal O(d)$ over $\mathbf P^1_k$ are exactly the
pairs $(p,q)\in k[t]\times k[s]$ with

$$
p(t)=t^{d}q(1/t)\qquad\text{in }k[t,t^{-1}],
$$

$p$ being the coefficient of $g_0$ over $U_0$ and $q$ the
coefficient of $g_1$ over $U_1$.

## Proof

A section of $\mathcal O(d)$ is a pair of sections $p\,g_0$ over
$U_0$ and $q\,g_1$ over $U_1$, with $p\in k[t]$ and
$q\in k[s]$, that agree over
$U_{01}=\Spec k[t,t^{-1}]$, i.e. $p\,g_0=q\,g_1$ in $\Gamma(U_{01},\mathcal O(d))$. By the
glueing relation $g_0=t^{-d}g_1$ of
[def-sc-p1-standard] this is $p\,t^{-d}=q$, equivalently
$p=t^{d}q$; substituting $s=1/t$ gives
$p(t)=t^{d}q(1/t)$.
