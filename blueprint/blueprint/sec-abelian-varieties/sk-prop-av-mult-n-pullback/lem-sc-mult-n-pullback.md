+++
id = "lem-sc-mult-n-pullback"
kind = "lemma"
title = "Pullback of symmetric modules under multiplication by $n$"
lean = ["AlgebraicGeometry.nonempty_iso_overPullback_npow_id"]
order = 482
uses = ["def-sc-abelian-variety", "def-sc-mult-n", "thm-sc-theorem-of-cube"]
+++
Let $A$ be an abelian variety
over a field $k$, let $\mathcal N$ be an invertible
$\mathcal O_A$-module with
$[-1]^*\mathcal N\cong\mathcal N$, and let $n\geq1$. Then

$$
[n]^*\mathcal N\cong\mathcal N^{\otimes n^2},
$$

where $[n]$ is the multiplication map of
[def-sc-mult-n].

## Proof

*Reference: Stacks Project, Groupoid Schemes, Lemma 39.9.7,
[Tag 0BFF](https://stacks.math.columbia.edu/tag/0BFF).* Pull
the relation of [thm-sc-theorem-of-cube] back along
$x\mapsto(x,x,-x)$: since $m_{123}(x,x,-x)=x$,
$m_1(x,x,-x)=m_2(x,x,-x)=x$, $m_3(x,x,-x)=-x$,
$m_{12}(x,x,-x)=2x$, and
$m_{13}(x,x,-x)=m_{23}(x,x,-x)=0$, one gets
$\mathcal L^{\otimes3}\otimes[-1]^*\mathcal L\cong[2]^*\mathcal L$ for every $\mathcal L$, hence
$[2]^*\mathcal N\cong\mathcal N^{\otimes4}$ for symmetric
$\mathcal N$. Next pull the relation back along
$x\mapsto(x,x,[n-1]x)$: $m_{123}(x,x,[n-1]x)=[n+1]x$,
$m_1=m_2=\mathrm{id}$, $m_3=[n-1]$, $m_{12}=[2]$, and
$m_{13}=m_{23}=[n]$, so

$$
[n+1]^*\mathcal N\otimes\mathcal N^{\otimes2}\otimes
[n-1]^*\mathcal N
\cong[2]^*\mathcal N\otimes[n]^*\mathcal N^{\otimes2}.
$$

By induction on $n$ (the case $n=2$ was just done, and
$n=1$ is the identity), the induction hypothesis
$[m]^*\mathcal N\cong\mathcal N^{\otimes m^2}$ for $m\leq n$
gives

$$
[n+1]^*\mathcal N\cong\mathcal N^{\otimes(4+2n^2-2-(n-1)^2)}
=\mathcal N^{\otimes(n+1)^2},
$$

as required.
