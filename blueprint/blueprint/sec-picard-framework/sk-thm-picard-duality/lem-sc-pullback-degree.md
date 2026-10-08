+++
id = "lem-sc-pullback-degree"
kind = "lemma"
title = "Degree of pullbacks of divisors"
order = 700
uses = ["def-sc-curves", "def-sc-divisor", "lem-sc-point-cartier"]
+++
Let $\pi:C\to C'$ be a finite flat morphism of proper smooth
connected curves over an algebraically closed field
$k$, of degree $d=[k(C):k(C')]$, and let
$D'=\sum_Pn_P[P']$ be a divisor on $C'$. Then

$$
\deg(\pi^*D')=d\cdot\deg D',
$$

where $\pi^*D'$ is the pullback divisor
$\sum_{P'}n_{P'}\sum_{\pi(P)=P'}v_P(t_{P'})[P]$ ($t_{P'}$ a local
equation of $P'$); in particular
$\deg\pi^*[P']=d$ for every closed point $P'$.

## Proof

Since $\pi$ is finite flat, $\pi_*\mathcal O_C$ is locally free
of rank $d$, and the fibre over $P'$ is
$\operatorname{Spec}((\pi_*\mathcal O_C)\otimes k(P'))$, a
$k$-algebra of dimension $d$ (all residue fields are $k$
because $k$ is algebraically closed), whose length is

$$
\sum_{\pi(P)=P'}v_P(t_{P'})\,[k(P):k]
=\sum_{\pi(P)=P'}v_P(t_{P'}),
$$

as $\mathcal O_{C,P}$ is a discrete valuation ring with residue
field $k(P)$ ([lem-sc-point-cartier]). Hence
$\deg\pi^*[P']=\sum_{\pi(P)=P'}v_P(t_{P'})=d$, and the general
case follows by linearity.
