+++
id = "def-weil-pbc-bounded-constructible-tower"
kind = "definition"
title = "Uniformly bounded constructible tower"
order = 1250
uses = ["def-weil-pbc-adic-coefficient-datum"]
+++
An adic tower is an object $M_\bullet\in D(\operatorname{Tow}_{A}(T))$
equipped with normalization isomorphisms
$M_{n+1}\otimes^L_{P_{n+1}}P_n\simeq M_n$ satisfying the quotient cocycle of
[def-weil-pbc-adic-coefficient-datum]. It is *uniformly bounded
constructible* if there are integers $d_0\leq d_1$, one finite
stratification $T=\coprod_\alpha T_\alpha$, and, on each stratum, a pro-etale
covering $\{U_{\alpha j}\to T_\alpha\}_j$ with the following datum. For each
$U_{\alpha j}$ there is a bounded complex $L_{\alpha j}$, supported in
$[d_0,d_1]$, whose terms are finite locally constant $A_T|_{U_{\alpha
j}}$-modules and whose reductions have finite lisse cohomology, together with
isomorphisms

$$
 M_n|_{U_{\alpha j}}\xrightarrow{\sim}
 L_{\alpha j}\otimes^L_{A_T}(P_n)_T|_{U_{\alpha j}}
$$

for every $n$. These isomorphisms intertwine the normalization maps of
$M_\bullet$ with the quotient transition maps of the local reduction tower.

The finite-level constructibility of the local models is the notion of Stacks
Project, Section 61.27 (Tag
[09AI](https://stacks.math.columbia.edu/tag/09AI)) and Definition 61.28.1
(Tag [09BT](https://stacks.math.columbia.edu/tag/09BT), Section 61.28, Tag
[09BS](https://stacks.math.columbia.edu/tag/09BS)): the Stacks entries define
constructibility, lissity and adic lissity of a single sheaf $\mathcal
F=\lim\mathcal F/I^n\mathcal F$ for a Noetherian ring $\Lambda$ with an ideal
$I$, the adic lisse case by local isomorphism to $\underline M^\wedge$, and
state no tower-level assertion; the form used here is a uniform tower with
bounded local models and finite lisse reductions.
