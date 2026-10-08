+++
id = "def-galois-fibre-functor"
kind = "definition"
title = "The fibre functor"
order = 962
uses = ["def-galois-categories"]
+++
In the situation of [def-galois-categories], the *fibre functor*
is

$$
F_{\bar y}:\mathrm{FLC}(Y)\longrightarrow(\text{finite sets}),\qquad
\mathcal F\longmapsto\mathcal F_{\bar y},
$$

and on $\mathrm{F\acute Et}(Y)$ the notation
$P\mapsto|P_{\bar y}|$ of [def-galois-categories] is used; that
the two functors correspond under the identification of
[thm-galois-lc-etale] is part of that theorem. Its
*automorphism group*

$$
\pi_1(Y,\bar y)=\operatorname{Aut}(F_{\bar y})
$$

is the group of natural automorphisms of $F_{\bar y}$, embedded into
$\prod_{\mathcal F}\operatorname{Aut}(F_{\bar y}(\mathcal F))$ by
evaluation and endowed with the topology induced from the product of the
discrete topologies; this is the *etale fundamental group* of $Y$ at
$\bar y$. A $\pi_1(Y,\bar y)$-set is a finite set with a continuous
action of $\pi_1(Y,\bar y)$, and such sets form the category
$\pi_1(Y,\bar y)\text{-}\mathbf{Set}$.
