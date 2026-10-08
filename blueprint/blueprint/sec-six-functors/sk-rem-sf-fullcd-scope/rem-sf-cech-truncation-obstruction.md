+++
id = "rem-sf-cech-truncation-obstruction"
kind = "remark"
title = "The Čech complex of a single weakly contractible covering: what its truncation is missing, and what does not supply it"
order = 2056
uses = ["def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site"]
+++
Let $T$ be a scheme, let $U\to T$ be a nonempty object of the
small pro-étale site $T_{\Proet}$ of
[def-weil-pbc-proetale-site], let $\mathcal F$ be a sheaf of
$A$-modules on $T_{\Proet}$, that is, an object of
[def-weil-pbc-proetale-modules], and let $W\to U$ be a pro-étale
covering whose source is weakly contractible, as supplied by Stacks Project,
Pro-étale Cohomology, Lemma 61.13.5,
[Tag 0F4P](https://stacks.math.columbia.edu/tag/0F4P); let $K$ be the
Čech hypercover of that covering,
$K_n=W^{n+1}=W\times_U\dots\times_UW$, which is a hypercovering by Stacks
Project, Example 25.3.6, [Tag
0GMA](https://stacks.math.columbia.edu/tag/0GMA). The following four facts answer, for this device, the question of what a
bound on the length of a weakly contractible hypercovering can and cannot give.

1. **(i)** *Every term of $K$ is nonempty, so this hypercover cannot be
truncated at all.* Each $W^{n+1}$ contains the diagonal copy of $W$, so no
term is empty and no truncation of $K$ is a hypercovering;
*No hypercovering of a nonempty object has an empty term* shows that this is a property of
hypercoverings and not of this construction, and
*The question of a bounded weakly contractible hypercovering has a negative answer* draws the consequence.
1. **(ii)** *If all fibre products $W^{n+1}$ are weakly contractible, the
Čech complex computes $R\Gamma(U,\mathcal F)$, and its truncation is
legitimate exactly when the vanishing holds.* This is
*Truncating the Čech complex of a single weakly contractible covering needs the vanishing as input*: the complex has a term in every degree,
by (i), and its truncation at $N$ is a quasi-isomorphism if and only if
$H^q(U,\mathcal F)=0$ for every $q>N$. The truncation therefore needs as
input exactly the vanishing it is meant to produce, and no bounded replacement
follows from pro-étale descent.
1. **(iii)** *The weak contractibility of $W$ alone does not give (ii),
and no other recorded cover does either.* The recorded sources say nothing
about the fibre products $W\times_U\dots\times_UW$, so the weak contractibility
of the terms of the Čech hypercover is a second input, distinct from the weak
contractibility of $W$; neither does the stronger cover of Stacks Project,
Pro-étale Cohomology, Proposition 61.11.3,
[Tag 0983](https://stacks.math.columbia.edu/tag/0983) (for an affine $U$;
Lemma 61.13.3, [Tag 098I](https://stacks.math.columbia.edu/tag/098I), in
general), whose members are spectra of w-contractible rings, with Definition
61.11.1, [Tag 0981](https://stacks.math.columbia.edu/tag/0981), and Lemma
61.11.2, [Tag 0982](https://stacks.math.columbia.edu/tag/0982), and are
therefore weakly contractible, supply it: the Čech nerve of any of its
members has the same shape. What Stacks Project, Pro-étale
Cohomology, Lemma 61.14.1,
[Tag 09A1](https://stacks.math.columbia.edu/tag/09A1), supplies instead is a
hypercovering whose terms are weakly contractible by construction, and by
*The question of a bounded weakly contractible hypercovering has a negative answer* that hypercovering is unbounded. The
criterion that is available in place of a length bound is the vanishing of the
coefficient sheaf on the terms, *Vanishing above the degree in which the coefficient sheaf dies on the terms*.
1. **(iv)** *Neither the degeneration of the spectral sequence nor the
compact generation of the derived category bounds the degree.* If all terms are
weakly contractible, the spectral sequence of Stacks Project, Hypercoverings,
Lemma 25.5.3, [Tag 01GY](https://stacks.math.columbia.edu/tag/01GY), for the
Čech hypercover degenerates at $E_2$, and for the constant coefficient
sheaf its remaining row $E_1^{p,0}=\mathcal F(W^{p+1})$ is nonzero in every
degree, its cohomology being $H^p(U,\mathcal F)$ itself; and the compact
generation of the pro-étale derived category, Stacks Project, Pro-étale
Cohomology, Lemma 61.15.1,
[Tag 0F4Q](https://stacks.math.columbia.edu/tag/0F4Q), exhibits generators,
namely the $j_{U!}\mathcal A_U$ at affine weakly contractible $U$, and
contains no bound on degrees.
