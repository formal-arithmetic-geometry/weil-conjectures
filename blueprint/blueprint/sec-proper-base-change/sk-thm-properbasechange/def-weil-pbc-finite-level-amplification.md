+++
id = "def-weil-pbc-finite-level-amplification"
kind = "definition"
title = "Finite-level amplification condition"
order = 1350
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-cartesian-square", "def-weil-pbc-constructible-direct-image-finiteness", "def-weil-pbc-derived-categories", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-proetale-operations"]
+++
For a cartesian square [def-weil-pbc-cartesian-square] $\square$ with
$\Lambda$-coefficient data as in the adic coefficient datum, write
$\mathrm{AMP}(\square;c)$ if, for every $n\geq1$, with $P_n=A/I^n$ and
$\Lambda=P_n$:

1. the finite-level direct images satisfy the finiteness conditions
   [def-weil-pbc-constructible-direct-image-finiteness]
   $\mathrm{FIN}(f,P_n;c)$ and $\mathrm{FIN}(f',P_n;c)$;
2. the finite-level pullbacks $Lg_n^*,Lg_n'^*$ restrict to exact
   triangulated functors
   $$
    \begin{aligned}
     Lg_n^* &:D^b_c(Y_{\Proet},P_n)\longrightarrow
              D^b_c(Y'_{\Proet},P_n),\\
     Lg_n'^* &:D^b_c(X_{\Proet},P_n)\longrightarrow
               D^b_c(X'_{\Proet},P_n)
    \end{aligned}
   $$
   which carry objects with cohomology in $[a,b]$ into objects with
   cohomology in $[a,b]$.

Here $D^b_c(Z_{\Proet},P_n)^{[a,b]}$ denotes the full class of objects of
$D^b_c(Z_{\Proet},P_n)$ whose cohomology vanishes outside $[a,b]$. That the
conditions (i)--(ii) imply the amplitude containments for
$Rf_*,Rf'_*,Lg_n^*,Lg_n'^*$ is recorded with the other properties of this
predicate.

*Source note:* no Stacks Project entry states this predicate: its first
clause is the finiteness condition of the blueprint, whose etale inputs are
Lemma 59.92.2 ([Tag 095U](https://stacks.math.columbia.edu/tag/095U),
amplitude) and Theorem 63.14.5 ([Tag
0GL0](https://stacks.math.columbia.edu/tag/0GL0), constructibility),
transferred to the pro-etale sites below, and its second clause is the
restriction of the finite-level pullbacks to bounded constructibles, for
which the nearest entries are Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)), Proposition 61.29.7 ([Tag
09C7](https://stacks.math.columbia.edu/tag/09C7)) and the pullback
compatibility of Lemmas 61.27.2 and 61.27.4 ([Tag
09AK](https://stacks.math.columbia.edu/tag/09AK), [Tag
09AL](https://stacks.math.columbia.edu/tag/09AL)); the blueprint adds the
predicate that lets the amplification hypotheses be stated for one square
and one level $n$.
