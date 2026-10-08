+++
id = "lem-fin-finite-boundary-reconstruction"
kind = "lemma"
title = "Recovering constructibility at a finite boundary"
order = 1628
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions", "lem-fin-closed-immersion", "lem-fin-extension-by-zero", "lem-fin-finite-reflects-derived", "lem-fin-proper-bounded-constructible", "lemma-weil-pbc-geometric-stalk-conservative", "prop-constructible-derived-subcategory", "sbc-def-coefficient-conventions", "thm-constructible-serre"]
+++
Let $b:Y\to S$ be proper
between finite-type schemes, with the finite coefficients of
[sbc-def-coefficient-conventions].
Let $a:G\hookrightarrow Y$ be open, with closed complement
$i:Z\hookrightarrow Y$, and assume $bi:Z\to S$ is finite.
For $K\in\hyperref[def-weil-pbc-derived-categories]{D^+(Y,\Lambda)}$,
suppose $a^*K$ and the direct image
$Rb_*K$ belong to their respective
bounded constructible categories.
Then $K\in D^b_c(Y,\Lambda)$.

## Proof

For any sheaf $E$, the sequence

$$
0\to a_!a^*E\to E\to i_*i^*E\to0
$$

is exact on every geometric stalk, hence exact by
[lemma-weil-pbc-geometric-stalk-conservative].
Here $a_!$ is the extension by zero of
[def-weil-pbc-extension-by-zero].
The four functors in this sequence are exact, so applying the
sequence term by term to a representative of $K$ gives a triangle

$$
a_!a^*K\longrightarrow K\longrightarrow i_*i^*K\longrightarrow .
$$

By [lem-fin-extension-by-zero], $a_!a^*K$ is bounded
constructible. Apply $Rb_*$.
Its image is bounded constructible by
[lem-fin-proper-bounded-constructible], as is $Rb_*K$
by assumption. Their cone $R(bi)_*i^*K$ is bounded constructible,
because the bounded constructible complexes form a triangulated
subcategory [prop-constructible-derived-subcategory] (the cohomology
long exact sequence and the weak Serre property
[thm-constructible-serre]).
Since $bi$ is finite, [lem-fin-finite-reflects-derived]
proves $i^*K\in D^b_c(Z,\Lambda)$.
Exact closed direct image
[lem-fin-closed-immersion] gives the same property for
$i_*i^*K$. Return to the displayed triangle: its outer terms are bounded
constructible, so $K$ is by
[prop-constructible-derived-subcategory].
No identification of $i^*Rj_*$ with a lower-dimensional
open direct image occurs.
