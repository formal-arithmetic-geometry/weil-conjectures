+++
id = "lem-kun-095r"
kind = "lemma"
title = "Pushforward of constructible sheaves along finite morphisms"
order = 1774
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "fin4-thm-finite-morphisms-constructible", "lemma-weil-pbc-finite-direct-image-exact", "sbc-def-coefficient-conventions"]
+++
Let $k$ be a field, $X$ and $Y$ schemes of
finite type over $k$,
$f:X\to Y$ a
finite and finitely
presented morphism, and $\Lambda$ a finite ring annihilated by an
integer invertible on $k$, in the sense of
[sbc-def-coefficient-conventions]. If $F$ is a
constructible
$\Lambda$-module sheaf on $X_{\Et}$, then $f_*F$ is constructible
on $Y_{\Et}$, and $R^qf_*F=0$ for every $q>0$.

## Proof

The constructibility of $f_*F$, including that of all higher direct
images, is [fin4-thm-finite-morphisms-constructible] of the smooth-base-change chapter (stated there for the coefficient ring of
[sbc-def-coefficient-conventions], under exactly the hypotheses on
$X$, $Y$ and $\Lambda$ displayed above); the vanishing of the
higher direct images is
[lemma-weil-pbc-finite-direct-image-exact].
