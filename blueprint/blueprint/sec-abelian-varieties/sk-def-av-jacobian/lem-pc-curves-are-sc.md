+++
id = "lem-pc-curves-are-sc"
kind = "lemma"
title = "Curves in the sense of file 06"
order = 455
uses = ["def-pc-curve", "def-pc-dimension", "def-pc-smooth-projective-curve", "def-sc-curves"]
+++
Let $k$ be an algebraically closed field and let $X$ be a
smooth projective curve over
$k$. Then $X$ is a smooth *connected curve over $k$* in the sense of
[def-sc-curves]: $X$ is nonempty, connected, separated, of finite type over
$k$ and of dimension one, and smooth over $k$.

## Proof

By [def-pc-smooth-projective-curve] $X$ is a
curve over $k$, hence a
variety: integral, with
$X\to\operatorname{Spec}(k)$ separated and of finite type ([def-pc-curve]); in
particular $X$ is nonempty, connected (being irreducible), separated,
of finite type and, being a
curve, of dimension $1$. Its structure morphism is smooth by hypothesis,
and
[def-sc-curves] requires exactly: nonempty, connected, separated scheme of
finite type of dimension one, smooth over $k$. This proves the
claim.
