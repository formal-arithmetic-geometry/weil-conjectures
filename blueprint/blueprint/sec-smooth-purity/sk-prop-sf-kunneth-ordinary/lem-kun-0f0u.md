+++
id = "lem-kun-0f0u"
kind = "lemma"
title = "Strict henselization as a limit"
order = 1762
uses = ["def-kun-dimension", "def-kun-separably-closed", "def-weil-pbc-scheme-conventions", "def-weil-pbc-strict-henselization-limit"]
+++
Let $K$ be a field, $X$ a scheme of finite type over $K$, and $x\in X$
a point with $\operatorname{trdeg}_K\kappa(x)=a>0$; put
$d=\kundim_xX$ and $X'=\Spec\bigl(\mathcal O^{\mathrm{sh}}_{X,x}\bigr)$,
the strict henselization of [def-weil-pbc-strict-henselization-limit].
Then there is a separably closed field $L\supseteq K$
([def-kun-separably-closed]) and a presentation

$$
X'=\varprojlim_iX_i
$$

of $X'$ as an inverse limit of affine schemes $X_i$ of finite type over
$L$ with affine transition morphisms and
$\kundim X_i<\kundim X$ for every $i$.
(*Source:* the case of Stacks Project,
[Tag `0F0U`](https://stacks.math.columbia.edu/tag/0F0U) that is
used in this chapter, namely the presentation of the strict henselization as a
limit of smaller-dimensional finite type models. In the Stacks Project the
proof uses Noether normalization, Algebra, Lemma 10.115.5,
[Tag `00OZ`](https://stacks.math.columbia.edu/tag/00OZ)
(available in this manuscript as thm:zl-relative-noether), a linear
change of coordinates putting the image of $x$ at the generic point of the
linear subspace, the description of the strict henselization as the filtered
colimit of the pointed etale neighbourhoods
([def-weil-pbc-strict-henselization-limit]), and the dimension bound for
an algebra which is quasi-finite over a polynomial ring.)

## Proof

This is the recorded classical input named in the statement, the case used here of Stacks Project, Tag [0F0U](https://stacks.math.columbia.edu/tag/0F0U): the strict henselization of a point of positive transcendence degree over the base field is an inverse limit of affine finite type models of strictly smaller dimension. In the Stacks Project the proof uses Noether normalization, Algebra, Lemma 10.115.5 ([Tag 00OZ](https://stacks.math.columbia.edu/tag/00OZ)), available in this manuscript as thm:zl-relative-noether, together with the description of the strict henselization as a filtered colimit of pointed etale neighbourhoods ([def-weil-pbc-strict-henselization-limit]). No separate proof is given.
