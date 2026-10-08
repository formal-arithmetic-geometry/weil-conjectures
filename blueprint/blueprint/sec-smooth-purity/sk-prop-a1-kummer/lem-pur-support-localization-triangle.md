+++
id = "lem-pur-support-localization-triangle"
kind = "theorem"
title = "Localization triangle for the exceptional inverse image"
order = 1933
uses = ["def-pur-flasque-support", "def-pur-support-triangle", "def-pur-triangle-meaning", "def-weil-exceptional-inverse-image", "def-weil-open-closed-recollement", "def-weil-pbc-kinjective-resolutions", "lem-pur-support-exact"]
+++
Let $s:Z\hookrightarrow X$, $j:U\hookrightarrow X$ be the
closed–open pair, and let $K$ be
a bounded below complex of $\Lambda$-module sheaves. The
specified construction gives a
distinguished triangle

$$
s_*Rs^!K\longrightarrow K\longrightarrow Rj_*j^*K
\longrightarrow s_*Rs^!K[1]
$$

in $D(X,\Lambda)$, with $Rs^!$ the
exceptional inverse image
when that adjoint is defined. It has the canonicality, functoriality
and etale base-change compatibility of
the preceding definition.

## Proof

By [lem-pur-support-exact], the three complexes in
[def-pur-support-triangle] form a short exact sequence. Its cone
triangle is distinguished, and the cone-to-quotient quasi-isomorphism
identifies its third term with $j_*j^*I(K)$.

The sheaf functor $s^!$ of [def-pur-flasque-support] is right
adjoint to $s_*$: every map $s_*N\to M$ has image supported on
$Z$, hence factors uniquely through $\mathcal G_ZM$, giving
$\operatorname{Hom}_X(s_*N,M)=\operatorname{Hom}_Z(N,s^!M)$.
Since $s_*$ is exact for a closed immersion, its derived right
adjoint is computed on injective resolutions by $s^!I(K)$, and
uniqueness of right adjoints identifies it with the exceptional
inverse image of [def-weil-exceptional-inverse-image].
The restriction $j^*$ preserves injectives because its left adjoint
$j_!$ is exact by [def-weil-open-closed-recollement].
Thus $j_*j^*I(K)$ computes $Rj_*j^*K$.

The comparison theorem for the resolutions of
[def-weil-pbc-kinjective-resolutions] and the natural kernel and
quotient maps give canonicality and functoriality in the sense of
[def-pur-triangle-meaning]. Finally, along an etale map the site
is localized: the support kernel and the open direct image are
computed on the same objects after restriction. Etale restriction
preserves injectives, since its extension-by-zero left adjoint is
exact. Applying this to the displayed injective model identifies its
derived pullback with the model for the base-changed pair, proving
etale base-change compatibility.
