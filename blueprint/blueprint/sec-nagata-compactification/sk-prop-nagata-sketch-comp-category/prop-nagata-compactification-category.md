+++
id = "prop-nagata-compactification-category"
kind = "theorem"
title = "The compactification category is nonempty, cofiltered, and base-changes"
order = 414
tags = ["latex:proposition"]
uses = ["def-nagata-compactification", "def-nagata-compactification-base-change", "def-nagata-dense-compactification", "def-nagata-immersion-compactification", "def-nagata-scheme-theoretic-image", "lemma-nagata-compactification-base-change", "lemma-nagata-dense-flat-pullback", "lemma-nagata-immersion-into-proper", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-proper-to-separated-target", "lemma-nagata-scheme-image-universal", "thm-nagata-compactification"]
+++
Let $S$ be a quasi-compact, quasi-separated scheme and let $f\colon X\to S$
be separated and of finite type. Let $\operatorname{Comp}(f)$ be the
category whose objects are the compactifications
$c=(X\xrightarrow{j}\overline X\xrightarrow{\bar f}S)$ of $f$ in the sense of
[def-nagata-compactification] ($j$ a quasi-compact open immersion, $\bar f$
proper, $\bar f\circ j=f$; scheme-theoretic density of $j$ is *not*
required), and whose morphisms $u\colon c_1\to c_2$, the *refinements*, are
the proper $S$-morphisms $u\colon\overline X_1\to\overline X_2$ with
$u\circ j_1=j_2$. Then:

1. $\operatorname{Comp}(f)$ is nonempty.
1. **(i)** Any two objects $c_1,c_2$ admit a common refinement
$c\to c_1$, $c\to c_2$; hence every finite family of objects admits one.
One such $c$ is the scheme-theoretic image $\overline X$ of
$(j_1,j_2)\colon X\to\overline X_1\times_S\overline X_2$, and for it
$j$ is scheme-theoretically dense.
1. **(ii)** Any two parallel refinements $u,v\colon c_1\to c_2$ are
equalized by a further refinement $c'\to c_1$.

In particular $\operatorname{Comp}(f)$ is cofiltered. Moreover it is
compatible with base change: let $g\colon S'\to S$ be any morphism and
$f'\colon X'=X\times_SS'\to S'$ the base change of $f$.

1. For every object $c$ of $\operatorname{Comp}(f)$, its base change
$c_{S'}=(X'\xrightarrow{j'}\overline X\times_SS'\to S')$ is an object of
$\operatorname{Comp}(f')$, and for every refinement $u\colon c_1\to c_2$ the
base change $u'=u\times_SS'$ is a refinement $c_{1,S'}\to c_{2,S'}$,
functorially in $u$. Consequently base change carries a common refinement
$c\to c_1,\ c\to c_2$ to a common refinement
$c_{S'}\to c_{1,S'},\ c_{S'}\to c_{2,S'}$, and equalizing refinements to
equalizing refinements.
1. If $c$ is the common refinement constructed in (i) from $c_1,c_2$ and
$c'$ the one constructed from $c_{1,S'},c_{2,S'}$, then the ambient scheme
of $c'$ is a closed subscheme of that of $c_{S'}$, and the inclusion is a
refinement $c'\to c_{S'}$ over the two projections. If $g$ is flat, this
inclusion is an isomorphism, i.e. the construction of (i) commutes with
flat base change.

Scheme-theoretic density is not preserved by arbitrary base change, which
is why it is not part of the objects: $c_{S'}$ need not be
scheme-theoretically dense ([def-nagata-dense-compactification]) even if
$c$ is, but it always is when $g$ is flat.

## Proof

*Category.* Identities are refinements, and a composite of two proper
$S$-morphisms compatible with the open immersions is again one, so
$\operatorname{Comp}(f)$ is a category. Note that any $S$-morphism
$u\colon\overline X_1\to\overline X_2$ with $u\circ j_1=j_2$ is automatically
proper by [lemma-nagata-proper-to-separated-target], since $\overline X_1\to S$
is proper and $\overline X_2\to S$ is separated.

*Nonemptiness.* Since $S$ is quasi-compact and quasi-separated and $f$ is
separated of finite type, [thm-nagata-compactification] provides a
compactification of $f$ in the sense of [def-nagata-compactification], i.e.
an object of $\operatorname{Comp}(f)$.

*(i).* Put $Y=\overline X_1\times_S\overline X_2$ and
$a=(j_1,j_2)\colon X\to Y$. The structure map $Y\to S$ is proper: it is the
base change of $\bar f_2$ along $\bar f_1$ followed by $\bar f_1$, and proper
maps are stable under base change and composition. The map $a$ is a
quasi-compact immersion: it factors as

$$
X\xrightarrow{(\mathrm{id},j_2)}X\times_S\overline X_2
\xrightarrow{j_1\times\mathrm{id}}\overline X_1\times_S\overline X_2 ,
$$

where the first map is the graph of $j_2$, a closed immersion because
$\overline X_2\to S$ is separated, and the second is the base change of the
quasi-compact open immersion $j_1$, hence a quasi-compact open immersion.
Moreover $a$ lies over $S$, the composite $X\to Y\to S$ being $f$.
Hence the factorization $\mathsf C(a)$ of [def-nagata-immersion-compactification],

$$
X\xrightarrow{a^{\mathrm{im}}}\overline X=\operatorname{SIm}(a)
\hookrightarrow Y\longrightarrow S ,
$$

with $\operatorname{SIm}(a)$ the scheme-theoretic image of
[def-nagata-scheme-theoretic-image], is a compactification
$c=(j,\bar c)$ of $f$ by [lemma-nagata-immersion-into-proper], where
$j=a^{\mathrm{im}}$; by [lemma-nagata-immersion-open-in-scheme-image], $j$
is moreover scheme-theoretically dense. Let
$p_i\colon\overline X\hookrightarrow Y\to\overline X_i$ be the restricted
projections. They are $S$-morphisms with
$p_i\circ j=\mathrm{pr}_i\circ a=j_i$, and they are proper by
[lemma-nagata-proper-to-separated-target] since $\overline X\to S$ is proper
and $\overline X_i\to S$ is separated. So $p_i\colon c\to c_i$ are
refinements. For a family $c_1,\dots,c_n$ with $n\geq3$, take a common
refinement $c''$ of $c_1,\dots,c_{n-1}$ by induction and a common refinement
of $c''$ and $c_n$; composing refinements gives the claim.

*(ii).* Let $u,v\colon c_1\to c_2$ be parallel refinements, and let
$\overline X'\subseteq\overline X_1$ be their equalizer, i.e. the pullback of
the diagonal $\Delta\colon\overline X_2\to\overline X_2\times_S\overline X_2$
along $(u,v)\colon\overline X_1\to\overline X_2\times_S\overline X_2$. Since
$\overline X_2\to S$ is separated, $\Delta$ is a closed immersion, so
$i\colon\overline X'\hookrightarrow\overline X_1$ is a closed immersion and
$\overline X'\to\overline X_1\xrightarrow{\bar f_1}S$ is proper. Because
$u\circ j_1=j_2=v\circ j_1$, the universal property of the pullback gives
$j'\colon X\to\overline X'$ with $i\circ j'=j_1$. This $j'$ is a
quasi-compact open immersion: the closed subscheme
$\overline X'\times_{\overline X_1}X$ of $X$ receives the section induced by
$j'$, so it is all of $X$; hence
$X\cong\overline X'\times_{\overline X_1}X$ and $j'$ is the base change of
$j_1$ along $i$. Thus $c'=(j',\bar f_1\circ i)$ is an object of
$\operatorname{Comp}(f)$, the closed immersion $i$ (which is proper) is a
refinement $c'\to c_1$, and $u\circ i=v\circ i$ by construction.

A nonempty category in which any two objects have a common refinement and
any two parallel morphisms are equalized by a further morphism is cofiltered
by definition, so (i), (ii) and nonemptiness give the cofilteredness.

*Base change, first part.* By [lemma-nagata-compactification-base-change],
the construction $c_{S'}$ of [def-nagata-compactification-base-change] is a
compactification of $f'$, i.e. an object of $\operatorname{Comp}(f')$. For
a refinement $u\colon c_1\to c_2$, the map
$u'=u\times_SS'\colon\overline X_1\times_SS'\to\overline X_2\times_SS'$ is an
$S'$-morphism, it is proper as a base change of a proper morphism, and
$u'\circ j_1'=(u\circ j_1)\times_SS'=j_2'$ by functoriality of fibre
products. Functoriality $(u\circ w)'=u'\circ w'$ and $\mathrm{id}'=\mathrm{id}$
holds for the same reason; hence commuting triangles and equalities
$u\circ w=v\circ w$ are preserved, which gives the statements on common and
equalizing refinements.

*Base change, second part.* Let $Y'=Y\times_SS'
=\overline X_{1}'\times_{S'}\overline X_{2}'$ with
$\overline X_i'=\overline X_i\times_SS'$, let $q\colon Y'\to Y$ be the
projection, and let $a'=(j_1',j_2')\colon X'\to Y'$, which is the base change
of $a$ along $q$. The ambient scheme of $c_{S'}$ is
$\operatorname{SIm}(a)\times_YY'$, a closed subscheme of $Y'$ through which
$a'$ factors (via $j\times_SS'$). By [lemma-nagata-scheme-image-universal]
applied to $a'$, there is a unique closed immersion
$\operatorname{SIm}(a')\hookrightarrow\operatorname{SIm}(a)\times_YY'$
compatible with the maps to $Y'$ and hence with the maps from $X'$; it is
proper and lies over the two projections to $\overline X_i'$, so it is a
refinement $c'\to c_{S'}$ compatible with the refinements to $c_{i,S'}$.
If $g$ is flat, so is $q$. The morphism $a$ is quasi-compact, and it is
quasi-separated as an immersion; so the flat base change statement in
[lemma-nagata-dense-flat-pullback] gives
$\operatorname{SIm}(a')\cong\operatorname{SIm}(a)\times_YY'$ as closed
subschemes of $Y'$, i.e. the above inclusion is an isomorphism.

*Density.* Density is not stable under arbitrary base change: for
$S=\overline X=\operatorname{Spec}K[t]$ over a field $K$, $X=D(t)$ and $j$ the
inclusion, $c=(j,\mathrm{id})$ is scheme-theoretically dense, but its base
change to $S'=\operatorname{Spec}K$ ($t=0$) has $X'=\varnothing$ and
$\overline X'=\operatorname{Spec}K$, so it is not. For flat $g$, the
dense-pullback statement in [lemma-nagata-dense-flat-pullback], applied to
$j$ (quasi-compact, and quasi-separated as an immersion) and the flat map
$\overline X\times_SS'\to\overline X$, shows that $c_{S'}$ is again
scheme-theoretically dense whenever $c$ is. This is why
$\operatorname{Comp}(f)$ uses the notion of [def-nagata-compactification]
without density.
