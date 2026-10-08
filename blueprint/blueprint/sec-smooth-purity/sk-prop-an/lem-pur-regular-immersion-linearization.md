+++
id = "lem-pur-regular-immersion-linearization"
kind = "lemma"
title = "Etale linearization of a regular immersion"
order = 1980
uses = ["def-pur-conventions", "def-pur-regular-immersion", "def-sbc-smooth-morphisms", "def-weil-scheme-morphism-properties", "lem-sc-smooth-regular", "sbc-thm-etale-local-normal-form"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $i:Z\hookrightarrow X$ be a regular
closed immersion of pure codimension $c$, with $X$ smooth over the
perfect field $k$ and $Z$ regular. Then:

1. $Z$ is smooth over $k$
(regularity plus finite type over the perfect field
$k$: the complete local
rings are power-series rings, so the local ring of $Z$ at every point is
regular, and finite type over a perfect field, hence smooth).
1. The pair $(X,Z)$ is etale locally the *linear* pair: for
every $z\in Z$, writing $m$ for the dimension of its smooth component,
there are an etale neighborhood $U\to X$ of $z$, an
etale neighborhood $V\to Z$ of $z$, an etale map
$$
u:U\longrightarrow\mathbf A^{c+m}_k
$$
and an identification $V=u^{-1}(\mathbf A^m_k)$ with
$Z\cap U=V$, $u|_V$ etale, and the ideal of $V$ in $U$ generated
by $x_1,\dots,x_c$.

## Proof

The regular–smooth criterion over the perfect field $k$, as in
[lem-sc-smooth-regular], makes $Z$ smooth. Work first at a
closed point $z$, and on the smooth component of $Z$ containing
it, of dimension $m$. Choose local generators $f_1,\ldots,f_c$
of its ideal, possible by [def-pur-regular-immersion].
For this smooth pair the conormal sequence at $z$ is an exact
sequence of vector spaces

$$
0\to (I/I^2)\otimes k(z)\to\Omega_{X/k}\otimes k(z)
\to\Omega_{Z/k}\otimes k(z)\to0.
$$

The first map sends the classes of $f_i$ to $df_i$.
Choose functions $g_1,\ldots,g_m$ on $Z$ whose differentials
form a basis of the last space, and lift them to functions on $X$.
The differentials $df_i,dg_j$ then form a basis of the middle
space. The coordinate map $(f_1,\ldots,f_c,g_1,\ldots,g_m)$
to $\mathbf A^{c+m}_k$ is etale at $z$, by the differential
criterion for the local coordinates in
[sbc-thm-etale-local-normal-form]. Shrink its source so that
it remains etale and the $f_i$ still generate the ideal of $Z$.
Then its inverse image of $x_1=\cdots=x_c=0$ is exactly $Z$,
and its restriction to $Z$ is etale by base change.
These neighborhoods cover all closed points. Their union contains
every point: its closed complement, if nonempty, would contain a
closed point since the schemes are of finite type over a field.
This gives the claimed neighborhoods at arbitrary points as well.
