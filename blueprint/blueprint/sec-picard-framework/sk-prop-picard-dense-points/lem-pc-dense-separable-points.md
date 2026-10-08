+++
id = "lem-pc-dense-separable-points"
kind = "lemma"
title = "Density of rationally defined closed points"
order = 751
uses = ["def-pc-field-tower", "def-pc-morphism-conventions", "def-pc-scheme", "def-weil-scheme-morphism-properties"]
+++
(Varieties, Lemma 33.25.6, Tag
[056U](https://stacks.math.columbia.edu/tag/056U).)
Let $k$ be a field and let $X$ be a scheme over $k$ which is smooth
over $k$. Then the set of closed points $x\in X$ with $\kappa(x)/k$
finite and separable is dense in $X$.

## Proof

It suffices to show: for every nonempty open $V\subseteq X$ there is a
closed point of $V$ with finite separable residue field over $k$ (the
statement is Zariski-local and the assertion is stable under replacing
$X$ by a nonempty open, so we may replace $X$ by $V$ in the course of
the argument). Choose a diagram

$$
\pi:U\longrightarrow\mathbf A^d_k
$$

with $U\subseteq X$ a nonempty open and $\pi$ an 'etale morphism over $k$
with $U\subseteq X$ a nonempty open and $\pi$ étale: since $X$ is
smooth over the field $k$, the structure morphism is smooth, and a
smooth $k$-algebra is Zariski-locally a standard smooth
$k[x_1,\dots,x_n]/(f_1,\dots,f_c)$ with invertible Jacobian subdeterminant;
the Jacobian condition says exactly that the projection onto the
remaining $n-c$ coordinates is étale – this is Morphisms of Schemes,
Lemma 29.37.21, Tag [054L](https://stacks.math.columbia.edu/tag/054L)
(smooth $=$ locally étale over affine space; we replace $X$ by the
relevant open).

The morphism $\pi$ is open (etale morphisms are open: Morphisms of
Schemes, Lemma 29.37.13, Tag
[03WT](https://stacks.math.columbia.edu/tag/03WT)), so
$\pi(U)\subseteq\mathbf A^d_k$ is a nonempty open. By Varieties,
Lemma 33.25.5 (Tag [055T](https://stacks.math.columbia.edu/tag/055T))
there is a closed point $w\in\pi(U)$ with $\kappa(w)/k$ finite
separable: the proof of 33.25.5 is the simple argument that a nonempty
open $W\subseteq\mathbf A^d_k$ contains the point
$(a_1,\dots,a_d)$ of $k^{sep}$-rational type with
$f(a_1,\dots,a_d)\neq0$ (after shrinking, $W=\mathbf A^d_k\setminus V(f)$
for a nonzero polynomial $f$, and $f$ cannot vanish on the whole of
$(k^{sep})^d$ because $k^{sep}$ is infinite: e.g. if $k$ is finite
then $k^{sep}=\bigcup_{m\ge1}\mathbf F_{q^{m!}}$ is infinite and a
nonzero polynomial in $d$ variables over an infinite field does not
vanish identically elsewhere; the same genericity argument applies for
any infinite field); the point
$\operatorname{Spec}(k(a_1,\dots,a_d))\to\mathbf A^d_k$ with
$k(a_1,\dots,a_d)/k$ finite separable (the $a_i$'s are separable:
their minimal polynomials are separable since their roots generate a
separable extension) is a closed point of $W$: its residue field is
finite over $k$, and points of a scheme locally of finite type over a
field with finite residue field are closed (Morphisms of Schemes,
Lemma 29.21.2, Tag [01TE](https://stacks.math.columbia.edu/tag/01TE)).

Pick any $x\in U$ with $\pi(x)=w$. By Morphisms of Schemes,
Lemma 29.37.7 (Tag [02GL](https://stacks.math.columbia.edu/tag/02GL))
the extension $\kappa(x)/\kappa(w)$ is finite separable (for an étale
ring map $R\to S$ over a field, the residue extension is finite
separable: an étale morphism is unramified, so the residue extension
is a finite separable extension, a standard consequence of the
definitions of unramified and flat), hence $\kappa(x)/k$ is finite
separable by transitivity. The point $x$ is closed in $X$: it is
closed in $U$ (its residue field is finite over $k$), and a closed
point of a nonempty open of a scheme locally of finite type over $k$
with finite residue field is closed in $X$: its residue field $\kappa(x)$
is finite over $k$, so $x$ is closed in every open neighbourhood in
which it lies (the standard criterion of 01TE applies
Zariski-locally on $X$). This proves the claim for $V$ (we applied the
argument with $U$ replaced by the nonempty open $U\cap V$).
