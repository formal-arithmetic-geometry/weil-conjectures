+++
id = "lem-pc-hilb-addition"
kind = "lemma"
title = "The addition morphism on Hilbert schemes"
order = 787
uses = ["def-pc-finite-locally-free", "def-pc-hilb-functor", "lem-pc-cartier-criterion"]
+++
(Picard Schemes of Curves, Lemma 44.3.4, Tag
[0B9G](https://stacks.math.columbia.edu/tag/0B9G).) Let $X\to S$ be
a separated smooth morphism of relative dimension $1$, assume that
all the functors $\operatorname{Hilb}^e_{X/S}$ are representable,
and let $d\geq0$. There is a canonical morphism

$$
\underline{\operatorname{Hilb}}^d_{X/S}\times_SX\;\longrightarrow\;\underline{\operatorname{Hilb}}^{d+1}_{X/S},
$$

finite locally free of degree $d+1$, sending a pair
$(Z,x)$ of a degree-$d$ closed subscheme and a point to the
scheme-theoretic addition of $x$ to $Z$.
For a rational point $x$ this is the divisor $Z+x$.

## Proof

Assume $\operatorname{Hilb}^d_{X/S}$ and $\operatorname{Hilb}^{d+1}_{X/S}$ are representable (for
the statement of the lemma this is part of the hypotheses, cf. the
formulation ``or as in Lemma 44.3.4''; the proof constructs the
morphism from the universal objects, so representability is exactly
what is needed); write $H_d:=\underline{\operatorname{Hilb}}^d_{X/S}$,
$H_{d+1}:=\underline{\operatorname{Hilb}}^{d+1}_{X/S}$ and let

$$
D_{\mathrm{univ}}\subseteq X_{H_{d+1}}=H_{d+1}\times_SX
$$

be the universal closed object of degree $d+1$ (the element of
$\operatorname{Hilb}^{d+1}_{X/S}(H_{d+1})$ given by representability,
[def-pc-hilb-functor]).

*Step 1: the subtraction claim.* Let $T$ be a scheme over $S$,
$D\subseteq X_T$ a closed subscheme finite locally free of degree
$d+1$ over $T$ and $x:T\to X$ a morphism whose graph
$\Gamma_x:T\to X_T$ is contained in $D$ (as closed subschemes). Then
there is a closed subscheme $D'\subseteq X_T$, finite locally free of
degree $d$ over $T$, with $D=D'+\Gamma_x$ (the sum of the effective
Cartier divisors).
Proof: by [lem-pc-cartier-criterion] ((1)$\Rightarrow$(2)) both
$D\to T$ and $\Gamma_x\to T$ ($\cong T$, finite locally free of degree
$1$; it is a closed subscheme of $X_T$ because the graph of a morphism
to a separated scheme over $S$ is closed) are relative effective
Cartier divisors on $X_T/T$; since $\Gamma_x\subseteq D$, the classical
difference statement for relative effective Cartier divisors
(Divisors, Lemma 31.19.4, Tag
[0B8V](https://stacks.math.columbia.edu/tag/0B8V): if
$D_1,D_2$ are relative effective Cartier divisors with $D_1\subseteq D_2$ there is a relative effective Cartier divisor $D'$ with
$D_2=D_1+D'$) gives $D=D'+\Gamma_x$ with $D'$ a relative effective
Cartier divisor. Then $D'\subseteq D$ (the summand of a sum is
contained in the sum) so $D'\to T$ is finite (a closed subscheme of
the finite scheme $D$ over $T$), hence finite locally free
([def-pc-finite-locally-free]: finite + flat + locally of finite
presentation, the latter because $D'$ is an effective Cartier divisor
on the finite presentation scheme $X_T$). Its degree is
$d+1-1=d$: the degree of the sum of two finite locally free effective
Cartier divisors is the sum of the degrees (the local computation:
with local defining equations $w$ (of $D'$) and $v$ (of $\Gamma_x$)
on an affine open $\operatorname{Spec}(B)$ of $X_T$, the sequence

$$
0\to B/(w)\to B/(vw)\to B/(v)\to0
$$

is exact – the first map is multiplication by $v$, injective since
$v$ is a nonzerodivisor, and the quotient of $B/(vw)$ by its image
$(v)/(vw)\cong B/(w)$ is $B/(v)$ – so the rank of
$B/(vw)=\mathcal{O}_{D'+\Gamma_x}$ is the sum of the ranks of $\mathcal{O}_{D'}$ and
$\mathcal{O}_{\Gamma_x}$, that is $\deg D=\deg D'+\deg\Gamma_x=\deg D'+1$;
hence $\deg D'=d$ since $\deg D=d+1$). This proves
the claim.

*Step 2: the morphism.* Consider the map of functors on
$(\mathit{Sch}/S)$: a $T$-valued point of $H_d\times_SX$ is a pair
$(D',x)$ with $D'\in\operatorname{Hilb}^d_{X/S}(T)$ (a closed subscheme of $X_T$
finite locally free of degree $d$) and $x:T\to X$; over $T$ the pair
$(D'+\Gamma_x,x)$ is, by Step 1 applied with $D:=D'+\Gamma_x$ and
$\Gamma_x$, an element of $D_{\mathrm{univ}}(T)$ (an element
$(D,x)$ of $\operatorname{Hilb}^{d+1}(T)$ whose graph is contained in $D$): the
assignment $(D',x)\mapsto(D'+\Gamma_x,x)$ defines a map of functors
$H_d\times_SX\to D_{\mathrm{univ}}(\cdot)\subseteq (H_{d+1}\times_SX)(\cdot)$, and Step 1 provides its inverse
$(\xi=(D,x))\mapsto(D',x)$. Both are natural in $T$, so by the
representability of the functors involved ($D_{\mathrm{univ}}$: the
closed subscheme of $H_{d+1}\times_SX$ whose functor is the
intersection as above; note that $D_{\mathrm{univ}}$ is representable
as the base change of the universal closed subscheme of
$X_{H_{d+1}}$: the closed immersion
$D_{\mathrm{univ}}\to H_{d+1}\times_SX$ represents the subfunctor
$\{\xi=(D,x):\Gamma_x\subseteq D\}$ of $H_{d+1}\times_SX$) the map
is induced by an isomorphism of schemes

$$
H_d\times_SX\;\stackrel{\sim}{\longrightarrow}\;D_{\mathrm{univ}}
$$

over $H_{d+1}$. Composing with the closed immersion
$D_{\mathrm{univ}}\hookrightarrow H_{d+1}\times_SX$ and the projection
to $H_{d+1}$ gives the morphism

$$
H_d\times_SX\;\longrightarrow\;H_{d+1},
$$

finite locally free of degree $d+1$ (it is the composite of an
isomorphism with the projection $D_{\mathrm{univ}}\to H_{d+1}$, and
$D_{\mathrm{univ}}\to H_{d+1}$ is finite locally free of degree
$d+1$: it is the universal closed object, hence finite locally free
of degree $d+1$ by [def-pc-hilb-functor]). The description of
the morphism on points is exactly the statement: a pair $(Z,x)$
goes to $D'+\Gamma_x$; for a closed point $x$ of degree $1$ (with
$\kappa(x)=k$ a field) $\Gamma_x$ is the reduced point and
$Z+\Gamma_x$ is the divisor $Z+x$.
