+++
id = "lemma-nagata-conrad-disjointness-blowup"
kind = "lemma"
title = "Deligne's disjointness blow-up (Deligne, *Lemme* 0.3) (Conrad)"
order = 208
lean = ["AlgebraicGeometry.disjoint_closure_range_of_blowupMap_sup"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-blowup-chart-ring", "def-nagata-conrad-disjointness-setup", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-chart-extended-ideal-principal", "lemma-nagata-conrad-strict-transform-in-charts", "lemma-nagata-dense-flat-pullback", "lemma-nagata-extended-ideal-affine-chart", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-ideal-unit-off-support", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-restrict-open", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded"]
+++
In the situation of [def-nagata-conrad-disjointness-setup], the two
closed subsets

$$
\overline{Y'},\qquad
p'^{-1}\bigl(\overline{q^{-1}(V\setminus U)}\bigr)
$$

of $Z'$ are disjoint. In words: after the base change by $q$, the closure
of the image of $Y$ in $Z$ no longer meets the part of $Z$ lying over the
closure of $V\setminus U$.

## Proof

Formation of topological closures commutes with restriction to an open
subspace, and by [lemma-nagata-scheme-image-restrict-open] the same
holds for scheme-theoretic images of quasi-compact immersions. The
assertion is therefore local on $X$ and on $Z$, so we may assume
$X=\operatorname{Spec}(A)$ and $Z=\operatorname{Spec}(B)$. Put
$I_j=\Gamma(X,\mathcal I_j)$. We construct, locally on $X'$, a function on
$Z'$ which vanishes on $p'^{-1}(\overline{q^{-1}(V\setminus U)})$ and equals
$1$ on $\overline{Y'}$.

*Step 1: the charts $U(s_2)$, $s_2\in I_2$, cover
$\overline{q^{-1}(V\setminus U)}$.* The strict transform of $V(\mathcal I_1)$
is a closed subscheme of $X'$. Since $q$ is an isomorphism over $V$ we have
$q^{-1}(V\setminus U)\cong V\setminus U$ as topological spaces, and the
underlying space of $V(\mathcal I_1)$ contains $\overline{V\setminus U}$; so
$\overline{q^{-1}(V\setminus U)}$ lies inside the strict transform of
$V(\mathcal I_1)$. By
[lemma-nagata-conrad-strict-transform-in-charts], applied to the two
centres $V(\mathcal I_1)$ and $V(\mathcal I_2)$, that strict transform is
covered by the charts $U(s_2)$ with $s_2\in I_2$.

*Step 2: reduction.* By Step 1 the opens $p'^{-1}(U(s_2))$, for
$s_2\in I_2$, cover $p'^{-1}(\overline{q^{-1}(V\setminus U)})$, and

$$
p'^{-1}\bigl(\overline{q^{-1}(V\setminus U)}\bigr)
\subseteq p'^{-1}\bigl(q^{-1}(T_1)\bigr)
$$

because $\overline{V\setminus U}\subseteq V(\mathcal I_1)=T_1$ as sets. So
it suffices to prove, for every $s_2\in I_2$,

$$
p'^{-1}\bigl(q^{-1}(T_1)\bigr)\cap p'^{-1}(U(s_2))\cap\overline{Y'}
=\varnothing .
$$

*Step 3: an equation for $s_2$ on $\overline Y$.* By hypothesis (3) of
[def-nagata-conrad-disjointness-setup], $p^{-1}(T_1)\cap\overline Y$ is
a closed subscheme of $p^{-1}(T_2)$, so $p^{\#}(s_2)\in B$ vanishes on it.
Hence $p^{\#}(s_2)=t_1+g$ with $t_1$ vanishing on the closed subscheme
$p^{-1}(T_1)$, which is cut out by $I_1^2B$, and $g$ vanishing on
$\overline Y$. Write $t_1=\sum_ib_is_{1i}r_{1i}$ with $s_{1i},r_{1i}\in I_1$
and $b_i\in B$. Since $Y\hookrightarrow\overline Y$ is a schematically dense
open immersion, we get on $\overline Y$ the identity
$s_2=\sum_ib_is_{1i}r_{1i}$.

*Step 4: $s_2$ is a unit where it matters.* The scheme $Y$ lies over
$U\subseteq V$ and $V$ does not meet $T_2$, so

$$
Y'\cap p'^{-1}(U(s_2))
\subseteq p'^{-1}\bigl(U(s_2)\cap(X'\setminus q^{-1}(T_2))\bigr).
$$

On $U(s_2)\setminus q^{-1}(T_2)$ the section $s_2$ vanishes nowhere, hence is
a unit. Dividing the identity of Step 3 by $s_2$ therefore gives

$$
h:=\sum_ib_i\Bigl(\frac{s_{1i}}{s_2}\Bigr)r_{1i}=1
\qquad\text{on }Y'\cap p'^{-1}(U(s_2)).
$$

Each $s_{1i}/s_2$ is a global section of $\mathcal O$ on the chart $U(s_2)$,
by the very definition of the chart algebra
([def-nagata-blowup-chart-ring]), so $h$ is a global function on the
open subscheme $p'^{-1}(U(s_2))$ of $Z'$.

*Step 5: passing to the closure.* The immersion
$Y'\cap p'^{-1}(U(s_2))\to p'^{-1}(U(s_2))$ is quasi-compact, so $h=1$ on the
scheme-theoretic image $\overline{Y'\cap p'^{-1}(U(s_2))}$ as well
([def-nagata-scheme-theoretic-closure]); and that image is
$\overline{Y'}\cap p'^{-1}(U(s_2))$, because closures commute with
restriction to an open subscheme.

*Step 6: conclusion.* All the $r_{1i}$ lie in $I_1$, so $h$ vanishes on
$p'^{-1}(q^{-1}(V(\mathcal I_1)))\cap p'^{-1}(U(s_2))$. Thus the single
function $h$ takes the value $1$ on
$\overline{Y'}\cap p'^{-1}(U(s_2))$ and the value $0$ on
$p'^{-1}(q^{-1}(V(\mathcal I_1)))\cap p'^{-1}(U(s_2))$, so these two subsets
are disjoint. Since $V(\mathcal I_1)=V(\mathcal I_1^2)=T_1$ as sets, this is
exactly eq:nagata-conrad-disjointness-local.
