+++
id = "lem-kun-0f1i-normal"
kind = "lemma"
title = "The normal integral case"
order = 1776
uses = ["def-kun-constant-sheaf", "def-kun-separably-closed", "def-kun-torsion-invertible", "def-kun-unbounded-exchange", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-kun-0ezp", "lem-kun-0ezt", "lem-kun-0f1h", "lem-kun-algebra-union", "lem-kun-colim-of-localizations", "lem-kun-fibre-product-limits", "lem-kun-zn-sheaf-invertible-orders"]
+++
Let $K$ be a field and let $n\ge1$ be an integer invertible in
$K$. Let $X$ be a scheme of finite type over $K$, let $S'$
be an affine, integral and normal $K$-scheme with algebraically
closed function field $L$, set $X'=X\times_KS'$,
$Y=X'\times_{S'}\Spec(L)$, and let $h:Y\to X'$ be the projection.
Then $R^qh_*\underline{\mathbf Z/d\mathbf Z}=0$ for all $q>0$
and all $d\mid n$. (*Source:* Stacks Project, Tag
[0F1I](https://stacks.math.columbia.edu/tag/0F1I), final
reduction.)

## Proof

Write $S'=\Spec(B)$, so that $L$ is the fraction field of $B$.
By [lem-kun-algebra-union] write $B=\bigcup_{i\in I}B_i$ as the
union of its finite type $K$-subalgebras $B_i$. Let $J$ be the
set of pairs $(i,g)$ with $i\in I$ and $g\in B_i$ nonzero,
ordered by $(i',g')\ge(i,g)$ if and only if $B_i\subset B_{i'}$
and $g$ maps to an invertible element of $(B_{i'})_{g'}$. Then
$L=\varinjlim_{(i,g)\in J}(B_i)_g$ by
[lem-kun-colim-of-localizations]. For $j=(i,g)\in J$ set
$S_j=\Spec(B_i)$ and $U_j=\Spec((B_i)_g)$. Then the diagram

$$
\begin{array}{ccc}
X'&\xleftarrow{\;h\;}&Y\\
\Big\downarrow{}&&\Big\downarrow{}\\
S'&\longleftarrow&\Spec(L)
\end{array}
\qquad\text{is the limit of}\qquad
\begin{array}{ccc}
X\times_KS_j&\xleftarrow{\;h_j\;}&X\times_KU_j\\
\Big\downarrow{}&&\Big\downarrow{}\\
S_j&\longleftarrow&U_j
\end{array}
$$

by [lem-kun-fibre-product-limits] (limits and fibre products
commute) and [lem-kun-colim-of-localizations]: the rings $(B_i)_g$
have filtered colimit $L$, so their spectra have limit $\Spec(L)$, and
the resulting maps exhibit the diagram $S'\leftarrow\Spec(L)$ as the
limit of the diagrams $S_j\leftarrow U_j$. Thus we may
apply [lem-kun-0ezt] to see that it suffices to prove that the
exchange morphisms (of [def-kun-unbounded-exchange]) hold in the
diagrams on the right. Each right-hand diagram is the diagram of
[lem-kun-0f1h] for the open immersion $j:U_j\to S_j$ of finite
type $K$-schemes and the scheme $X$ of finite type over $K$,
applied to the sheaf $\underline{\mathbf Z/d\mathbf Z}$, a sheaf of
$\mathbf Z/d\mathbf Z$-modules whose stalks are $d$-torsion, with
$d\mid n$ invertible in $K$, hence of orders invertible in $K$
by [lem-kun-zn-sheaf-invertible-orders].
Hence [lem-kun-0f1h] gives

$$
(X\times_KS_j\to S_j)^{-1}R^q(U_j\to S_j)_*\underline{\mathbf Z/d\mathbf Z}
\;\cong\;R^qh_{j,*}\underline{\mathbf Z/d\mathbf Z}
$$

for all $q\ge0$. Passing to the limit with
[lem-kun-0ezt] we obtain

$$
(X'\to S')^{-1}R^q(\Spec(L)\to S')_*\underline{\mathbf Z/d\mathbf Z}
\;\cong\;R^qh_*\underline{\mathbf Z/d\mathbf Z}
$$

for all $q$. But $\Spec(L)$ is integral and normal with
algebraically closed (hence separably closed) function field, so
$R^q(\Spec(L)\to S')_*\underline{\mathbf Z/d\mathbf Z}=0$ for
$q>0$ by [lem-kun-0ezp]. Hence
$R^qh_*\underline{\mathbf Z/d\mathbf Z}=0$ for $q>0$, as
desired.
