+++
id = "lemma-nagata-conrad-quasi-affine-equal-opens"
kind = "lemma"
title = "Quasi-affine target over a qcqs base, $U=V$ (Conrad)"
order = 212
lean = ["AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom"]
uses = ["def-nagata-admissible-blowup", "def-nagata-conrad-quasi-domination", "def-nagata-constructible-closed-support", "def-nagata-dense-compactification", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "def-nagata-qc-open-complement-ideal", "def-nagata-quasi-affine-morphism", "lemma-nagata-admissible-blowup-preserves-density", "lemma-nagata-blowup-proper", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-conrad-quasi-affine-affine-base", "lemma-nagata-constructible-closed-support", "lemma-nagata-dense-flat-pullback", "lemma-nagata-ext-scheme-theoretically-dominant-separated", "lemma-nagata-extend-admissible-blowup", "lemma-nagata-ideal-invertible-product-factor", "lemma-nagata-invertible-product-factor", "lemma-nagata-qc-open-complement-ideal", "lemma-nagata-qc-open-complement-ideal-exists", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-product-ideal", "thm-nagata-blowup-universal-property", "thm-nagata-global-blowup-proper"]
+++
Let $X$ be qcqs, let $U\subseteq X$ be a quasi-compact open, let
$p\colon Y\to X$ be separated, quasi-affine and locally of finite type, and
let $f\colon U\to Y$ be an $X$-morphism. There is a finite type
quasi-coherent ideal $\mathcal I$ on $X$ with
$V(\mathcal I)\subseteq X\setminus U$ such that
$\widetilde X=\operatorname{Bl}_{\mathcal I}(X)$ carries a quasi-domination
of $\widetilde X$ over $Y$ extending $f$, and such that the inverse image of
$U$ in $\widetilde X$ is scheme-theoretically dense.

As in [lemma-nagata-conrad-quasi-affine-affine-base], $U$ need not be
assumed dense in $X$: the centre constructed below cuts out exactly the
boundary $X\setminus U$, so the inverse image of $U$ becomes
scheme-theoretically dense in $\widetilde X$ in any case.

## Proof

Choose a finite affine open cover $X=\bigcup_{i=0}^nW_i$ and put
$U_i=U\cap W_i$, a quasi-compact open of $W_i$, and $Y_i=p^{-1}(W_i)$,
quasi-affine and locally of finite type over $W_i$. Let
$f_i\colon U_i\to Y_i$ be the restriction of $f$.

By [lemma-nagata-conrad-quasi-affine-affine-base] there is, for each
$i$, a finite type quasi-coherent ideal $\mathcal I_i$ on $W_i$ with
$V(\mathcal I_i)\subseteq W_i\setminus U_i$, an open
$T_i\subseteq\operatorname{Bl}_{\mathcal I_i}(W_i)$ containing the inverse
image of $U_i$, and a $W_i$-morphism $g_i\colon T_i\to Y_i$ extending $f_i$
whose graph is closed in
$Y_i\times_{W_i}\operatorname{Bl}_{\mathcal I_i}(W_i)$.

*Extending the centres.* By
[lemma-nagata-extend-admissible-blowup] each $\mathcal I_i$ extends to a
finite type quasi-coherent ideal $\mathcal J_i$ on $X$ with
$V(\mathcal J_i)\cap U=\varnothing$ whose blow-up restricts over $W_i$ to
$\operatorname{Bl}_{\mathcal I_i}(W_i)$, and does so as a cartesian square.

*The blow-up.* By
[lemma-nagata-qc-open-complement-ideal-exists] there is a finite type
quasi-coherent ideal $\mathcal K$ on $X$ with $V(\mathcal K)=X\setminus U$.
Set $\mathcal I=\mathcal K\cdot\prod_i\mathcal J_i$, a finite type ideal with
$V(\mathcal I)=X\setminus U$ *exactly*, and let
$\pi\colon\widetilde X=\operatorname{Bl}_{\mathcal I}(X)\to X$ be its
blow-up. Since $V(\mathcal I)=X\setminus U$, the second assertion of
[lemma-nagata-conrad-dense-in-admissible-blowup] makes $\pi^{-1}(U)$
scheme-theoretically dense in $\widetilde X$, hence also topologically
dense; this is the last assertion of the lemma.

Each $\mathcal J_i$ divides $\mathcal I$, so its inverse image on
$\widetilde X$ is an invertible factor of the invertible ideal
$\mathcal I\cdot\mathcal O_{\widetilde X}$ and is therefore itself
invertible. The universal property of blowing up
([thm-nagata-blowup-universal-property]) then gives a canonical
$X$-morphism $\pi_i\colon\widetilde X\to\operatorname{Bl}_{\mathcal J_i}(X)$.
Restricting $\pi_i$ over $W_i$ and using the cartesian square of the
previous paragraph, we obtain a $W_i$-morphism
$\rho_i\colon\pi^{-1}(W_i)\to\operatorname{Bl}_{\mathcal I_i}(W_i)$.

Put $T_i'=\rho_i^{-1}(T_i)\subseteq\pi^{-1}(W_i)$, an open subscheme of
$\widetilde X$ containing $\pi^{-1}(U\cap W_i)$, and let
$\overline f_i\colon T_i'\to Y$ be the composite of $\rho_i|_{T_i'}$, $g_i$
and $Y_i\hookrightarrow Y$. The graph $\Gamma_i$ of $\overline f_i$ is a
base change of the graph of $g_i$ along the comparison morphism of the two
fibre products, hence a closed immersion; so $\Gamma_i$ is closed in the part
$(Y\times_X\widetilde X)|_{W_i}$ of $Y\times_X\widetilde X$ lying over
$W_i$.

*Gluing.* Let $T=\bigcup_iT_i'$, an open subscheme of $\widetilde X$
containing $\bigcup_i\pi^{-1}(U\cap W_i)=\pi^{-1}(U)$. The $X$-morphisms
$\overline f_i$ agree on overlaps: the open $\pi^{-1}(U)\cap T_i'\cap T_j'$
is scheme-theoretically dense in $T_i'\cap T_j'$, both morphisms agree with
$f$ on it, and $Y\to X$ is separated, so
[lemma-nagata-ext-scheme-theoretically-dominant-separated] makes them
agree on $T_i'\cap T_j'$. They therefore glue to an $X$-morphism
$\overline f\colon T\to Y$ extending $f$.

*Closedness of the graph.* The graph $\Gamma_{\overline f}$ is the
union of the $\Gamma_i$, and closedness may be checked on the open cover of
$Y\times_X\widetilde X$ by the parts lying over the $W_i$. So it suffices to
prove that the local extension loci are pairwise compatible:

$$
T_j'\cap\pi^{-1}(W_i)\subseteq T_i'\qquad\text{for all }i,j,
$$

for then $\Gamma_{\overline f}\cap(Y\times_X\widetilde X)|_{W_i}=\Gamma_i$,
which is closed there. (This step is not formal: a priori
$\overline f_j$ could be defined at points of $\pi^{-1}(W_i)$ where
$\overline f_i$ is not.)

Fix $i$ and $j$ and put $N=\pi^{-1}(U\cap W_i)\cap T_j'$. The two morphisms
$\overline f_i$ and $\overline f_j$ agree on $N$, both being restrictions of
$f$ there, so $\Gamma_j|_N=\Gamma_i|_N$ and in particular
$\Gamma_j(N)\subseteq\Gamma_i$. Since $\pi^{-1}(U)$ is topologically dense
in $\widetilde X$ and $T_j'\cap\pi^{-1}(W_i)$ is open, $N$ is dense in
$T_j'\cap\pi^{-1}(W_i)$; as $\Gamma_j$ is continuous,
$\Gamma_j\bigl(T_j'\cap\pi^{-1}(W_i)\bigr)$ lies in the closure of
$\Gamma_j(N)$. Intersecting with the open
$(Y\times_X\widetilde X)|_{W_i}$, in which $\Gamma_i$ is closed, gives
$\Gamma_j\bigl(T_j'\cap\pi^{-1}(W_i)\bigr)\subseteq\Gamma_i$. Projecting to
$\widetilde X$ and using that a graph maps isomorphically to its domain
yields $T_j'\cap\pi^{-1}(W_i)\subseteq T_i'$, as claimed.

Hence $(T,\overline f)$ is a quasi-domination of $\widetilde X$ over $Y$
extending $f$.
