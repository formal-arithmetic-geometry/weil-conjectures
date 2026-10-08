+++
id = "lemma-nagata-conrad-case3-disjointness-reduction"
kind = "lemma"
title = "The disjointness reduction in Case 3 (Conrad)"
order = 214
lean = ["AlgebraicGeometry.exists_isAdmissible_disjoint_closure_range_of_le"]
uses = ["def-nagata-admissible-blowup", "def-nagata-conrad-disjointness-setup", "def-nagata-constructible-closed-support", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-qc-open-complement-ideal", "def-nagata-scheme-theoretic-image", "lemma-nagata-conrad-disjointness-blowup", "lemma-nagata-constructible-closed-support", "lemma-nagata-finite-type-ideal-compact", "lemma-nagata-finite-type-ideal-power-in-ideal", "lemma-nagata-ideal-directed-union-finite-type", "lemma-nagata-qc-open-complement-ideal", "lemma-nagata-qc-open-complement-ideal-exists", "prop-nagata-global-blowup-cover-independent"]
+++
Let $X$ be qcqs, let $U\subseteq V\subseteq X$ be quasi-compact open
subschemes, let $p\colon Y\to X$ be a morphism with $Y$ qcqs, and let
$f\colon U\to Y$ be a section of $p$ over $U$ whose image is closed in
$p^{-1}(V)$. There is a $V$-admissible blow-up
$q\colon\widetilde X=\operatorname{Bl}_{\mathcal I}(X)\to X$ such that, after
base change along $q$, the closure of the image of $f$ is disjoint from the
part lying over $\overline{q^{-1}(V\setminus U)}$.

## Proof

We produce the two centres required by
[lemma-nagata-conrad-disjointness-blowup], applied with $Z=Y$, with the
open immersions $U\subseteq V\subseteq X$, and with $f(U)=\Gamma_f$ in the
role of the scheme lying over $U$.

Let $\mathcal H$ be the ideal of the reduced structure on the closed subset
$\overline{V\setminus U}$, so $V(\mathcal H)=\overline{V\setminus U}$; since
$V\setminus U$ is closed in $V$, its closure misses $U$. Give $X\setminus V$
a finite type closed subscheme structure $V(\mathcal K)$ using
[lemma-nagata-qc-open-complement-ideal-exists].

We first check $p\bigl(p^{-1}(V(\mathcal H^2))\cap\overline{f(U)}\bigr) \subseteq X\setminus V$ as sets. Indeed a point of the left-hand side lies
in $\overline{V\setminus U}$, and if it lay in $V$ then, $f(U)$ being closed
in $p^{-1}(V)$, the point of $\overline{f(U)}$ above it would lie in $f(U)$
and so map into $U$, which is disjoint from $\overline{V\setminus U}$. As
$\mathcal K$ is of finite type,
[lemma-nagata-finite-type-ideal-power-in-ideal] gives an $n$ with

$$
\mathcal K^n\cdot\mathcal O_Y\subseteq
\mathcal H^2\cdot\mathcal O_Y+\mathcal I_{\overline{f(U)}} .
$$

The ideal $\mathcal H$ need not be of finite type. By
[lemma-nagata-ideal-directed-union-finite-type] it is the directed
supremum of its finite type quasi-coherent subideals $\mathcal I_{1,\alpha}$;
products and inverse images of ideals commute with directed suprema, so
$\mathcal H^2\cdot\mathcal O_Y+\mathcal I_{\overline{f(U)}}$ is the directed
supremum of the $\mathcal I_{1,\alpha}^2\cdot\mathcal O_Y+ \mathcal I_{\overline{f(U)}}$, and
[lemma-nagata-finite-type-ideal-compact] applied to the finite type
ideal $(\mathcal K\cdot\mathcal O_Y)^n$ produces an $\alpha$ with

$$
\mathcal K^n\cdot\mathcal O_Y\subseteq
\mathcal I_{1,\alpha}^2\cdot\mathcal O_Y+\mathcal I_{\overline{f(U)}} .
$$

Now take $\mathcal I_1=\mathcal I_{1,\alpha}$ and
$\mathcal I_2=\mathcal I_{1,\alpha}^2+\mathcal K^n$, so that
$T_2=V(\mathcal I_2)=T_1\cap V(\mathcal K^n)$ is disjoint from $V$, and
$\mathcal I=\mathcal I_1+\mathcal I_2$. The centre $\mathcal I$ is of finite
type and $V(\mathcal I)\subseteq V(\mathcal I_2)\subseteq X\setminus V$, so
the blow-up is $V$-admissible; the containment
$\overline{V\setminus U}=V(\mathcal H)\subseteq V(\mathcal I_{1,\alpha})$
holds because $\mathcal I_{1,\alpha}\subseteq\mathcal H$, the scheme $f(U)$
lies over $U$ because $f$ is a section of $p$, and the displayed containment
is hypothesis (3) of [def-nagata-conrad-disjointness-setup]. So
[lemma-nagata-conrad-disjointness-blowup] applies and gives the
assertion.

(Conrad additionally arranges $\mathcal I_{1,\alpha}|_U=\mathcal O_U$; this
is not needed here, because $V(\mathcal I)\subseteq V(\mathcal K^n)$ is
already disjoint from $V$, hence from $U$.)
