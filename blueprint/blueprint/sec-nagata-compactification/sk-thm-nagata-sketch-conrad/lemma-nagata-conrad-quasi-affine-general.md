+++
id = "lemma-nagata-conrad-quasi-affine-general"
kind = "lemma"
title = "Quasi-affine target, $U\\subseteq V$ (Conrad)"
order = 216
lean = ["AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom_of_le"]
uses = ["def-nagata-admissible-blowup", "def-nagata-conrad-quasi-domination", "def-nagata-dense-compactification", "def-nagata-global-blowup", "def-nagata-quasi-affine-morphism", "lemma-nagata-admissible-blowup-comp", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-blowup-proper", "lemma-nagata-conrad-case3-disjointness-reduction", "lemma-nagata-conrad-case3-smaller-base", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-conrad-quasi-affine-equal-opens", "lemma-nagata-extend-admissible-blowup", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
Let $X$ be qcqs, let $U\subseteq V\subseteq X$ be quasi-compact open
subschemes, let $Y$ be qcqs and let $p\colon Y\to X$ be separated,
quasi-affine and locally of finite type. Let $f\colon U\to Y$ be an
$X$-morphism whose image is closed in $p^{-1}(V)$. There is a finite type
quasi-coherent ideal $\mathcal I$ on $X$ with
$V(\mathcal I)\subseteq X\setminus V$ such that
$\operatorname{Bl}_{\mathcal I}(X)$ carries a quasi-domination over $Y$
extending $f$.

Neither $U$ nor $V$ needs to be assumed dense in $X$. The only density used
below is that of the inverse image of $U$ in the blow-up of the smaller base
$X^{\circ}$ of Step 2, and that is exactly the scheme-theoretic density which
[lemma-nagata-conrad-quasi-affine-equal-opens] hands back. Note also
that the centre is only required to avoid the *larger* open $V$, which
is what makes this statement stronger than
[lemma-nagata-conrad-quasi-affine-equal-opens] rather than a special
case of it.

## Proof

*Step 1: separating $p(\overline{f(U)})$ from $\overline{V\setminus U}$.*
[lemma-nagata-conrad-case3-disjointness-reduction] gives a $V$-admissible
blow-up $\pi_1\colon X_1\to X$ such that, writing
$p_1\colon Y_1=Y\times_XX_1\to X_1$ for the base change of $p$ and
$f_1\colon\pi_1^{-1}(U)\to Y_1$ for the induced section, the closure of
$f_1\bigl(\pi_1^{-1}(U)\bigr)$ is disjoint from
$p_1^{-1}\bigl(\overline{\pi_1^{-1}(V\setminus U)}\bigr)$.

*Step 2: passing to a smaller base.* The closure of
$f_1\bigl(\pi_1^{-1}(U)\bigr)$ is quasi-compact, so its image under $p_1$ is a
quasi-compact subset of $X_1$, and Step 1 makes it disjoint from
$\overline{\pi_1^{-1}(V\setminus U)}$. So
[lemma-nagata-conrad-case3-smaller-base] applies over $X_1$ and produces a
quasi-compact open $X^{\circ}\subseteq X_1$ containing both
$p_1\bigl(\overline{f_1(U)}\bigr)$ and $\pi_1^{-1}(U)$, with
$X^{\circ}\cap\pi_1^{-1}(V)=\pi_1^{-1}(U)$. From now on we work over $X_1$
and write $U$, $V$, $Y$, $p$, $f$ for their inverse images and base changes
there.

*Step 3: applying Case 2.* Put $Y^{\circ}=p_1^{-1}(X^{\circ})$. The
morphism $Y^{\circ}\to X^{\circ}$ is separated, locally of finite type and
quasi-affine: quasi-affineness of a morphism is stable under base change
(`AlgebraicGeometry.IsQuasiAffineHom.of_isPullback`) and under
restricting the base to an open subscheme. Since $X^{\circ}\cap V=U$,
[lemma-nagata-conrad-quasi-affine-equal-opens] applies over $X^{\circ}$
with the single open $U$: there is a finite type quasi-coherent ideal
$\mathcal I^{\circ}$ on $X^{\circ}$ with
$V(\mathcal I^{\circ})\subseteq X^{\circ}\setminus U$, an open
$W^{\circ}\subseteq\widetilde X^{\circ}= \operatorname{Bl}_{\mathcal I^{\circ}}(X^{\circ})$ containing the inverse
image of $U$, and an $X^{\circ}$-morphism $g^{\circ}\colon W^{\circ}\to Y^{\circ}$ extending $f$ whose graph is closed in
$Y^{\circ}\times_{X^{\circ}}\widetilde X^{\circ}$; moreover the inverse image
of $U$ in $\widetilde X^{\circ}$ is scheme-theoretically dense.

Note that it is *not* necessary to replace $Y^{\circ}$ by the
scheme-theoretic image of $f$ here, as Conrad does. That
replacement is only used to make the graph closed in Step 5, and for that
purpose the closed *subset* $\overline{f_1(U)}$ of $Y_1$ suffices.

*Step 4: descending the centre to $X_1$.* Since
$V(\mathcal I^{\circ})\subseteq X^{\circ}\setminus U= X^{\circ}\setminus(X^{\circ}\cap V)$, the centre $\mathcal I^{\circ}$ is
disjoint from $X^{\circ}\cap V$, so
[lemma-nagata-extend-admissible-blowup] extends it to a $V$-admissible
finite type quasi-coherent ideal $\mathcal I_2$ on $X_1$ whose blow-up
$\pi_2\colon\widetilde X_1\to X_1$ restricts over $X^{\circ}$ to
$\widetilde X^{\circ}$, cartesianly. Transporting $(W^{\circ},g^{\circ})$
along that cartesian square — this is the same transport lemma as in the
proof of [lemma-nagata-conrad-quasi-affine-equal-opens] — gives an open
$W\subseteq\pi_2^{-1}(X^{\circ})\subseteq\widetilde X_1$ containing
$\pi_2^{-1}\bigl(\pi_1^{-1}(U)\bigr)$ and an $X_1$-morphism $G\colon W\to Y_1$ extending $f_1$, whose graph is closed in the part of
$Y_1\times_{X_1}\widetilde X_1$ lying over $X^{\circ}$.

*Step 5: the graph is closed.* Write $\Gamma\subseteq Y_1\times_{X_1}\widetilde X_1$ for the graph of $G$ and put
$N=\mathrm{pr}_{Y_1}^{-1}\bigl(\overline{f_1(U)}\bigr)$, a closed subset.
The inverse image of $U$ is topologically dense in $\widetilde X^{\circ}$,
by the scheme-theoretic density of Step 3, hence also in the open subscheme
$W$; as $G$ agrees with $f_1$ there, continuity gives
$G(W)\subseteq\overline{f_1(U)}$ and therefore $\Gamma\subseteq N$. On the
other hand $p_1\bigl(\overline{f_1(U)}\bigr)\subseteq X^{\circ}$ by the
choice of $X^{\circ}$, so $N$ is contained in the open part of
$Y_1\times_{X_1}\widetilde X_1$ lying over $X^{\circ}$. A subset of a closed
set contained in an open set is closed as soon as it is closed in that open
set; so $\Gamma$ is closed in $Y_1\times_{X_1}\widetilde X_1$.

*Conclusion.* The composite of the $V$-admissible blow-up
$\pi_1$ of $X$ and the $\pi_1^{-1}(V)$-admissible blow-up $\pi_2$ of $X_1$ is
a $V$-admissible blow-up of $X$ by
[lemma-nagata-admissible-blowup-comp]: there is a finite type
quasi-coherent ideal $\mathcal I$ on $X$ with
$V(\mathcal I)\cap V=\varnothing$ and an $X$-isomorphism
$\widetilde X_1\cong\operatorname{Bl}_{\mathcal I}(X)$. Transporting $(W,G)$
along it, and composing $G$ with $Y_1\to Y$, gives the required
quasi-domination of $\operatorname{Bl}_{\mathcal I}(X)$ over $Y$ extending
$f$.
