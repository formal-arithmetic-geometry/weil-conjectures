+++
id = "lem-kun-0f1h"
kind = "lemma"
title = "Base change for open immersions"
order = 1771
uses = ["def-kun-torsion-invertible", "def-kun-truncations", "def-kun-unbounded-exchange", "def-weil-pbc-strict-henselization-limit", "lem-kun-0ezt", "lem-kun-0f09", "lem-kun-0f0u", "lem-kun-0f14b", "lem-kun-0f1c", "lem-kun-0f1g", "lem-kun-0f1h-sep-reduction", "lem-kun-base-change-open-closed", "lem-kun-bc-base-change", "lem-kun-bc-kunneth-compat", "lem-kun-closed-points-of-product", "lem-kun-compactification-affine", "lem-kun-descent-limit", "lem-kun-descent-limit-open", "lem-kun-dimension-extension", "lem-kun-dimension-finite-type", "lem-kun-fibre-product-limits", "lem-kun-finite-closed-subscheme", "lem-kun-invertible-orders-colimit", "lem-kun-leray-bdd", "lem-kun-projective-implies-proper", "lem-kun-proper-stability", "lem-kun-stalk-as-pullback", "lem-kun-stalk-faithful-derived", "lem-kun-tensor-unit", "lem-kun-zn-sheaf-invertible-orders", "lem-weil-pbc-exchange-identity-pasting", "lemma-weil-pbc-direct-image-filtered-colimit"]
+++
Let $K$ be a field. Let $j:U\to X$ be an open immersion of
schemes of finite type over $K$ and let $Y$ be a scheme of finite
type over $K$. Consider the diagram

$$
\begin{array}{ccc}
Y\times_{\Spec(K)}X&\xleftarrow{\;h\;}&Y\times_{\Spec(K)}U\\
\Big\downarrow{\scriptstyle q}&&\Big\downarrow{\scriptstyle p}\\
X&\xleftarrow{\;j\;}&U .
\end{array}
$$

Then the exchange morphism of
[def-kun-unbounded-exchange],
$q^{-1}Rj_*F\to Rh_*p^{-1}F$, is an isomorphism for every abelian
sheaf $F$ on $U_{\Et}$ whose stalks are torsion of orders
invertible in $K$. (*Source:* Stacks Project, Tag
[0F1H](https://stacks.math.columbia.edu/tag/0F1H).)

## Proof

*Reduction to $\kunZn$-coefficients.* Write $F=\varinjlim F[n]$ where the colimit is over the multiplicative system of integers
invertible in $K$ ([def-kun-torsion-invertible] and
[lem-kun-invertible-orders-colimit]). Both sides
of the exchange morphism of [def-kun-unbounded-exchange] commute
with filtered colimits in $F$: $Rj_*$ and $Rh_*$ by the
sheaf-level filtered-colimit property of
[lemma-weil-pbc-direct-image-filtered-colimit] in each degree
(together with the truncation triangles of
[def-kun-truncations]), and the inverse images are exact.
Hence it suffices to prove the lemma for each $F[n]$, a sheaf of
$\kunZn$-modules which has orders invertible in $K$ by
[lem-kun-zn-sheaf-invertible-orders]; that is, we may assume that
$F$ is a sheaf of $\kunZn$-modules for some $n$ invertible in
$K$.

*Induction.* We prove the lemma by induction on
$\kundim X+\kundim Y$, finite by [lem-kun-dimension-finite-type], (well-founded induction on the pair of
dimensions). If $\kundim X\le0$, then $X$ is a finite discrete
set of points ([lem-kun-finite-closed-subscheme]: every
irreducible component of $X$ is a point, hence closed), so $U$ is
open and closed in $X$, and the claim follows from
[lem-kun-base-change-open-closed]. This covers the base of the
induction.

*Stalks over points with positive transcendence degree.*
Choose a point $z\in X\times_KY$; we will show that the exchange
morphism is an isomorphism on the stalk at every geometric point
$\bar z$ over $z$ ([lem-kun-stalk-faithful-derived]).

Suppose first that $z$ maps to $x\in X$ with
$\operatorname{trdeg}_K\kappa(x)>0$. Set
$X'=\Spec(\mathcal O^{\mathrm{sh}}_{X,x})$ and denote
$U'\subset X'$ the inverse image of $U$. Consider the base change

$$
\begin{array}{ccc}
Y\times_KX'&\xleftarrow{\;h'\;}&Y\times_KU'\\
\Big\downarrow{\scriptstyle q'}&&\Big\downarrow{\scriptstyle p'}\\
X'&\xleftarrow{\;j'\;}&U'
\end{array}
$$

of our diagram by $X'\to X$. The morphism $X'\to X$ is a filtered
colimit of etale (in particular smooth) morphisms
([def-weil-pbc-strict-henselization-limit]), so by smooth base
change in the form of [lem-kun-0f09] applied to
$q:Y\times_KX\to X$ with $E:=Rj_*F$, and to
$h:Y\times_KU\to Y\times_KX$ with $E:=p^{-1}F$ (both
$E$ lie in $\Dplus$ with stalks of torsion orders invertible on
the base), the pullback of the exchange morphism to
$Y\times_KX'$ is, by [lem-kun-bc-base-change], the exchange
morphism
$(q')^{-1}Rj'_*F'\to Rh'_*(p')^{-1}F'$, where $F'$ is the pullback
of $F$ to $U'$. So it suffices to show that the latter map is an
isomorphism, for then the original map is an isomorphism on stalks at
$\bar z$ (stalks are computed by pullback,
[lem-kun-stalk-as-pullback]).

By [lem-kun-0f0u] there is a separably closed field $L/K$ such
that $X'=\varprojlim_iX_i$ with $X_i$ affine of finite type over
$L$ and $\kundim X_i<\kundim X$ (using
$\operatorname{trdeg}_K\kappa(x)>0$). For $i$ large enough there
exists an open $U_i\subset X_i$ restricting to $U'$ in $X'$
([lem-kun-descent-limit-open]), and the sheaf $F'$ is a
filtered colimit of pullbacks of sheaves on the $U_i$
([lem-kun-descent-limit]). We apply the induction hypothesis to
the diagrams

$$
\begin{array}{ccc}
Y\times_KX_i&\xleftarrow{\;h_i\;}&Y\times_KU_i\\
\Big\downarrow{\scriptstyle q_i}&&\Big\downarrow{\scriptstyle p_i}\\
X_i&\xleftarrow{\;j_i\;}&U_i
\end{array}
\qquad\text{equal to}\qquad
\begin{array}{ccc}
Y_L\times_LX_i&\xleftarrow{\;h_i\;}&Y_L\times_LU_i\\
\Big\downarrow{\scriptstyle q_i}&&\Big\downarrow{\scriptstyle p_i}\\
X_i&\xleftarrow{\;j_i\;}&U_i
\end{array}
$$

over the field $L$ and to the pullbacks of $F$ to these diagrams:
here $\kundim X_i+\kundim Y_L<\kundim X+\kundim Y$ by
[lem-kun-dimension-extension], so the induction hypothesis
applies and the exchange morphisms at the finite levels are isomorphisms. By [lem-kun-0ezt], applied to the affine limit
system $X_i$, we conclude that the map
$(q')^{-1}Rj'_*F'\to Rh'_*(p')^{-1}F'$ is an isomorphism.

Suppose now that $z$ maps to $y\in Y$ with
$\operatorname{trdeg}_K\kappa(y)>0$. Let
$Y'=\Spec(\mathcal O^{\mathrm{sh}}_{Y,y})$. By
[lem-kun-0f0u] there is a separably closed field $L/K$ with
$Y'=\varprojlim_iY_i$, $Y_i$ affine of finite type over $L$ and
$\kundim Y_i<\kundim Y$; in particular $Y'$ is a scheme over $L$.
Denote with a subscript $L$ base change from schemes over $K$ to
schemes over $L$. Consider the commutative diagrams

$$
\begin{array}{ccccc}
Y'\times_KX&\xleftarrow{\;h'\;}&Y'\times_KU\\
\Big\downarrow{\scriptstyle f}&&\Big\downarrow{\scriptstyle f'}\\
Y\times_KX&\xleftarrow{\;h\;}&Y\times_KU\\
\Big\downarrow{\scriptstyle q}&&\Big\downarrow{\scriptstyle p}\\
X&\xleftarrow{\;j\;}&U
\end{array}
\qquad\text{and}\qquad
\begin{array}{ccccc}
Y'\times_LX_L&\xleftarrow{\;h'\;}&Y'\times_LU_L\\
\Big\downarrow{\scriptstyle q'}&&\Big\downarrow{\scriptstyle p'}\\
X_L&\xleftarrow{\;j_L\;}&U_L\\
\Big\downarrow{}&&\Big\downarrow{}\\
X&\xleftarrow{\;j\;}&U
\end{array}
$$

and observe that the top rows are the same on the left and on the
right (canonical identifications of fibre products,
[lem-kun-fibre-product-limits]). By smooth base change
([lem-kun-0f09], applied to the square
$Y'\times_KU\to Y'\times_KX$ over $Y'\to Y$) we see that
$f^{-1}Rh_*p^{-1}F=Rh'_*(f')^{-1}p^{-1}F$. By smooth base change
for $\Spec(L)\to\Spec(K)$ in the form of [lem-kun-0f1c] we see that $Rj_{L,*}F_L$ is the pullback of $Rj_*F$ to $X_L$.
Combining these two observations, and using that a vertical
composition of exchange morphisms is an exchange morphism
([lem-weil-pbc-exchange-identity-pasting]) we conclude that it suffices to prove that the
exchange morphism for the upper square in the second diagram is an
isomorphism, in order to prove that our original map is an
isomorphism on stalks at $\bar z$. Then, using that
$Y'=\varprojlim_iY_i$ and arguing exactly as in the previous
paragraph ([lem-kun-descent-limit],
[lem-kun-descent-limit-open], the induction hypothesis – since
$\kundim X_L+\kundim Y_i<\kundim X+\kundim Y$ by
[lem-kun-dimension-extension] – and [lem-kun-0ezt]), we
see that the induction hypothesis forces our map over
$Y'\times_KX$ to be an isomorphism.

*Minimal counterexample.* Thus any counterexample with
$\kundim X+\kundim Y$ minimal would have the exchange morphism an
isomorphism on all stalks at non-closed points of $X\times_KY$,
because by [lem-kun-closed-points-of-product] a point $z$ of
$X\times_KY$ is closed if and only if both of its images in $X$
and $Y$ are closed. Since it is enough to prove the isomorphism
after base change along open immersions of the factors
([lem-kun-stalk-faithful-derived]; the base change along the
open immersions $X_0\to X$, $Y_0\to Y$ is a smooth base change
applied to the exchang morphism by [lem-kun-0f09] and
[lem-kun-bc-base-change]), we may assume $X$ and $Y$ are
affine, after replacing them by affine open neighbourhoods of the
images of a closed point where the map is not an isomorphism; the dimension sum cannot increase. However, then we can choose a dense open immersion $Y\to Y'$ with $Y'$ projective over $K$
([lem-kun-compactification-affine]); we have
$\kundim Y'=\kundim Y$ ([lem-kun-dimension-extension]), so we
get a minimal counterexample with $Y$ projective over $K$ (and
with the exchange morphism an isomorphism at all non-closed points).
In the next paragraph we show that this cannot happen.

*The projective case.* Consider a diagram as in the statement
of the lemma such that
$q^{-1}Rj_*F\to Rh_*p^{-1}F$ is an isomorphism at all non-closed
points of $X\times_KY$ and such that $Y$ is projective over $K$.
The restriction of the map to $(X\times_KY)_{K^{\mathrm{sep}}}$ is
the corresponding map for the diagram of the lemma base changed to
$K^{\mathrm{sep}}$ ([lem-kun-0f1c] and
[lem-kun-bc-base-change]), so by
[lem-kun-0f1h-sep-reduction] we may and do assume $K$ is
separably closed. Choose a distinguished triangle

$$
q^{-1}Rj_*F\to Rh_*p^{-1}F\to Q\to(q^{-1}Rj_*F)[1]
$$

in $D((X\times_KY)_{\Et})$. Since the first map is an isomorphism
on stalks at all non-closed points, $Q$ has nonzero stalks only at
closed points of $X\times_KY$, so by [lem-kun-0f1g] it
suffices to prove $H^i((X\times_KY)_{\Et},Q)=0$ for all $i$.
Thus it suffices to prove that
$q^{-1}Rj_*F\to Rh_*p^{-1}F$ induces an isomorphism on cohomology.
Recall that $F$ is annihilated by $n$ invertible in $K$. By the
Kunneth formula of [lem-kun-0f14b] (with proper factor $Y$,
which is projective hence proper by
[lem-kun-projective-implies-proper] and
[lem-kun-proper-stability], and $E=\underline{\kunZn}$; here
$Rj_*F\in D(X_{\Et},\kunZn)$), we have

$$
\begin{aligned}
\RGamma\bigl((X\times_KY)_{\Et},q^{-1}Rj_*F\bigr)
&\cong\RGamma(X_{\Et},Rj_*F)\kunotimes{\kunZn}
\RGamma(Y_{\Et},\underline{\kunZn})\\
&\cong\RGamma(U_{\Et},F)\kunotimes{\kunZn}
\RGamma(Y_{\Et},\underline{\kunZn}),
\end{aligned}
$$

using [lem-kun-tensor-unit]
for $q^{-1}Rj_*F\cong\pr_1^{-1}\underline{\kunZn}\kunotimes{\kunZn} \pr_2^{-1}Rj_*F$ and [lem-kun-leray-bdd]
for the second line, and

$$
\RGamma\bigl((X\times_KY)_{\Et},Rh_*p^{-1}F\bigr)
\cong\RGamma\bigl((U\times_KY)_{\Et},p^{-1}F\bigr)
\cong\RGamma(U_{\Et},F)\kunotimes{\kunZn}
\RGamma(Y_{\Et},\underline{\kunZn})
$$

(using [lem-kun-leray-bdd] for $h$ and
[lem-kun-0f14b] for the pair $(Y,U)$). By
[lem-kun-bc-kunneth-compat], $\RGamma$ of the exchange
morphism is, under these identifications, the identity, hence an
isomorphism. This finishes the proof.
