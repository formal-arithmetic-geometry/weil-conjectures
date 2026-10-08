+++
id = "sk-d-six"
kind = "section"
title = "The geometric operation package"
order = 2268
uses = ["sk-d-setup"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations"]
+++
*Definition (sketch).*

On the geometric categories, a package consists of the
ordinary functors

$$
f^*,\quad Rf_*,\quad Rf_!,\quad f^!,\quad\otimes_A^{\mathrm L},\quad\RHom_A,
$$

with $f^*\dashv Rf_*$ and $Rf_!\dashv f^!$, their units, counits and
composition identities, projection formulas, $!$-base change, proper base
change, exceptional exchange maps, and tensor symmetries with Koszul signs.
Here $f^*$ and $f^!$ already denote derived functors.
Include constructible finiteness, open–closed localization, open-immersion
purity, the closed-immersion unit $1\simeq Ri^!Ri_*$, and
$Rf_*=Rf_!$ for proper $f$. Put

$$
\begin{gathered}
\omega_X=a_X^!A,\qquad D_XK=\RHom_A(K,\omega_X),\\
R\Gamma_c(X,K)=Ra_{X!}K,\qquad
M\boxt N=p_X^*M\otimes_A^{\mathrm L}p_Y^*N.
\end{gathered}
$$

Its duality clause is invertibility of the evaluation-adjoint map
$K\to D_XD_XK$.
The constructible comparison with the small étale site is included.
Coherence always means equality of component morphisms in ordinary categories.
This specifies the required data; their geometric realization is quoted
separately in the Six operations and duality node.
Dualizing composition $f^!\omega_Y\simeq\omega_X$ and perfectness of
compact cohomology and geometric stalks are consequences explained there.
Product comparison maps are constructed from these data; their invertibility
is not part of the specification here, but is available as the imported
[sk-thm-sf-kunneth-verdier].

Uses: [sk-d-setup]
