+++
id = "def-pur-scheme-geometric-frobenius"
kind = "definition"
title = "Scheme and geometric Frobenius of the purity datum"
order = 2235
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-trf-scheme-frobenius", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "prop-trf-frobenius-factorization", "prop-trf-scheme-galois-comparison", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
global finite-field datum
$(p,a,q,k_0,k)$, and let $f_0:X_0\to Y_0$ be a
finite-type separated
morphism of $k_0$-schemes whose base change to $k$ is smooth of relative
dimension $d$. Put $X=X_0\times_{k_0}k$, $Y=Y_0\times_{k_0}k$, and
let $f:X\to Y$ be the base change of $f_0$. With
$\gamma=\operatorname{Frob}_q=\sigma^{-1}$ in the
geometric Frobenius convention of
the framework chapter, write

$$
g_{X,\gamma}=\operatorname{id}_{X_0}\times\Spec(\gamma),\
g_{Y,\gamma}=\operatorname{id}_{Y_0}\times\Spec(\gamma),
$$

for the semilinear (geometric-Galois) automorphisms, and let $\Phi_X$,
$\Phi_Y$ be the $q$-power scheme Frobenius endomorphisms of $X_0$
resp. $Y_0$, base-changed to $X$ and $Y$, in the notation of
[def-trf-scheme-frobenius]; they form the following commutative squares

$$
\begin{array}{ccc}
X & \xrightarrow{\ g_{X,\gamma}\ } & X\\
f\downarrow & & \downarrow f\\
Y & \xrightarrow{\ g_{Y,\gamma}\ } & Y,
\end{array}
\qquad
\begin{array}{ccc}
X & \xrightarrow{\ \Phi_X\ } & X\\
f\downarrow & & \downarrow f\\
Y & \xrightarrow{\ \Phi_Y\ } & Y,
\end{array}
$$

The first square is Cartesian, since its horizontal arrows are the
compatible semilinear automorphisms. The second is commutative by
the affine description of scheme Frobenius in
[def-trf-scheme-frobenius]; it is not asserted to be Cartesian.
The scheme-Frobenius forms below are transported from the first square
using the comparison isomorphisms, not by applying Cartesian base change
to the second square. The comparison
isomorphisms $\kappa_X,\kappa_Y$ are those of
[prop-trf-scheme-galois-comparison]: the absolute Frobenius
factorizes as

$$
\operatorname{Fr}^{(q)}_{Y/k}=g_{Y,\sigma}\Phi_Y=\Phi_Yg_{Y,\sigma}
$$

([prop-trf-frobenius-factorization], with $\sigma:z\mapsto z^q$ the
arithmetic Frobenius), so the scheme Frobenius and the geometric-Galois
automorphism $g_{Y,\gamma}=g_{Y,\sigma}^{-1}$ differ by the universal
homeomorphism $\operatorname{Fr}^{(q)}_{Y/k}$, under which the etale site
is invariant by [thm-weil-pbc-universal-homeomorphism-invariance].
The isomorphisms are compatible with the pullback-composition
identifications and with $f$:

$$
Lf^*\kappa_Y=\kappa_XLf^*.
$$
