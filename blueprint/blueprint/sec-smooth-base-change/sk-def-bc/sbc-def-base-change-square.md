+++
id = "sbc-def-base-change-square"
kind = "definition"
title = "Base-change square"
order = 1366
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-scheme-conventions"]
+++
A *base-change square* is a diagram of schemes

$$
\begin{array}{ccc}
X & \xleftarrow{\;h\;} & Y\\
f\big\downarrow & & \big\downarrow e\\
S & \xleftarrow{\;g\;} & T
\end{array}
\qquad (Y=X\times_S T)
$$

together with the chosen Cartesian identification
$Y\cong X\times_ST$ of
the Cartesian square of
the proper-base-change chapter, so that $f\circ h=g\circ e$; here $f:X\to S$ and
$g:T\to S$ are the two morphisms to the base $S$ (the vertical and the
horizontal side, respectively), and $h:Y\to X$, $e:Y\to T$ the
projections. The chosen identification gives the canonical isomorphism

$$
\theta_\square:h^{-1}f^{-1}\xrightarrow{\ \sim\ }e^{-1}g^{-1}
$$

of inverse-image functors, compatible with identity and pasted
squares, as in [def-weil-pbc-cartesian-square].
