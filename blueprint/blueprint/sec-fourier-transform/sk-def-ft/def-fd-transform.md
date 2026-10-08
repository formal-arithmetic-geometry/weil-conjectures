+++
id = "def-fd-transform"
kind = "definition"
title = "The Fourier–Deligne transform"
order = 2693
lean = ["AlgebraicGeometry.Etale.fourierTransform"]
uses = ["def-fd-kernel", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions"]
+++
For $K\in D^b_c(V,E)$, $V_0\to S_0$ being the rank-$r$ vector
bundle of [def-fd-kernel], the *Fourier–Deligne transform*
of $K$ is

$$
\operatorname{FT}_\psi(K):=p_{2,!}\bigl(p_1^*K\otimes^L_E\mathcal K_\psi\bigr)[r],
\qquad p_1:V\times_SV^\vee\to V,\ p_2:V\times_SV^\vee\to V^\vee,
$$

in Laumon's normalization (the shift $[r]$ – the relative dimension
of $V_0/S_0$ – is part of the definition; it is the
normalization for which the transform of a perverse object is
perverse, and for which the inversion formula below holds without an
additional shift, up to the twist $(-r)$). It is an exact
triangulated functor on the ambient derived categories; on the bounded
constructible domains its well-definedness is asserted in the
well-definedness theorem below.
