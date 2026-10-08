+++
id = "def-pc-pic-sigma-functor"
kind = "definition"
title = "The normalized functor $\\operatorname{Pic}_{X/k,\\sigma}$"
order = 799
uses = ["def-pc-picard-presheaf", "def-pc-rational-point", "def-pc-subfunctor", "def-sc-picard-group"]
lean = ["AlgebraicGeometry.picardFunctorNormalized"]
+++
Let $k$ be a field, $X$ a scheme over $k$, and $\sigma\in X(k)$ a
$k$-rational point. For a scheme $T$
over $k$ put

$$
\operatorname{Pic}_{X/k,\sigma}(T):=\operatorname{Ker}\Bigl(\sigma_T^*:\operatorname{Pic}(X_T)
\longrightarrow\operatorname{Pic}(T)\Bigr),
$$

i.e. the set of isomorphism classes $[\mathcal L]$ for which
$\sigma_T^*\mathcal L$ is isomorphic to $\mathcal O_T$.
A trivialization is not part of an element of this kernel; when a
proof chooses one, that choice is auxiliary. Its value at
$T=\operatorname{Spec}(k)$ is computed in [lem-pc-sigma-k-points].
