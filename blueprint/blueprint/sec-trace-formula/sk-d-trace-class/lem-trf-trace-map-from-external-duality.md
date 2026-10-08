+++
id = "lem-trf-trace-map-from-external-duality"
kind = "theorem"
title = "Trace morphism from external duality"
order = 2317
uses = ["def-trf-admissibility", "def-trf-dualizing-complex", "def-trf-external-product", "def-trf-fixed-scheme", "def-trf-trace-class-source", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "thm-trf-dualizing-complex-composition", "thm-trf-fixed-point-base-change", "thm-trf-verdier-duality"]
+++
Let
$F=\operatorname{Fix}(c)$, $i_F:F\to C$, and $d:F\to X$ be the
fixed-square maps, all with the
exceptional admissibility required
below. There is then a morphism

$$
\mathfrak t_{c,K}:R\Gamma(C,\mathcal H_c(K))
\longrightarrow R\Gamma(F,\omega_{F,A}),
$$

where the source and target use the
trace-class source and
dualizing complex.

## Proof

Let $\Delta:X\to X\times_sX$ be the diagonal. The external product
of [def-trf-external-product] pulls back to
$K\otimes_A^LD_XK$. The definition of the Verdier dual in
[def-trf-dualizing-complex], evaluation for internal Hom, and the
symmetry of the derived tensor in [def-weil-derived-tensor] give
$K\otimes_A^LD_XK\to\omega_{X,A}$.
By the pullback/direct-image adjunction of
[def-weil-derived-pullback-tensor-hom], its adjoint is

$$
e_K:K\boxtimes_A^LD_XK\longrightarrow R\Delta_*\omega_{X,A}.
$$

Assuming the comparison requested in [thm-trf-verdier-duality],
apply $Rc^!$ to this map and form

$$
\begin{aligned}
\mathcal H_c(K)&\xrightarrow{\sim}Rc^!(K\boxtimes_A^LD_XK)\\
&\xrightarrow{Rc^!e_K}Rc^!R\Delta_*\omega_{X,A}\\
&\xrightarrow{\sim}Ri_{F*}Rd^!\omega_{X,A}\\
&\xrightarrow{\sim}Ri_{F*}\omega_{F,A}.
\end{aligned}
$$

The last two arrows are the exceptional form of fixed-square base
change in [thm-trf-fixed-point-base-change] and the composition
of dualizing complexes in [thm-trf-dualizing-complex-composition].
Taking derived global sections gives $\mathfrak t_{c,K}$.
Equivalently, adjunction along $i_F$ gives
$\theta_{c,K}:Li_F^*\mathcal H_c(K)\to\omega_{F,A}$.
Thus this objectwise map is a consequence of the external duality
[thm-trf-verdier-duality], which is proved; the construction is
unconditional.
