+++
id = "def-trf-fixed-scheme"
kind = "definition"
title = "Fixed scheme of a correspondence"
order = 2087
uses = ["def-trf-coefficient-conventions", "def-trf-correspondence", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
and the coefficient
conventions, and let $c=(c_1,c_2):C\to X\times_sX$ be a
cohomological correspondence with
$s=\Spec k$. Let

$$
\Delta_X:X\longrightarrow X\times_sX
$$

be the diagonal. The *fixed scheme* is

$$
F=\operatorname{Fix}(c):=C\times_{X\times_sX,c,\Delta_X}X,
$$

the scheme-theoretic intersection of the image of $c$ with the
diagonal, with first projection $i_F:F\to C$ and second projection
$d:F\to X$, so that $c_1i_F=d=c_2i_F$. For $h:X\to X$ a
morphism,
$\operatorname{Fix}(h):= \operatorname{Fix}((\operatorname{id}_X,h))$ is the scheme-theoretic
equalizer of $h$ and the identity. We say that $F$ has
*finitely many open-and-closed components* when the set
$\pi_0(F)$ of open-and-closed connected components of $F$ is finite;
in that case

$$
F=\coprod_{\beta\in\pi_0(F)}\beta,
$$

with each $\beta$ an open-and-closed
subscheme of $F$.

*Recorded in advance* from chapter *The trace formula* of the source.
