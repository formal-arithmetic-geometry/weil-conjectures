+++
id = "prop-trf-trace-class-unconditional"
kind = "theorem"
title = "The Verdier trace class is unconditionally defined"
order = 2324
tags = ["latex:proposition"]
uses = ["def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-supported-pairing", "def-trf-trace-class", "def-trf-trace-class-source", "lem-trf-trace-map-from-external-duality", "thm-trf-kunneth-verdier", "thm-trf-verdier-duality"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, put $s=\Spec k$, let
$c=(c_1,c_2):C\to X\times_sX$ be an
admissible cohomological
correspondence with fixed scheme
$F=\operatorname{Fix}(c)$, and let $K\in D^b_{ctf}(X,A)$. Then the
Verdier trace class
$\operatorname{Tr}_c(u)$ of [def-trf-trace-class] is defined for
every correspondence $u:Lc_2^*K\to Rc_1^!K$, under no hypothesis
beyond the admissibility of $c$ and $K\in D^b_{ctf}(X,A)$.

## Proof

By [def-trf-trace-class] the trace class is the composite

$$
A\xrightarrow{\ \widetilde u\ }
R\Gamma(C,\mathcal H_c(K))\xrightarrow{\ \mathfrak t_{c,K}\ }
R\Gamma(F,\omega_{F,A})
$$

followed by the identification of the target with
$\operatorname{Hom}_{D(F,A)}(A_F,\omega_{F,A})$, where
$A=A_{E,n}$ is the coefficient ring of
[def-trf-coefficient-conventions].
The first arrow is the mate of $u$ under the tensor–internal-Hom
adjunction of [def-trf-trace-class-source], which is defined for
every correspondence $u$ and needs no hypothesis. The second arrow
is the morphism $\mathfrak t_{c,K}$ of
[lem-trf-trace-map-from-external-duality]: its construction
applies the external duality
[thm-trf-verdier-duality] — itself a consequence of the
Kunneth–Verdier chain [thm-trf-kunneth-verdier] — to the
external product of the dualizing data of
[def-trf-dualizing-complex], and its inverse comparisons are the
ones supplied by the supported pairing of
[def-trf-supported-pairing]. Both arrows therefore exist as soon
as the correspondence $c$ is admissible in the sense of
[def-trf-correspondence] and the fixed scheme is the one of
[def-trf-fixed-scheme], which is the assertion.
