+++
id = "def-trf-trace-class"
kind = "definition"
title = "Trace-class notation conditional on its construction"
order = 2309
uses = ["def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-trace-class-source", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
That this construction is unconditional is
[prop-trf-trace-class-unconditional].

Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, $s=\Spec k$, and let
$c=(c_1,c_2):C\to X\times_sX$ be an admissible
cohomological correspondence with
fixed scheme
$F=\operatorname{Fix}(c)$ of [def-trf-fixed-scheme]. A
correspondence $u:Lc_2^*K\to Rc_1^!K$ is equivalently a section
$\widetilde u:A_C\to\mathcal H_c(K)$ of the
trace-class source of
[def-trf-trace-class-source]; its *Verdier trace class* is

$$
\operatorname{Tr}_c(u):
A\xrightarrow{\widetilde u}
R\Gamma(C,\mathcal H_c(K))
\xrightarrow{\mathfrak t_{c,K}}
R\Gamma(F,\omega_{F,A})
$$

where the displayed morphism is identified with an element of
$\operatorname{Hom}_{D(F,A)}(A_F,\omega_{F,A})$ by the
global-sections adjunction, and $\mathfrak t_{c,K}$ is
the morphism of [lem-trf-trace-map-from-external-duality]. Here
$\omega_{F,A}$ is the
dualizing complex of
[def-trf-dualizing-complex].
