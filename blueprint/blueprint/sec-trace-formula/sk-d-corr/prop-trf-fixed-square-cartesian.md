+++
id = "prop-trf-fixed-square-cartesian"
kind = "theorem"
title = "The fixed square is Cartesian"
order = 2279
tags = ["latex:proposition"]
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-fixed-scheme", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties", "thm-sf-comp-composition"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, put $s=\Spec k$, and let
$c=(c_1,c_2):C\to X\times_sX$ be a
cohomological correspondence with
fixed scheme
$F=\operatorname{Fix}(c)$ of [def-trf-fixed-scheme] and projections
$i_F:F\to C$, $d:F\to X$. Then the square

$$
\begin{array}{ccc}
F & \xrightarrow{i_F} & C\\
{\scriptstyle d}\downarrow & & \downarrow{\scriptstyle c}\\
X & \xrightarrow{\Delta_X} & X\times_sX
\end{array}
$$

is Cartesian, the composites
$c_1i_F$ and $c_2i_F$ both equal $d$, and the identity
$\Delta_Xd=ci_F$ holds. Moreover the composition law for the
exceptional inverse image gives

$$
Rd^!\xrightarrow{\ \sim\ }Ri_F^!Rc_1^!
$$

(the adjoint form of the composition law $R(c_1i_F)_!\cong Rc_{1!}Ri_{F!}$ of [thm-sf-comp-composition],
as $d=c_1i_F$); it is the only unconditional "!"-transport of the two
legs in the fixed square, see also the remark below.

## Proof

By [def-trf-fixed-scheme], $F$ is the fiber product
$C\times_{X\times_sX,c,\Delta_X}X$, which is precisely the assertion that
the square is Cartesian. The composites $c_1i_F$ and $c_2i_F$ are the
projections $p_1,p_2:X\times_sX\to X$ applied to the identity
$\Delta_Xd=ci_F$ of [def-trf-fixed-scheme], hence both equal $d$;
the identity $\Delta_Xd=ci_F$ is part of the fiber-product data. The
last displayed isomorphism is the composition law for the exceptional
inverse image of [def-trf-admissibility] applied to the equality
$d=c_1i_F$ in the form
$R(c_1i_F)^!=Ri_F^!Rc_1^!$.
