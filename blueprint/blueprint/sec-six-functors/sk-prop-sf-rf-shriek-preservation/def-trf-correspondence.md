+++
id = "def-trf-correspondence"
kind = "definition"
title = "Cohomological correspondence"
order = 2086
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, put $s=\Spec k$, and let $X$ be
separated of finite type
over $k$. A *cohomological correspondence* consists of a
separated finite-type
scheme $C$ with a morphism

$$
c=(c_1,c_2):C\longrightarrow X\times_sX,
$$

and, for $K\in D^b_{ctf}(X,A)$, a morphism

$$
u:Lc_2^*K\longrightarrow Rc_1^!K
$$

in $D(C,A)$, where $Lc_2^*$ is the
derived pullback and
$Rc_1^!$ is the
exceptional inverse image
of [def-trf-admissibility]; $c_2$ is the ordinary pullback leg
and $c_1$ the exceptional leg. The correspondence is
*admissible* if $c_1$ and every base change of $c_1$ occurring
below are exceptionally admissible at $A$.

*Recorded in advance* from chapter *The trace formula* of the source.
