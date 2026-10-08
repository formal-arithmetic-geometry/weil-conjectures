+++
id = "def-trf-karoubi-trace"
kind = "definition"
title = "Trace on a Karoubi summand"
order = 2397
uses = ["def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-weil-algebraically-closed-coefficients", "def-weil-finite-field-fiber", "def-weil-pbc-qbar-category"]
+++
Fix the global finite-field datum
and the coefficient
conventions. In the
common-stage
algebraically closed coefficient category of the framework chapter, an object
of $D^b_c(X,\Qlb)$ is represented by a finite-stage pair $(E,K_E)$
with $E/\Ql$ finite in $\Qlb$; the category is idempotent complete,
so no idempotent appears in the presentation (in the classical
presentation of the
$\Qlb$ coefficient category of
the proper-base-change chapter the object was a pair $((E,K_E),e)$ with $e^2=e$ in
the common-stage category). The *trace of an endomorphism $v$ on the
summand* $e$ of a perfect complex $P$ is the
categorical trace

$$
\operatorname{tr}_E\bigl(v\circ e\mid P\bigr),
$$

which depends only on the summand $(eP,ev)$: the decomposition
$P\simeq eP\oplus(1-e)P$ splits $v\circ e$ as $ev|eP$ on the
summand and $0$ on the complement.
