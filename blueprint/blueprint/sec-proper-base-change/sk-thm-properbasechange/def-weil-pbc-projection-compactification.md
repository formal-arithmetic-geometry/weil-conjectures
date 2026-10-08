+++
id = "def-weil-pbc-projection-compactification"
kind = "definition"
title = "Chosen compactification and compact-support image"
order = 1268
lean = ["AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification"]
uses = ["def-nagata-compactification"]
+++
Let $f:X\to Y$ admit a chosen compactification

$$
X\xrightarrow{j}\overline X\xrightarrow{p}Y,
\qquad f=pj,
$$

with $j$ a quasi-compact open immersion and $p$ proper. For this datum set

$$
Rf_!^{(j,p)}E:=Rp_*j_!E.
$$

For proper $f$, its identity compactification is $(j,p)=(1_X,f)$.
