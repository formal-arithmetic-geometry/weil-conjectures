+++
id = "lemma-weil-pbc-target-locality"
kind = "lemma"
title = "Target locality"
order = 1190
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-property", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-qcqs-higher-direct-image", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
For proper $f:X\to Y$, the property $\mathsf{PBC}(f)$ is local for the etale
topology on $Y$.

## Proof

For an etale $V\to Y$ and a torsion sheaf $F$, sections of $R^qf_*F$ on $V$
are the sheafification of $U\mapsto H^q(X\times_YU,F|)$ over etale
$U\to V$. This description is functorial in $V$ and commutes with further
etale localization. Therefore an exchange map is an isomorphism if and
only if it is so after an etale cover of $Y$ (and its pullback cover on
$Y'$), because geometric stalks form a conservative family. The section
description is the content located at Tag `03Q8`.

## Detailed form

For proper $f:X\to Y$, the assertion $\mathrm{PBC}(f)$ of
[def-weil-pbc-property] is local on $Y$ for the etale topology. More
precisely, after an etale covering $\coprod_iV_i\to Y$, the exchange map is an
isomorphism if and only if its pullback over every $V_i$ is an isomorphism.

## Proof

By the quasi-compact quasi-separated description of higher direct image, the
restriction of $R^qf_*F$ to $V$ is the sheafification of $U\mapsto
H^q(X\times_YU,F|)$, compatible with further etale restriction and with the
canonical exchange morphism of [def-weil-pbc-derived-exchange]. Hence the
exchange map is an isomorphism if and only if it is so on the stalks over an
etale cover, and geometric stalks are conservative.
