+++
id = "def-amb-etale-compact-support"
kind = "definition"
title = "Compact supports on the ordinary etale category"
order = 1560
uses = ["def-weil-compactifications-refinements", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-extension-by-zero"]
+++
For a compactification
$c=(j,r)$ of $f:X\to S$ between Noetherian schemes,
define the ordinary etale compact-support candidate by

$$
Rf_!^c=Rr_*j_!:D(X_{\rm et},A)\longrightarrow D(S_{\rm et},A).
$$

Here $j_!$ is the etale
extension by zero,
and $Rr_*$ is the ordinary
derived direct image.
For a proper refinement take the comparison which is the
identity over $X$; the comparison lemma below proves
that these maps give a compactification-independent
functor, denoted $Rf_!$. This definition concerns
the etale category; it does not identify it with a
functor on the pro-etale category.
The notation refers to ordinary derived categories.
