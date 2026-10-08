+++
id = "lem-exc-closed-lift-filtered"
kind = "lemma"
title = "The closed-lift indexing category is filtered"
order = 1839
uses = ["def-exc-ind-etale-closed-lift", "lem-weil-pbc-ind-etale-stability"]
+++
The category $\mathcal N_A(\overline C)$ of [def-exc-ind-etale-closed-lift]
is filtered.

## Proof

The factorization through $A$ is an object of
[def-exc-ind-etale-closed-lift]. Two objects have the common successor
$B\otimes_AB'$, with its multiplication map to $\overline C$. This is etale
of finite presentation, using base change and composition as in the
stability lemma for ind-etale algebras.

For parallel arrows $f,g:B\rightrightarrows B'$, quotient $B'$ by the
differences $f(b)-g(b)$. This is the pullback of the diagonal of
$\operatorname{Spec}B/A$ along
$(f,g):\operatorname{Spec}B'\to\operatorname{Spec}(B\otimes_AB)$. That
diagonal is open and closed, as proved in the same stability lemma; its
pullback is an idempotent localization of $B'$, hence still etale of finite
presentation over $A$. Its map to $\overline C$ exists because the parallel
arrows agree there. It equalizes the arrows and proves filteredness.
