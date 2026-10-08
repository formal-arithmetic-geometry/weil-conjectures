+++
id = "lem-exc-etale-algebra-lift"
kind = "lemma"
title = "Etale algebras lift across an arbitrary quotient"
order = 1837
uses = ["def-exc-etale-algebra-lift", "def-weil-pbc-scheme-conventions", "lem-exc-etale-jacobian-presentation"]
+++
The algebra of [def-exc-etale-algebra-lift] is etale of finite presentation
over $A$, and its specified reduction
$B^{\mathrm{lift}}/IB^{\mathrm{lift}}\to\overline B$ is an isomorphism.
Hence every etale finite-presentation $A/I$-algebra has such a lift, with no
nilpotence assumption on $I$.

## Proof

For the algebra of [def-exc-etale-algebra-lift], the Jacobian determinant of
the $m+1$ relations in $m+1$ variables is $\Delta^2$: the last column has
only its last entry $\Delta$ nonzero. This determinant is a unit, since
$t\Delta=1$. Thus [lem-exc-etale-jacobian-presentation] proves etaleness.
Modulo $I$, the last variable is uniquely $\overline\Delta^{-1}$, giving the
asserted reduction isomorphism. Every etale $\overline B$ admits the
required presentation by the same lemma. This proves the lifting calculation
of [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
explicitly.
