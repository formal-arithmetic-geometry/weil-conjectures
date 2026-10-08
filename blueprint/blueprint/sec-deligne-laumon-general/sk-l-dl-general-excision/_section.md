+++
id = "sk-l-dl-general-excision"
kind = "section"
title = "Open–closed reduction"
order = 2814
lean = ["AlgebraicGeometry.HasDirectImageWeightBound.of_openClosed"]
uses = ["sk-d-dl-general-weights", "sk-prop-sf-open-closed-triangle"]
+++
*Lemma (sketch).*

Let $j_0:U_0\hookrightarrow X_0$ be open with closed complement
$i_0:Z_0\hookrightarrow X_0$. If the direct-image assertion holds for
$f_0j_0$ and $f_0i_0$, it holds for $f_0$.

## Proof

Apply $Rf_{0!}$ to
$j_{0!}j_0^*K\to K\to i_{0*}i_0^*K\xrightarrow{+1}$.
In each degree the middle term has a subobject that is a quotient of
the open term, with quotient a subobject of the closed term.
Both have the required bound. The same argument on
the target, using compact-support base change, allows a finite
stratification of the base. Filtrations of the coefficient sheaf are
handled by the corresponding long exact sequences.

Uses: [sk-d-dl-general-weights], [sk-prop-sf-open-closed-triangle]
