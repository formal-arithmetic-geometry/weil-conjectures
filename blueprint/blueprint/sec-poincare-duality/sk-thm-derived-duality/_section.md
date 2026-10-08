+++
id = "sk-thm-derived-duality"
kind = "section"
title = "Degreewise duality over a field"
order = 2437
uses = ["sk-def-pairing", "sk-lem-finite", "sk-thm-sf-identification"]
+++
*Corollary (sketch).*

In the setting of [sk-def-set] and [sk-def-pairing], let $K$ be perfect over
$\Lambda_X$ and let $\Lambda$ be a field coefficient stage.
The derived pairing of [sk-thm-sf-identification] gives perfect pairings

$$
\langle-,-\rangle_i:H^i_c(X,K)\times H^{2d-i}\bigl(X,K^\vee(d)\bigr)
\longrightarrow\Lambda.
$$

The line-valued form takes values in $\Lambda(-d)$; for proper $X$
the same holds with $H_c$ replaced by $H$.
(Blueprint 15, prop:pod-degree-of-the-pairing,
thm:pod-degreewise-perfectness-over-a-field.)

## Proof

Over a field stage a bounded complex of finite-dimensional spaces
splits as $\bigoplus_jH^j(C)[-j]$, so
$H^{-i}(C^\vee)\cong H^i(C)^\vee$
(lem:pod-cohomology-of-dual-over-field).
Apply this to the perfect point complexes of [sk-lem-finite] and
the derived isomorphism of [sk-thm-sf-identification].
Eliminating the twist through
$\Lambda(d)\otimes_\Lambda\Lambda(-d)\cong\Lambda$ gives the
line-valued form. For proper $X$, $Ra_{X!}\cong Ra_{X*}$, so
$H_c$ may be replaced by $H$.

Uses: [sk-def-pairing], [sk-lem-finite], [sk-thm-sf-identification]
