+++
id = "sk-d-integral"
kind = "section"
title = "Borel–Moore sections and integration"
order = 2281
uses = ["sk-d-setup", "sk-d-six"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward"]
+++
*Definition (sketch).*

A Borel–Moore section on a geometric scheme $T$ is
$\alpha:A_T\to\omega_T$ in the derived category.
For proper $h:T\to T'$, define $h_*\alpha$ by

$$
A_{T'}\longrightarrow Rh_*A_T\xrightarrow{Rh_*\alpha}Rh_*\omega_T
\simeq Rh_!h^!\omega_{T'}\xrightarrow{\varepsilon_h^!}\omega_{T'}.
$$

If $T$ is proper over $s$, set $\int_T\alpha=(a_T)_*\alpha\in A$.

Uses: [sk-d-setup], [sk-d-six]
