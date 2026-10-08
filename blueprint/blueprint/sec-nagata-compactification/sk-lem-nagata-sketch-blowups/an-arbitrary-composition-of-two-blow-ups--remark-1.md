+++
id = "an-arbitrary-composition-of-two-blow-ups--remark-1"
kind = "remark"
title = "Formalization route"
order = 129
+++
The formal statement
(`exists_finiteDegree_center_le_blowup`) recasts Tag 0803 purely
in ideal-sheaf terms: $Z'$ is replaced by a finite-type ideal sheaf
$\mathcal J$ on the blow-up and the conclusion is the inverse-image
equality $\mathcal L\cdot\mathcal O_{X'}=\mathcal I_E^d\cdot\mathcal J$ for
a finite-type $\mathcal L\subseteq\mathcal I^d$; no relative-Proj quotient
is formed, and the support bound is recovered downstream
(`coe_support_eq_of_comap_pow_mul`). The choice-packaged
[def-nagata-proj-closed-center-finite-degree] is replaced by the bare
existential.
