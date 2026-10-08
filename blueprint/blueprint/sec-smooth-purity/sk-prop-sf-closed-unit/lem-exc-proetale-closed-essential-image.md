+++
id = "lem-exc-proetale-closed-essential-image"
kind = "lemma"
title = "The essential image of closed direct image"
order = 1857
uses = ["def-weil-pbc-proetale-operations", "def-weil-pbc-scheme-conventions", "lem-exc-closed-localization", "lem-exc-open-closed-detection", "lem-exc-proetale-closed-fully-faithful", "prop-weil-pbc-proetale-constant-exact"]
+++
For a closed immersion $i:Z\hookrightarrow X$ with quasi-compact open
complement $j$, a pro-etale module sheaf $F$ lies in the image of $i_*$ if
and only if $j^*F=0$. For such a sheaf the canonical unit $F\to i_*i^*F$ is
an isomorphism.

## Proof

Evaluation on an object of the open complement gives $j^*i_*G=0$, by
[lem-exc-closed-localization], since its closed fibre is empty. Conversely
suppose $j^*F=0$ and consider the unit $\eta:F\to i_*i^*F$ of the pro-etale
operations. Its closed inverse image is an isomorphism: the triangle
identity says that $i^*\eta$, followed by the counit, is the identity, and
the counit is an isomorphism by [lem-exc-proetale-closed-fully-faithful].
Its open inverse image is the map between two zero sheaves. Both inverse
images are exact by the exactness of constant-coefficient pro-etale inverse
image, so the kernel and cokernel of $\eta$ have zero open and closed
inverse images. [lem-exc-open-closed-detection] makes them zero. This proves
the unit isomorphism and the essential-image assertion.
