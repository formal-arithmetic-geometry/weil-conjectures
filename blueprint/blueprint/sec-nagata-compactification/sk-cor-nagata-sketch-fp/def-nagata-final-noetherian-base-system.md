+++
id = "def-nagata-final-noetherian-base-system"
kind = "definition"
title = "Noetherian base system used in the final assembly"
order = 371
uses = ["def-nagata-glued-limit-comparison", "def-nagata-noetherian-inverse-system"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

Define

$$
\mathsf N_f=\mathsf N(S)
=(I_S,(S_\lambda)_\lambda,(t_{\mu\lambda})_{\lambda\leq\mu})
$$

and retain the constructed limit comparison
$\kappa_S\colon S\to\varprojlim_\lambda S_\lambda$.
