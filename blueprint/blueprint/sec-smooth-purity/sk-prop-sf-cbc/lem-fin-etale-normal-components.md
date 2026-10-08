+++
id = "lem-fin-etale-normal-components"
kind = "lemma"
title = "Normal components after etale pullback"
order = 1605
uses = ["def-sbc-normal-dominant-galois", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-noetherian-finite-components"]
+++
Let $W\to Y$ be etale with $W$ Noetherian and $Y$
normal integral.
Then $W$ is a finite disjoint union of open-and-closed
normal integral schemes.

## Proof

The commutative-algebra ascent of normality under etale
ring maps shows that every local ring of $W$ is a normal
domain; this is the etale case of
[Stacks
Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C). Applied to the affine ring maps in
[def-weil-pbc-scheme-conventions], it proves the stated
local-ring property. In particular $W$ is reduced.
Its finitely many irreducible components, supplied by
[lem-weil-pbc-noetherian-finite-components], are disjoint:
a point on two components would give two minimal primes
in its local domain. Each component is closed and has
closed complement, hence is also open. Its local rings
are those of $W$, so the component is normal integral
in the sense of [def-sbc-normal-dominant-galois].
