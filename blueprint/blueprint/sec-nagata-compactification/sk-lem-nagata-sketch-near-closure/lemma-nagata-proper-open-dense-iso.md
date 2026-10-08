+++
id = "lemma-nagata-proper-open-dense-iso"
kind = "lemma"
title = "A proper dense open immersion is an isomorphism"
order = 256
+++
**Status.** Bypassed by the formalized route: the two-open theorem is
concluded by
`AlgebraicGeometry.HasCompactification.of_two_open_cover`, which
never needs this criterion.

Let $q\colon Z\to X$ be both proper and an open immersion. If its image
contains a scheme-theoretically dense open subscheme of $X$, then $q$ is an
isomorphism.

## Proof

A proper immersion is a closed immersion. Thus the image is both open and
closed. Its closed complement has structure sheaf supported away from the
dense open; scheme-theoretic density forces that complement to be empty.
