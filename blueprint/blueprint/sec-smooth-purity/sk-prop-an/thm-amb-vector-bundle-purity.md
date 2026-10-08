+++
id = "thm-amb-vector-bundle-purity"
kind = "theorem"
title = "Vector-bundle purity before smooth orientation"
order = 1973
uses = ["cor-amb-affine-space-adjunction", "def-amb-vector-integration", "def-asd-vector-bundle-zero-section", "def-coefficient-twists-detailed", "def-weil-pbc-derived-categories", "lem-amb-etale-adjoint-locality", "lem-amb-proper-coproducts-projection", "lemma-weil-pbc-geometric-stalk-conservative", "thm-amb-etale-exceptional-adjoint"]
+++
Let $\pi:E\to S$ be a vector bundle of rank $d$
over a Noetherian scheme. For every complex $K$ of
etale $A$-modules on $S$, the adjoint of

$$
R\pi_!(\pi^*K(d)[2d])
\cong K\otimes_A^LR\pi_!A_E(d)[2d]
\xrightarrow{1\otimes t_\pi}K
$$

is an isomorphism

$$
\pi^*K(d)[2d]\xrightarrow{\sim}\pi^\times K.
$$

The notation refers to Tate twists, and vector-bundle integration.

## Proof

The vector bundle is compactifiable by its projective
completion. Thus its actual ambient adjoint exists by
[thm-amb-etale-exceptional-adjoint]. The projection
formula of [lem-amb-proper-coproducts-projection]
on this compactification defines the displayed
integration for every $K$, using the global map
of [def-amb-vector-integration].
Transpose it under the ambient adjunction.

Restrict to a trivializing open set of $S$.
The resulting map is the adjoint of the affine-space
counit. By
[lem-amb-etale-adjoint-locality], [cor-amb-affine-space-adjunction],
this map is the identity under the affine-space
identification of the right adjoint. Hence it is an
isomorphism on the inverse image of every trivializing
open set. These opens cover $E$, so
[lemma-weil-pbc-geometric-stalk-conservative] proves
that it is an isomorphism everywhere.
The construction used only the projective-line diagonal,
compact supports, and ordinary adjunctions; it did not
use general smooth purity, a localized top Chern class,
or frame independence in codimension greater than one.
