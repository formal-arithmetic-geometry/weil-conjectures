+++
id = "sk-lem-nagata-sketch-common"
kind = "section"
title = "Common modification"
order = 234
uses = ["sk-lem-nagata-sketch-blowups", "sk-lem-nagata-sketch-elimination"]
lean = ["AlgebraicGeometry.nonempty_commonModification"]
+++
*Lemma (sketch).*

Suppose $U\hookrightarrow X_1,X_2$ are open immersions of separated
finite-type $S$-schemes. There are $U$-admissible blow-ups
$X_i'\to X_i$ and open immersions $X_i'\hookrightarrow W$ covering
a separated finite-type $S$-scheme $W$, with the two copies of $U$
identified; see 0F3X.

## Proof

Take $X_{12}=\SIm(U\to X_1\times_SX_2)$. Its projections are
isomorphisms over $U$. Eliminate indeterminacy for both projections,
refine the two strict transforms by blowing up the product of their
pulled-back centres, and extend this refinement to the two ambient
schemes. Glue the resulting opens along this common transform.
The overlap map to $X_1'\times_SX_2'$ is an immersion and is proper:
its composite to $X_1\times_SX_2$ is proper, while the new product
is separated over the old one. Thus the overlap map is closed. The diagonal criterion then gives separatedness of $W$.

Uses: [sk-lem-nagata-sketch-blowups], [sk-lem-nagata-sketch-elimination]
