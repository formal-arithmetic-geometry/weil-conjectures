## What changed

Replaced the sole proof hole in
`AlgebraicGeometry.ProEtale.integral_ordinary_augmentation_milnor` while retaining its
signature verbatim. The proof uses a normalized strict inverse-limit cone and the
regular quotient tower comparison. The displayed ordinary augmentation remains the
first-vertex map throughout.

Added three intermediate modules under `lean/Sheaf/`: the general normalized
strict-limit cone, its transport across an additive coefficient equivalence and a
positive-tail identification, and the regular ordinary quotient tower comparison
(the remaining proof obligation).
The first reuses the existing generic K-injective Roos construction through a
private proof import. The last records the source library's packaged scalar-reduction cone API in
`Complete.AdicTower` and Mathlib's natural cone-to-cokernel quasi-isomorphism
as the proposed proof of the remaining pre-limit obligation.
A full draft of the quotient calculation was written from the cone-to-cokernel
API and the principal-reduction comparisons, but kernel checking of the concrete
sheaf tensor comparisons exceeded the per-file limit. Its strictly simpler
pre-limit statement is therefore left as the sole named intermediate obligation.
The new quotient statement uses the same sheaf instances as the assigned theorem;
no shared instance or existing declaration is changed. No existing module besides
the assigned item, and no existing definition or statement, was changed.

The boundary square has a shorter proof than the planned signed-cone calculation.
The constant diagonal has a projection as retraction, so its Milnor boundary
vanishes and its difference map is epic. The map between products commutes with
the difference maps. Cancelling the epic constant difference map against the
second triangle's zero middle/last composite proves the other boundary composite
vanishes. Thus this proves the boundary square for the specified augmentation,
without replacing that map by a choice of triangle lift.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.integral_ordinary_augmentation_milnor`
(node `lem-sfb-integral-ordinary-augmentation-milnor`).

The general normalized-limit auxiliary declarations are proved:

- `CategoryTheory.normalizedStrictLimitBase`
  (`lem-sfb-normalized-strict-limit-base`);
- `CategoryTheory.normalizedStrictLimitCone`
  (`lem-sfb-normalized-strict-limit-cone`);

The sole remaining `sorry` is
`AlgebraicGeometry.ProEtale.integral_regular_quotient_tower`
(`lem-sfb-integral-regular-quotient-tower`). It asserts only the natural identification
of regular quotient levels and their augmentation, with no inverse limit, etaZ,
Milnor triangle, or boundary square. Its docstring gives the construction and proof.

Holes closed: 1. Holes added: 1. Holes remaining in the assigned module: 0;
holes remaining in all four delivered Lean modules: 1. This is a decomposition,
not a net proof-hole reduction.
The original theorem signature was compared verbatim with the repository version.
The boundary argument and ordinary adjunction normalization are proved first as
private lemmas over abstract triangulated and abelian categories, then applied to
the concrete sheaf category. A private proved product-instance lemma shares that
construction. This avoids repeated normalization of the large concrete instances.
The final four-file compile passes; the assigned module's kernel check takes
14.6 seconds. The delivery tool records final compilation and preflight verification.

## No longer needed

Removed the original node's proof-dependency edges to
`lem-weil-proetale-countable-products-exact` and
`lem-weil-strict-roos-comparison`. Neither corresponding module is imported by this
proof. K-injective tower evaluations give the product triangle without exact
ordinary products, and normalization of its first arrow suffices because of the
split constant-tower argument for the boundary. These are dependency-edge removals;
no module is withdrawn or claimed to be globally unused.

The draft-only import `Sheaf.CategoryTheory.StrictDerivedLimitMilnor` was removed
from the new base module: its unnormalized conclusion does not provide the needed
ordinary projection formula, and the fully proved underlying generic construction
is imported directly instead. The quotient and tail modules publicly import the
tower API because their statements use its positive-tail indexing functor
`addOpFunctor`. Other extra triangle and cone-construction tools are private proof
imports. The quotient helper statement imports only its interface dependencies.
Draft proof imports of `Complete.AdicTower`, `ReductionCone`, `QuotPowTriangle`,
and the cone-to-cokernel API were removed from the final statement module.

The assigned module's redundant private `HomotopyLimit.Tower` import was removed;
the new cone helper already publicly supplies this API. All original public
imports of the assigned module remain verbatim. No declaration
or module under `lean/WeilConjectures/` is removed or changed. The unit statement and
its prescribed route through ordinary regular quotients and derived completion
are retained.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned use of exact countable products and the
explicit signed strict-Roos comparison was stronger than needed. The existing
`reductionConeIso` and its packaged transition and augmentation equations, together
with the natural cone-to-cokernel API, give the proposed proof of the regular
quotient identification, including transition compatibility and the augmentation;
that Lean obligation remains explicit in this delivery.
The generic natural Roos proof already available in the library supplies the
normalized inverse-limit cone after cancelling its resolution comparisons.

The boundary square does not require identifying a noncanonical morphism from all
of its projections: it follows from the split constant tower as described above.
A positive-tail identification is enough; the finite-tail homotopy-limit theorem
extends it across the initial principal quotient. All arguments cover the zero
complex and empty scheme and impose no boundedness or K-flatness on P.

## New nodes

`lem-sfb-normalized-strict-limit-base` records the ordinary projection normalization
of the existing generic K-injective Roos construction. Its proof is complete.

`lem-sfb-normalized-strict-limit-cone` records transport by the exact coefficient
equivalence and extension from a positive tail, with normalization for every map
into the ordinary termwise inverse limit. Its proof is complete.

`lem-sfb-integral-regular-quotient-tower` records the natural principal scalar
cone-to-cokernel comparison before taking any inverse limit. It is the sole
remaining named proof obligation, with its source and complete natural-language
proof in its docstring.

Each node is attached to its own new module and sourced to Stacks 0940/0941 or
099M. The assigned node's proof, proof dependencies, and proof origin were updated
to match the Lean argument. There are no change records: no existing interface,
shared definition, or other existing module was changed.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
