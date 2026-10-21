## What changed

Replaced the proof hole in `CategoryTheory.kInjectiveHom_scalar_telescope` without
changing its statement or the three tower/scalar definitions. Added private proved
helpers for resolution scalar naturality, postcomposition of Hom homotopies, scalar
postcomposition, and leg-compatible comparison of sequential colimits after localization.
The last helper uses the existing general telescope comparison and an isomorphism
of distinguished triangles, with identity on their first two vertices. Added the
private proof import `WeilConjectures.Algebra.Homology.HomComplexComponents` and removed
the unused public import `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
Updated the node proof to record this triangle comparison and the projections API.
Change record: `coord/changes/kinjective-hom-scalar-telescope-proof-imports.md`.
The downstream check reports zero consumer modules, so no adaptations are needed.

## Proved and sorry left

The proof replaces the sole original hole, `CategoryTheory.kInjectiveHom_scalar_telescope`
(node `lem-sfb-kinjective-hom-scalar-telescope`). One hole closed; zero holes added
or split off. There are zero `sorry`s in the delivered module.
Full single-file Lean compilation passed in 48.0 seconds. The delivery compile
and axiom probe also passed after the style repairs; preflight requested the
public-import change record now included in this packet.

## No longer needed

Removed the unused import `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the
statement expresses I, η and hI directly, and no declaration of that module is used.
Its underlying node `def-pur-derived-internal-hom` remains a conceptual statement
dependency; this delivery does not withdraw it or claim it is unused by other parents.
The explicit triangular chain isomorphism
between telescope cones is replaced by Mathlib's isomorphism of distinguished triangles;
the existing telescope comparison remains needed. No other original import is removed.

## Where the brief, the DAG or earlier work was wrong

The retained attempt had a misplaced docstring between declaration options and used
`neg_smul` where the sign is a unit; repaired the option order and used `Units.neg_smul`.
Removed its leftover `trace_state` debugging command. Generalized the private
projection equation to specify both degrees, so the mixed terms use the same index
without dependent rewrites. Applied a proved generic additive cancellation identity
and protected the internal-Hom definitions and private homotopy constructor from
unnecessary unfolding. No mathematical error found. The plan's explicit cone
comparison can be shortened:
the telescope comparison already supplies its distinguished triangle and preservation
of the coproduct cocone. Equality of the localized transition maps therefore gives
equality of the localized telescope maps, and the identity square extends to a triangle
isomorphism. Its second square gives the equality on all colimit legs.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
