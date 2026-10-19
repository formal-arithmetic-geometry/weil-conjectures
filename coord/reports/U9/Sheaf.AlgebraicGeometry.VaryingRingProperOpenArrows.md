## What changed

In `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`, proved
`moduleBetaInvApp_naturality` by transposing its naturality square, applying
naturality of the open unit, and then naturality of the inverse square comparison.
Retained the earlier proof of `moduleJ_congr` by equality substitution.

The direct proof initially reached deterministic kernel timeout while unfolding
`moduleSquareG` through the adjoint compositors. Its construction now comes from
`moduleSquareG_existsUnique`, a fully proved unique specification whose witness is
exactly the original explicit composite. The fully proved `moduleSquareG_eq`
recovers that formula. This prevents the costly unfolding while retaining equality
of the actual natural isomorphisms. The final module compiles in 4.0 seconds. Its unchanged direct importer,
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` (held by K9), compiles
against the sandbox in 4.1 seconds. No consumer adaptation is needed.

Existing signatures, visibility, and imports are unchanged. The existing definition
node records the equation API and the elementary proofs. Change record:
`coord/changes/U9-varying-ring-square-comparison.md`.

## Proved and sorry left

Closed 2 of the original 5 holes, both in namespace
`AlgebraicGeometry.ProEtale.VaryingRing`:
`moduleBetaInvApp_naturality` and `moduleJ_congr`.
Added 0 holes; split off 0 statements. The two new supporting theorems,
`moduleSquareG_existsUnique` and `moduleSquareG_eq`, are proved.

The 3 remaining holes are `moduleBetaInv_isIso`, `moduleJAdj_unit_isIso`, and
`moduleOpenToP_isIso`. Each belongs to
`def-sp-varying-ring-proper-open-arrows`; all retain their original statements and
complete natural-language proof docstrings.

The cartesian comparison still needs the section-normalized restriction/direct-image
comparison on the sequence site. The unit needs full faithfulness of the chosen
extension (equivalently, by the adjoint triple, of direct image along the open).
The clopen comparison needs the section product decomposition into the open image
and its complement, compatibly with the semilinear transitions. None is handed on
as a new statement or a new hole.

## No longer needed

None. Both public imports are needed by the unchanged definitions and signatures.
No imported module or node is withdrawn. The elementary naturality proof needs no
additional imports. The explicit square construction remains available through its
proved equation, so none of its dependencies is pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned node is a definition node whose original `proof` and `proof_deps`
were empty; the theorem plans were in the Lean docstrings. The retained report's
claim that naturality could not pass kernel conversion is resolved by the explicit
unique-equality specification and equation API for the square comparison.

The constant strict-tower unit theorem does not immediately prove the ordinary
varying-ring unit: a compatible evaluation/reflection argument still needs to be
supplied. The similarly named semilinear proper/open module imports this item's
consumer, so it cannot be imported here without a cycle. No statement was found
false. No other group's module is adapted.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
