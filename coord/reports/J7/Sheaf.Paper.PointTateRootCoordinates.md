## What changed

Completed the existing sandbox draft of `WeilConjectures.point_tate_root_coordinates` in
`Sheaf.Paper.PointTateRootCoordinates`, preserving its statement and all three public
helper definitions verbatim. The proof constructs compatible primitive roots, the finite
root coordinates, their inverse-limit coordinates, the normalized completed and finite
integral coordinates, and every signed tensor/Hom coordinate. Proved private helpers
record the section formulas and the inverse identities.

The proof reuses the proved explicit constructions behind `CompatiblePrimitiveRoots`,
`PurTwistRootLocalModels` and `PurTwistIntegralLocalModels`. Scalar extension of the unit
and the quotient adjunction give the prescribed generators, rather than an arbitrary
trivialization. Evaluation on the positive generator gives the negative coordinates.
The existing connected coefficient comparison supplies the terminal ring coordinates.
The DAG now also names `lem-pur-inverse-image-scalar-comparison`, whose scalar
adjunction and unit formula are used in the finite quotient normalization.

## Proved and sorry left

Closed: `WeilConjectures.point_tate_root_coordinates` (one original hole).
Added: none. Remaining in the item: none. No statements were split off.

## No longer needed

Removed direct proof imports:

- `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `Sheaf.Paper.PurTwistSheafLocallyFree`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.

The explicit constant-root sheafification comparison supplies the finite labels, so this
proof does not invoke `lem-pur-proetale-finite-constant-sections`. The completed and finite
integral comparisons come directly from the proved local-model constructions, so it does
not invoke `lem-pur-twist-sheaf-locally-free`. These two obsolete top-level `tool_uses`
approvals are removed, in their original order. Tensor/Hom APIs are available through the
retained statement imports and scalar comparison imports. Every public import is retained.

No module is withdrawn, and no transitive dependency used by another declaration is
claimed to be globally pruned. The unit statement and its route are retained.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics is valid. The retained sandbox draft required explicit ring-hom
coercions and sheafification comparison reductions against the current published build.
This session resumed the proof already present in the assigned sandbox; it did not
construct that draft from scratch. Existing proved local-model implementation lemmas
already provide the finite root isomorphisms, the compatible limit basis, the completed
integral comparison and the finite quotient comparison. Reusing those constructions
avoids repeating their split-polynomial, completion and quotient-kernel arguments.
The finite quotient's normalization follows from the units of the two scalar-extension
adjunctions and uniqueness of a left adjoint.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
