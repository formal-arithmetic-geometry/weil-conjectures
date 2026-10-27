## What changed

Proved `AlgebraicGeometry.Etale.isIso_projectionMap_coefficientExtensionRing` by
specializing the already proved
`AlgebraicGeometry.Etale.sf_finite_etale_projection_formula` to
`finiteCoefficientProjectionCompactification D f`. The latter theorem already gives
both bounded-below endpoint assertions and invertibility of the same canonical
projection transformation. Its `sfEtaleProjection` wrapper unfolds definitionally.
The supplied Tor interval gives the required existential interval after discarding
only the ordering proof. All constructibility and boundedness hypotheses pass
unchanged. Naturality is inherited from the identical bifunctor transformation.

Replaced the private proof import of `FiniteCompactProjectionFormula` with
`SfFiniteEtaleProjectionFormula`, and updated the existing node's proof,
proof dependencies and proof origin to this existing same-unit theorem. Every
public import, declaration signature and definition body is preserved. The helper
compactification and all geometric and coefficient hypotheses are unchanged.

Change record: `coord/changes/V1-finite-coefficient-etale-projection-proof-context.md`.

Added local `CommRing.toRing` instance priority and local irreducibility attributes
for the three projection bifunctor/map definitions, following the proof context of
the existing specialization theorem. These attributes keep elaboration from
unfolding the derived projection construction and export no changes.

Validation: the final single-file compile through `lcompile.py` on the project
server passed without diagnostics in 14.8 seconds. The import-direction checker
accepted the new proof import. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Etale.isIso_projectionMap_coefficientExtensionRing`
(node `thm-sf-pf-finite`). Proved 1 of 1 original sorries.

No sorry remains in the item module. Added zero holes and split off zero lemmas.
The proof uses an existing proved library theorem; no new theorem, axiom or data
construction is introduced.

## No longer needed

Removed these direct private imports:

- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`;
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`;
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`;
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.

The proof no longer uses node `lem-weil-finite-compact-projection-formula` or its
module as its proof dependency: the existing small-etale theorem
`sk-thm-sf-pf-finite` already supplies the entire conclusion, including D-plus
membership, for an arbitrary compactification. The old node remains in the
statement's historical citation dependencies; neither it nor its module is
withdrawn, and no claim is made that other consumers no longer need it. No other
DAG dependencies are pruned. The same unit's projection theorem is retained and
used directly; no unit statement or proof step is removed.

## Where the brief, the DAG or earlier work was wrong

The inherited plan overlooked the proved theorem
`sf_finite_etale_projection_formula`, which is a direct match and avoids converting
set-sheaf constructibility into the module-sheaf predicate required by
`isIso_finiteCompactProjection`. This is a shorter specialization route with no
statement change.

The first local mirror compile failed because the mirrored Mathlib root object
was absent. The documented `LCOMPILE_NO_LOCAL=1` setting selected the project server
for subsequent checks. Early `simpa` attempts exceeded the single-file limit;
the final direct application and existing local opacity/instance conventions
compile within the unchanged 60-second limit. No launcher tool was changed.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
