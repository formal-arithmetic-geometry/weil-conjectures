## What changed

Proved `AlgebraicGeometry.Scheme.existsUnique_etaleModuleStalkSpecialization` in
`Sheaf.AlgebraicGeometry.EtaleModuleStalkSpecialization`, following the existing
pointed-neighbourhood germ construction. The structural-map equation defines the
projected target points. Cone naturality and `ΓSpecIso_inv_naturality` show that
they commute with pointed neighbourhood maps. Their germs therefore form a cocone.
`strictHenselization_properties` supplies the initial affine representative functor;
Mathlib's `Functor.Final.isColimitWhiskerEquiv` transports the stalk colimit to
its opposite. The colimit desc gives existence, its component equation gives the
specified germ formula, and its hom extensionality gives uniqueness.

All existing declaration signatures, definitions, docstrings, and imports are
preserved. No new modules or auxiliary statements are introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.existsUnique_etaleModuleStalkSpecialization`
(node `def-weil-pbc-etale-module-stalk-specialization`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. Split-offs: 0.
The specialization definition now chooses from the proved unique-existence theorem.

## No longer needed

None. The proof follows the original docstring's route, using the existing
strict-henselization and stalk declarations. No new proof imports were needed;
the existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The definition node has empty `proof` and `proof_deps`; its Lean docstring supplies
the intended construction, and that construction is implemented directly.
No mathematical correction or departure from the unit route was needed.
Searches through LeanFinder, Loogle, and grep found Mathlib's generic stalk
colimit API, but no pre-existing specialization theorem with this statement.
The source read was `literature/stacks-project/etale-cohomology.tex`,
`section-specialization`, which constructs specialization by sending each pointed
neighbourhood germ to the germ at its projected target point.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
