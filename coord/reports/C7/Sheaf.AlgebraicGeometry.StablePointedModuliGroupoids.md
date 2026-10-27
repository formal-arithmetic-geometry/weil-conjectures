## What changed

Replaced `AlgebraicGeometry.StablePointedModuli.pullback_properties` by a complete Lean
reduction. The stability conjunct uses the new generic labelled-stability base-change
statement. For genus, `pullbackLeftPullbackSndIso` identifies the two geometric fibres
over the same algebraically closed field, its `hom_snd` equation identifies their
structure maps, and the proved cohomology-dimension comparison transports `X.genus`.
All existing statements, definitions, public imports, and instances are unchanged.

Added `Sheaf.AlgebraicGeometry.StructureSheafCohomologyIso` with a proved numerical
invariance theorem. Its private helper upgrades the existing natural additive
module-cohomology/source-H comparison to a linear equivalence: naturality for
`smulHom` and the scalar-endomorphism theorem establish linearity. The existing
`finrankH_pullback_of_isIso`, the quasi-coherence of the structure sheaf, and
`pullbackObjUnitIso` then give the numerical invariance. This reuses the source proof
rather than duplicating its injective-resolution or affine cohomology theory.

Added `Sheaf.AlgebraicGeometry.StablePointedCurveBaseChange`, containing the remaining
stability statement, with its source and full transport proof in its docstring.
The two new imports and Mathlib pullback pasting are private proof imports of the item.
Updated its node's proof, proof_deps, and proof_origin and created the two new nodes.
No changes to another existing module or another module's node were necessary.

Validation: `lcompile.py --all` compiled all three delivered Lean files in import
order. StablePointedCurveBaseChange took 9.2 s, StructureSheafCohomologyIso 4.6 s,
and StablePointedModuliGroupoids 45.1 s. No compiler errors or linter warnings remain.

## Proved and sorry left

Closed the textual hole in `AlgebraicGeometry.StablePointedModuli.pullback_properties`
(node `def-sfb-stable-pointed-moduli-groupoids`) by a complete proof from a strictly
smaller stability statement and the independently proved genus comparison. This is
a decomposition, not a net hole reduction: one upper hole closed and one lower hole
added. Two textual holes remain across the delivery, versus two in the original item.

New proved theorem: `AlgebraicGeometry.finrank_structureSheafCohomology_iso`
(node `lem-sfb-structure-sheaf-cohomology-iso`), with no local sorry. Its private
`finrank_moduleCohomology_eq_finrankH` helper is also fully proved.

Every remaining sorry:

- `AlgebraicGeometry.AbelianLevelModuli.hom_operations` in the item, unchanged;
  node `def-sfb-stable-pointed-moduli-groupoids`. Its existing docstring specifies
  the identity and composition coherence argument for frames.
- `AlgebraicGeometry.isStablePointedCurve_baseChange` in the new stability module;
  node `lem-sfb-stable-pointed-curve-base-change`. This is only stability, without
  the moduli object, prescribed total genus, or cohomology-dimension conclusion.

No sorry was added inside a definition or a private declaration. The new numerical
comparison works for arbitrary fields, q = 0, empty schemes, and infinite-dimensional
cohomology (the conclusion uses finrank). The stability statement includes empty
bases, zero markings, arbitrary non-flat base changes, and reducible nodal fibres.
It preserves the normalization-point count, including both branches of self-nodes.

## No longer needed

None pruned. No existing imports were removed, and no existing declared dependency,
module, or node became unnecessary. The item's node had empty proof/proof_deps before
this delivery; there was no alternative declared proof route to discard. All newly
added proof imports are used. No unit statement or realized unit step was bypassed.

Searches found no stable-pointed base-change theorem in Mathlib or the project.
The existing SemistableMarkedBaseChange theorem concerns a different multipointed-pair
predicate. The existing ProjectiveBundleBaseChange theorem supplies the projectivity
part of the remaining stability argument. Mathlib searches for cohomology invariance
returned ringed-space and sheaf pullback infrastructure; the source library supplied
`finrankH_pullback_of_isIso`, used here through its proved scalar-compatible bridge.

## Where the brief, the DAG or earlier work was wrong

The assigned node is a definition node with empty proof and proof_deps. Its two
remaining obligations had complete proof descriptions in the module's docstrings,
rather than numbered node steps. The updated node now records the actual pullback
reduction. Neither original statement was found false. The original genus condition
uses module right-derived sections, while the ready-made isomorphism theorem uses
ordinary H; treating these encodings as definitionally equal would be incorrect.
The new proved linear comparison accounts for their scalar actions explicitly.

## New nodes

`lem-sfb-stable-pointed-curve-base-change`: the stability-only part of the original
pullback well-definedness obligation. It records projective-bundle base change,
geometric-fibre transport, markings, and normalized-component special-point bounds.
Its Lean declaration is `AlgebraicGeometry.isStablePointedCurve_baseChange` and is the
one new sorry.

`lem-sfb-structure-sheaf-cohomology-iso`: the proved numerical cohomology invariant
needed for the geometric-genus conjunct, with explicit structural scalar maps.
Its declaration is `AlgebraicGeometry.finrank_structureSheafCohomology_iso`. Both new
nodes inherit the item's chapter/unit and blueprint ancestor, record LeanSearch,
Loogle/LeanFinder and source-grep searches, and introduce no new definition.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
