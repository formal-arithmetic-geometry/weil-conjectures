## What changed

Proved both theorems in `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` using
Mathlib's total-right-derived universal property. No signatures or definitions change.

For the cocycle, `Functor.rightDerived_ext` reduces equality to the components after
precomposition with eta_hgf. The four assumed comparison equations, functoriality of
Rh, and naturality of kappa_hg identify both paths with the same triple composite.
For the unit theorem, the identity functor is a right derived functor of localization
itself (`Functor.isRightDerivedFunctor_of_inverts`). `Functor.rightDerivedUnique`
provides the two normalized identity comparisons. Naturality and their unit equations
then give both unit laws, again using `rightDerived_ext`.

The identity comparison construction is a proved local proposition inside the unit
proof; no new public declaration or arbitrary witness from an unproved existence
statement is introduced. Each theorem locally enables transparent definitional equality
for the termwise composite-functor identifications; no heartbeat or time limit increases.

Replaced the unused public composition-theorem import with direct Mathlib statement
imports. Added one private Mathlib proof import and removed the four unused private
resolution imports. Updated the existing node's proof, proof dependencies, proof origin,
and obsolete tool-use list to agree with the shorter categorical argument. The node's
statement, statement dependencies, Lean attachment and unit realization stay unchanged.
Change record: `coord/changes/ringed-derived-composition-cocycle-imports.md`.

Validation: the file compiled cleanly through lcompile.py in 14.1 seconds with the
smaller import set. The delivery tool checks the final source and axioms as well.
The downstream tool and direct source search found no external Lean consumers.

## Proved and sorry left

Closed 2 of 2 original holes:

- `CategoryTheory.ringedDerivedComposition_cocycle`.
- `CategoryTheory.ringedDerivedComposition_units`.

Both belong to `lem-pur-ringed-derived-composition-cocycle`.
Added 0 holes; split off 0 statements; 0 holes remain in the delivery.
These are complete proofs, not a decomposition into further unproved lemmas.

## No longer needed

Removed these imports from this module:

- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` (previously public).
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`.

Removed all five old proof dependencies and their corresponding obsolete top-level
tool-use approvals:

- `prop-pur-kinjective-resolutions-exist`: no resolutions are chosen.
- `lem-weil-pbc-kinjective-hom-derived`: no Hom comparison or homotopy lift is needed.
- `lem-sf-kinjective-derived-map-computation`: naturality suffices instead of computing
  derived morphisms using resolutions.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: the theorem's normalization
  equations are already hypotheses. The existence/computation theorem is not used in
  the proof, but remains a statement dependency naming the comparison under study.
- `def-weil-pbc-ringed-topos-morphism`: it is needed for the theorem signatures, so its
  public import and statement dependency remain, but the categorical proof does not use
  its module-action or geometric-adjunction fields.

The replacement proof has no further project proof dependencies: its steps are direct
applications of Mathlib to the given universal properties and normalization equations.
No module or DAG node is deleted, and these results may still be needed by other parents.
The unit `sk-lem-sf-mate` and all its realized statements and steps remain intact.

## Where the brief, the DAG or earlier work was wrong

The resolution calculation in the old node and theorem docstrings is a valid alternative,
but is unnecessary for the formal statements: normalization is assumed on every complex,
and the functors are already assumed to have the full total-derived universal property.
This stronger interface makes coherence formal. The old Mathlib search correctly found
no single ready-made ringed-topos theorem, but its general `rightDerived_ext` and
`rightDerivedUnique` hits do suffice to construct these proofs.

The smaller public import closure needs the explicit filtered-colimit Mathlib import
for abelianness of small-site module sheaves; this was previously supplied transitively.
No false statement, source-library repair, forced adaptation, or unit-route error was found.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
