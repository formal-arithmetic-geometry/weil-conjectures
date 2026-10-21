## What changed

Retire the obsolete zero-hole module
Sheaf.AlgebraicGeometry.StrictLocalSectionsUnitLeray, as listed in
coord/retire-items.tsv, through deleted.txt. Its complete proof already exists in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalSectionsUnitLeray under
AlgebraicGeometry.Etale.smallModel_strictLocalSections_unit_leray. Preserve that
existing implementation and the DAG attachment to it, adding a note explaining
the retirement. No new theorem, alias or module is introduced.

Change record: coord/changes/U2-strict-local-sections-unit-leray-retirement.md.

Validation through lcompile.py passed for the original module (16.5 s), retained
replacement (0.1 s), live parent StrictLocalSmallModel.StrictLocalDerivedExchangeLeray
(12.6 s), and a scratch comparison probe (2.7 s). The probe proves equality of the
two fully quantified theorem constants by rfl, so their types are definitionally
identical. Both #print axioms outputs contain exactly propext, Classical.choice
and Quot.sound. The scratch sources and compiled artifacts are not delivered.

## Proved and sorry left

This is a listed retirement repair with 0 original holes, 0 holes closed, 0 holes
added, 0 split off and 0 holes left. The removed declaration
AlgebraicGeometry.Etale.strictLocalSections_unit_leray was already proved. Its
identically typed, fully proved replacement
AlgebraicGeometry.Etale.smallModel_strictLocalSections_unit_leray remains attached
to lem-weil-pbc-strict-local-sections-unit-leray. The three private helper proofs
also remain in the replacement module. No proof closure is claimed for retiring
a previously proved duplicate.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.StrictLocalSectionsUnitLeray.
Its five public imports disappear with that obsolete copy:

- Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
- Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
- WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
- WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

Those dependencies are still needed by the retained small-model implementation;
no dependency node or further module is claimed pruned. In particular, keep
lem-weil-pbc-strict-henselization-scheme-sections-exact and
lem-weil-pbc-strict-local-sections-unit-leray. tools/downstream.py reports zero
live downstream modules of the removed path. The live parent already privately
imports StrictLocalSmallModel.StrictLocalSectionsUnitLeray and invokes the
smallModel theorem. No live consumer needs adaptation.

The DAG parent lem-weil-pbc-strict-local-derived-exchange-leray still uses the
sections-unit node in proof_deps and its first proof step, and is already attached
to the fully proved small-model parent. The older archived parent at
quarantine/Sheaf/AlgebraicGeometry/StrictLocalDerivedExchangeLeray.lean still imports
the old path, but has no current coord/rework.tsv entry. Its existing replacement
argument and node attachment are preserved; no archive is deleted or restoration
assignment bypassed. The unit route in dag/units/sk-prop-h2.json is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished proof, but the current item is
a listed retirement with zero holes. Its mathematical obligation has already been
proved in the original small-model module, and the node was redirected there by
the earlier C3 restoration. Merely reproving the identity would leave the obsolete
copy in place. This delivery completes the retirement while preserving the exact
statement and all mathematical dependencies.

The canonical source theorem uses strictLocalization; the assigned old copy and
the retained smallModel theorem use strictHenselizationScheme. These cannot be
substituted by definitional equality. The Lean type-equality probe compares the
two small-model statements only. No adopted-source declaration, proof, signature,
attribute, public import or definition is changed.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
