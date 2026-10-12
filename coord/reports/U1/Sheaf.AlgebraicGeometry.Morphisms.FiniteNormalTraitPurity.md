## What changed

The existing declaration
`AlgebraicGeometry.Scheme.finite_normal_etale_of_trait_neighbourhood` now assembles two
strictly separate steps of its original proof: extension of the punctured cover, then
identification with the given normal finite model. Its existing signature and docstring
are byte for byte unchanged. The first worker's undocumented zero/one case restatements
and dimension-classification module were removed from the unlanded sandbox.

New module `Sheaf.AlgebraicGeometry.Morphisms.TraitEtaleExtension` states
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_trait_neighbourhood`.
It proves only existence of a finite etale extension with normal local rings and dense
puncture, without assuming normality or density of the given N. It does not conclude
that the given morphism n is etale. New module
`Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso` states
`AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open`, a generic comparison theorem
with no trait, smoothness, connectedness, dimension, or etaleness hypotheses.
Both unresolved proofs have complete source-based docstrings and matching nodes.

The main proof explicitly supplies local Noetherianity of L using the proved Mathlib
`LocallyOfFiniteType.isLocallyNoetherian q`, obtains the extension and restriction
isomorphism, applies the normal comparison theorem, rewrites n as an isomorphism
followed by the etale extension, and uses the proved composition instance.
Existential witnesses are eliminated only to prove a proposition. No data definition
is added, and no arbitrary witness is selected in a definition.

Mathlib.AlgebraicGeometry.Noetherian is now a plain proof import in the item and the
extension module. Its visibility correction is recorded in
`coord/changes/FiniteNormalTraitPurity-noetherian-import.md`. The only direct importer of
the item, StalkNormalizationFibrePurity, independently publicly imports Noetherian,
so this change needs no adaptation and changes no downstream statement.

## Proved and sorry left

Closed one original hole, by declaration name:
`AlgebraicGeometry.Scheme.finite_normal_etale_of_trait_neighbourhood`.
There is no direct sorry left in the item's module.

Added two holes:
- `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_trait_neighbourhood`
  (node `lem-sbc-trait-etale-extension`).
- `AlgebraicGeometry.Scheme.finite_normal_iso_of_dense_open`
  (node `lem-sbc-finite-normal-dense-open-iso`).

This is a decomposition, not a complete proof or a gain in the sorry ledger:
one original hole closed minus two added gives net -1 in the import closure.
The target still depends on sorryAx through these two statements. All three
#print axioms probes show only propext, Classical.choice, Quot.sound, and sorryAx.
All three delivered modules compile locally without errors or other warnings.
The original first-worker holes trait_purity_zero_case, trait_purity_one_case and
ringKrullDim_eq_zero_or_one were discarded before delivery, not counted as holes closed
against the library baseline.

## No longer needed

Removed direct proof imports Sheaf.RingTheory.SmoothNormalRing and
Sheaf.RingTheory.EtaleNormalRing from the item: their planned normality-ascent use
belongs to the extension lemma, whose module keeps them as plain proof imports.
The old proof_deps lem-weil-pbc-smooth-over-normal-ring-normal and
lem-weil-pbc-etale-over-normal-ring-normal are no longer direct dependencies of the item,
but remain dependencies of lem-sbc-trait-etale-extension. No old dependency node or
module is pruned from the import closure. The unlanded TraitDimensionClassification
module and its three proposed nodes are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's new theorems had no source/proof docstrings, incomplete node fields,
nonverbatim Lean statements, no recorded searches, and no updated parent proof plan.
Splitting only by dimension left the one-dimensional case essentially equal to the
whole difficult argument. The replacement follows the original plan's genuine
separation between producing an etale extension and comparing normal finite models.
The original mathematical statement was not found false, and no existing signature
was changed to make the proof easier.

## New nodes

`lem-sbc-trait-etale-extension` states the existence step from Stacks Tags
0EYE and 0EYJ, trait paragraph, with normality ascent from Tag 033C. Its module is
TraitEtaleExtension.lean, and its proof_deps retain the two original normality tools.

`lem-sbc-finite-normal-dense-open-iso` states the componentwise integral-closure
comparison used after extension (Stacks Tag 0BQL, integral-closure argument).
Its module is FiniteNormalDenseOpenIso.lean. Density is required on both sources;
no smoothness or etaleness conclusion is hidden in its statement.

Both nodes include chapter, unit, provenance, blueprint ancestry, source, verbatim
Lean signatures, complete proofs in words, and three actual Mathlib searches.
LeanSearch returned an Internal Server Error; that unavailability is recorded.
LeanFinder and focused rg searches located relative-normalization and etale-locus
lemmas, whose statements do not provide either new theorem. Searches of the project's
Lean sources found no equivalent comparison or divisor-purity theorem.

Change record: `coord/changes/FiniteNormalTraitPurity-noetherian-import.md`.

## Second reading by U1

1. Compared the final item against the repository with diff and checked the raw
   signature text: the existing declaration is byte for byte unchanged, as is its
   docstring. No existing definition, target statement, or other claimed module was
   changed. The only public-import correction has the named change record and preserves
   downstream access through the sole direct importer's own public Noetherian import.
   Verdict: pass.
2. Compiled all three modules through lcompile.py in import order. Added #print axioms
   to scratch copies and compiled each: only propext, Classical.choice, Quot.sound and
   sorryAx occur. There are exactly two named theorem holes, both whole proofs;
   no forbidden declaration form, partial proof hole, or data definition is added.
   Verdict: pass as a decomposition, not as an axiom-free completed proof.
3. Read both new statements and their full docstring arguments. Tested the field case
   (empty puncture and empty extension), the DVR case (irreducible regular special
   fibre), empty sources, disconnected finite covers, and the necessity of density on
   each normal model. Adding a component supported off U shows why density cannot be
   omitted in the comparison theorem. The extension statement deliberately does not
   use normality/density of N; it extends only the punctured cover. The comparison uses
   integral closure over an arbitrary locally Noetherian base, not etale purity. Their
   conclusions are distinct strict steps of the argument. Repeated searches using
   different wording and read the relative-normalization candidates. Verdict: true,
   needed statements; no duplicate or renamed target.
4. Read the original plan and sk-prop-input-spreading unit record. Its realized arrays
   are unchanged. The finite-etale-extension/normal-comparison route is kept. The main
   imports the two step modules privately; the generic comparison imports only what its
   signature needs. Normality ascent modules are retained only where the extension
   proof plan needs them. Every removed direct dependency is accounted for above;
   no import-closure pruning is claimed. Verdict: pass.
5. Checked the parent proof, proof_deps, and proof_origin against the assembly and both
   new nodes against their Lean signatures, docstrings, dependency unions, sources,
   searches, and ancestry. The parent retains all non-stage-3-owned fields unchanged.
   Verdict: pass.

Second-reading changes: replaced the incomplete dimension-case scaffolding with two
source-based steps, supplied the explicit Mathlib local-Noetherian proof, corrected
proof-only import visibility, completed both new nodes and the parent proof records,
and corrected the report's hole accounting and pruning claims.
