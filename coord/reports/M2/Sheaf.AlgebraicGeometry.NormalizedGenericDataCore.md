## What changed

Proved `AlgebraicGeometry.Etale.exists_constructible_module_normalized_generic_data_core`
in `Sheaf.AlgebraicGeometry.NormalizedGenericDataCore` with its signature unchanged.
The proof uses the existing constructibility comparison, constructible pullback,
finite separable field trivialization, and normalization declarations. It combines their
witnesses using the inverse-image composition and constant-pullback isomorphisms.

A fully proved private helper,
`isIso_unit_constantSheaf_of_generic_residueFieldIso`, transports the normal generic
constant-sheaf unit theorem from the canonical generic-stalk inclusion to `g`.
It proves that the stalk map is invertible using the residue-field square, factors `g`
through that stalk, and uses the actual composition-unit equation. No new public
statement, definition, module or unproved intermediate theorem is introduced.

Added proof-only imports:
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`,
`Sheaf.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant`,
`Sheaf.Paper.WeilPbcNormalizationInResidueFieldExtension`,
`WeilConjectures.ConstructibleSheaf.Pullback`,
`WeilConjectures.ConstructibleSheaf.FinitePushforward`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`.
All original public imports remain. Updated the core node's proof, proof_deps and
proof_origin to the implemented noncircular argument. The unit's realized route is unchanged.

The module compiles locally without errors or warnings. The private helper and the
main theorem were compiled incrementally. Edge cases: the hypothesis `x : X` excludes
an empty base; the zero module is allowed; normalization need not be Noetherian or
finite over X; no such hypotheses are used in the unit transport. The proof does not
use algebraic closedness or geometric-point lifting.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.Etale.exists_constructible_module_normalized_generic_data_core`
(node `new-normalized-generic-data-core`). Also proved the private unit-transport helper.
There are no sorries left in the delivered module and no new sorries.

This is a proof from existing named declarations, as requested for stage 3. In particular,
`normalization_in_finite_residue_field_extension` and
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed` are still
unproved inputs in the library; the field-trivialization theorem also uses its existing
unproved datum/construction inputs. Their proofs are separate items.

## No longer needed

Removed the circular proof-dependency edge from `new-normalized-generic-data-core` to
`lem-weil-pbc-constructible-module-normalized-generic-data`
(module `Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData`).
That module remains the consumer of the core theorem, so this removes only its use
as a purported input to the core, not its role above it.

No original imports were removed. Redundant experimental direct imports of
`Mathlib.AlgebraicGeometry.FunctionField` and `Mathlib.RingTheory.SimpleRing.Basic`
were removed after successful compilation without them. No geometric-point lifting
or algebraically closed extension lemma is needed for this core statement. The fuller
parent theorem still needs its lifting clause. No other existing node or module is
claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The core node's original one-step plan cited the fuller normalized-generic-data theorem,
whose Lean proof already invokes this core. It was circular. The delivery follows the
fuller node's detailed construction steps 1--3 instead, using their actual independent
inputs. The inverse-image coherence equations recorded under
`lem-weil-pbc-inverse-image-composition` live in the `Coherence` module, whereas the
node's primary Lean record names `Defs`; the proof imports `Coherence` explicitly.

The normalization theorem supplies integral Y with normal stalks, not a Noetherian Y.
The normal-unit theorem in `WeilConjectures.ConstructibleSheaf.FinitePushforward`
requires no Noetherian hypothesis and therefore fits; the similarly named
`Sheaf.AlgebraicGeometry.NormalGenericConstant` theorem would not suffice here.

Read the source construction at [Stacks 09Z6](https://stacks.math.columbia.edu/tag/09Z6)
and the normal generic-point theorem at
[Stacks 09Z5](https://stacks.math.columbia.edu/tag/09Z5).
The corresponding literature checkout is absent on this machine.
Searches: LeanFinder for finite separable trivialization of a constructible module sheaf
returned no combined construction; Loogle for `CategoryTheory.Adjunction.unit` supplied
adjunction tools; rg across both library roots found the existing independent inputs and
the proved pullback and coherence comparisons. No shorter combined theorem was found.

## Second reading by M2

1. **Statements.** Compared the delivered module with the repository version. The existing
   theorem signature is unchanged byte for byte. The new node records the same statement,
   with no added hypotheses or weakened conclusion.
2. **Proof.** Compiled the module with `lcompile.py`; it has no errors, warnings, `sorry`,
   axioms, unsafe declarations, or hollow definitions. The private helper and the public
   theorem are proved from named declarations; the remaining open inputs are imported
   theorems and are not new sorries in this delivery.
3. **Split statements.** No public theorem was split off and no new node beyond the
   existing core node was introduced. The helper is private and fully proved. Searches of
   the library and Mathlib found no duplicate declaration for the core result.
4. **Pruning and route.** The circular dependency on the fuller normalized-generic-data
   theorem was removed from the node's proof dependencies. The proof follows the unit's
   realized construction through constructibility, finite separable trivialization,
   normalization, and generic-unit transport. Imports used only for the proof are plain
   `import`; no original public import was removed.
5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` describe the
   implemented route, including the coherence module needed for inverse-image composition.
   The unit's `realized` route remains unchanged.

The second reading found no mathematical or interface defect. Changes made were limited to
the proof imports, the proof and its node metadata, and this required review record.
