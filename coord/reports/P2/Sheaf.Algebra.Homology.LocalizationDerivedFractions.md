## What changed

Proved `RingTensorCohomology.derivedLocalization_fractions` in
`Sheaf.Algebra.Homology.LocalizationDerivedFractions`, preserving its signature,
visibility, docstring, and original public imports.

Added a proof-only import of
`Sheaf.Algebra.Homology.BaseTensorUnitCohomologyModel`.
The second reader removed redundant direct imports of
`Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Localization.BaseChange`; both are already available transitively.
The private proved helper `ordinary_fractions` identifies the ordinary complex
unit on homology with a localized-module unit using exactness and
`ShortComplex.homologyMap_mapNatTrans`, then applies `IsLocalizedModule.surj`.
The private proved helper `model_fractions` transports this equation through the
existing A-linear balanced unit comparisons. The main proof constructs the
existing cohomology models over D = Aq tensor_R B, and uses two explicit
naturality equations to transport their numerator and denominator back to the
supplied functor F. No definition or public signature changes.

Updated the item's node proof, proof_deps and proof_origin to this route.
The unit record has no realized statement or steps replaced by this argument.

## Proved and sorry left

Closed the sole original hole:
`RingTensorCohomology.derivedLocalization_fractions`
(node `lem-pc-localization-derived-fractions`).
Both new private helpers are fully proved. No sorry remains in the delivered
module, no hole was added, and no statement was split off.

This is a proof from existing stated dependencies, not a claim that their
transitive axioms are already closed. In particular,
`RingTensorCohomology.exists_baseTensorUnitCohomologyModel`
(node `new-lem-pc-base-tensor-unit-cohomology-model`) remains an existing imported
sorry. Its balanced calculation is reused rather than restated.

Single-file compilation succeeded without warnings in about six seconds.
The ordinary argument works for arbitrary unbounded complexes and arbitrary S,
including S containing zero and S={1}; it invokes the unrestricted localized
module surjectivity field and has no nonzero or boundedness assumptions.

## No longer needed

No original public import was removed: all three supply the existing statement.
Removed the first worker's redundant proof imports of
`Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Localization.BaseChange` after compiling without both together.
These removals do not prune either Mathlib module from the import closure.
A trial direct import of `Mathlib.Algebra.Category.ModuleCat.Descent` was removed
because it is already publicly available through `RingTensorCohomology`.

The item's old direct proof dependencies
`lem-pc-balanced-derived-tensor-model` and
`lem-pc-derived-tensor-action-naturality` are replaced by the existing
`new-lem-pc-base-tensor-unit-cohomology-model`. They remain transitive dependencies
of that theorem; their modules are not claimed pruned from the targets' closure.

`lem-weil-pbc-localization-module-exact` is not used by this proof: exactness is
obtained from flatness and the extension/restriction adjunctions.
`lem-weil-pbc-localization-tensor-product` is also no longer a direct dependency;
the needed one-factor tensor localization is recorded under the existing
Mathlib leaf `lem-weil-pbc-localization-tensor-over-base`.
No whole library module is claimed pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The previous proof plan did not mention the already available
`exists_baseTensorUnitCohomologyModel`, which provides the balanced-complex unit
comparison needed here without localization assumptions. This avoids duplicating
its construction. The statement is unchanged and no mathematical error was found.


## Second reading by P2

1. Compared the delivered Lean module with the repository using `diff` and checked
   the complete existing theorem signature byte for byte: identical. The original
   docstring, visibility and public imports are unchanged. Only two private proved
   helpers, a proof-only import and the existing theorem's proof are added. There
   are no definitions or interface changes and no change record is required.
2. Compiled the whole delivered file locally through `lcompile.py`, without errors
   or warnings. Scanned for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`
   and `extern`: none occurs. In a scratch copy, `#print axioms` for
   `ordinary_fractions` gives only `propext`, `Classical.choice`, `Quot.sound`;
   `model_fractions` and `derivedLocalization_fractions` additionally use `sorryAx`
   through existing imported statements. No new data definition chooses a witness
   of an unproved existence theorem: all model and complex witnesses are eliminated
   locally inside proofs of propositions. Read the model construction and balanced
   unit comparison used by the proof; neither is redefined here.
3. No statement is split off and no new hole is added. Read both private helpers:
   exact extension/restriction identifies homology of the unit with localization
   of homology, and the second helper transports its equation through A-linear
   isomorphisms. The argument remains valid for the zero complex, S containing
   zero, S={1}, and arbitrary unbounded complexes. The imported balanced comparison
   is strictly a computation of the unit, with no localization assumption; it does
   not restate the fractions theorem.
4. Searched the library and Mathlib homology/module-category sources for
   localization of homology and fraction statements, and inspected the localization
   base-change instance and its surjectivity property. No shorter independent
   derived fraction result was found; the later model-localization results depend
   on this theorem. All newly added imports are proof-only. Removed the two
   redundant direct Mathlib imports and compiled with both absent. The report lists
   all four old direct proof dependencies that were replaced or removed and makes
   no whole-module pruning claim. Inspected
   `dag/units/sk-thm-picard-semicon.json`: its `realized` field is
   `{"statement": [], "steps": [[]]}`; no realized node is bypassed or modified.
   The balanced unit computation retains the old balanced tensor/action route
   transitively.
5. Compared node JSON: only `proof`, `proof_deps`, and `proof_origin` differ.
   The five proof steps match model existence, the existing balanced comparison,
   exact ordinary localization, A-linear transport and universal-counit naturality
   in the Lean proof. The dependency list equals the union of their `uses`.
   There are no new nodes, signatures, statement changes or forced adaptations.

Second-reading changes: removed the redundant direct proof imports
`Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Localization.BaseChange`, and corrected the import account
above. The proof itself needed no repair. Closed 1 original hole, added 0 holes;
this is a proof from existing open dependencies, not a decomposition or a claim
of transitive axiom closure.
