## What changed

The original `localizationModelMap_denominators` signature is unchanged. Its
proof now applies `RingTensorCohomology.derivedLocalization_fractions` to the
single derived functor `L.derived`, then explicitly transports the resulting
homology equation through the universal-counit comparison and the model
cohomology isomorphisms. Naturality of that comparison and the existing
`K.cohomologyIso_smul` field prove the denominator-action identification.
The new module `Sheaf.Algebra.Homology.LocalizationDerivedFractions` is imported
with plain `import`, because only the proof needs it. The denominator node's
proof route and dependencies now describe this actual proof.

The first worker's generic fraction-surjectivity and equality-kernel components
were false, and neither had a node or a complete proof docstring. They and the
new localized-module wrapper were removed. The unchanged sandbox copy of
`LocalizationModelSemilinear` was removed from the delivery. No definitions,
existing public signatures, public imports, target statements, or other
modules were changed. No interface change record is needed for the repaired
proof and its private proof import; the obsolete wrapper change record was
removed.

## Proved and sorry left

Hole closed in the item's module:
`RingTensorCohomology.localizationModelMap_denominators`
(node `lem-pc-first-localization-cohomology-denominators`).

Hole added and left in a new module:
`RingTensorCohomology.derivedLocalization_fractions`
(node `lem-pc-localization-derived-fractions`, module
`Sheaf.Algebra.Homology.LocalizationDerivedFractions`). Its whole proof is
`:= by sorry`, and its docstring gives the source and full mathematical proof.
There are no other delivered holes.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
The denominator theorem still depends on `sorryAx` through that named lower
statement, so this delivery does not claim a completed axiom-free proof of the
item. The lower statement handles only the fraction calculation for one
abstract derived functor. It has no tensor-coefficient module structure, no
second chosen model K, no cohomology-model isomorphisms and no counit comparison
between two derived functors. The actual parent proof supplies that missing
transport and scalar-action argument. It does not simply apply a renamed copy
of the parent statement.

Both modules compiled individually in import order using `lcompile.py` with no
errors or warnings. Scratch copies with `#print axioms` show exactly `propext`,
`Classical.choice`, `Quot.sound`, and the expected `sorryAx` for both declarations.
No data is chosen from an unproved existence theorem in this delivery.

## No longer needed

No repository import was removed, and no module is claimed pruned. Relative to
the original denominator node, these five nodes are no longer *direct*
proof dependencies:

- `lem-pc-balanced-derived-tensor-model`
- `lem-pc-derived-tensor-action-naturality`
- `lem-weil-pbc-localization-flat`
- `lem-weil-pbc-localization-module-exact`
- `lem-weil-pbc-localization-tensor-product`

They remain in the proof plan of `lem-pc-localization-derived-fractions`, so
they are not claimed obsolete or bypassed in the unit's route. The parent
retains its existing model-definition and localization-map dependencies.
The proposed `lem-pc-first-localization-cohomology-localized-module` node and
wrapper, both false generic component lemmas, their extra BaseChange proof
import and the linter-suppression option were discarded before delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's component theorems asserted fraction-surjectivity and a
denominator-torsion kernel for an arbitrary linear map, without any hypothesis
that it is a localization map. Both fail for the zero map on Z and S = {1}.
At y = 1, surjectivity asserts 1 = 0; for x1 = 0 and x2 = 1, the kernel component
also asserts 0 = 1. The surjectivity example uses identity ring localization,
so it satisfies even the extra ring-localization hypotheses of that component.
Independent scratch theorems `zero_not_fraction_surjective` and
`zero_not_denominator_kernel` proving these negations compiled and use only
the three permitted axioms. The missing component nodes and short docstrings
also violated the split-off contract. Merely compiling that delivery did not
make those statements true.

The original report described both parent assertions as proved despite the
false components and missing node coverage. The repaired delivery is instead
explicitly a one-for-one decomposition. The algebraic map-units calculation
was correct but unnecessary for this denominator-only reduction, and would
have forced an unrelated kernel obligation.

## New nodes

`lem-pc-localization-derived-fractions` states the cycle fraction calculation
before transport to the tensor-cohomology models. It is strictly a component
of the argument; the denominator theorem separately proves naturality and
scalar transport. Its node includes the exact Lean signature, source, proof
steps and their dependency union, origin, search records, creation record,
blueprint provenance, and the parent's chapter and unit.

Independent searches used Lean Finder for derived localization-unit fractions,
Loogle for `IsLocalization, TensorProduct`, and grep/rg with homology,
localization, fraction and derived-functor variants. Ordinary localization
and categorical derived-functor results were found, but no theorem supplies
this derived fraction calculation. LeanSearch was attempted and returned
Internal Server Error, recorded as unavailable. Existing model base-change
results depend on this denominator theorem and would create an import cycle.
Source checked: [Stacks 06Y6](https://stacks.math.columbia.edu/tag/06Y6) and
[Stacks 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8).

## Second reading by R4

1. Compared both originally delivered modules against the repository. Existing
   denominator and scalar-compatibility signatures were unchanged. After repair,
   the delivery parser reports no statement changes, removed declarations or
   interface changes; the original denominator signature compares identically.
   The unchanged semilinear module is omitted. Verdict: pass after repair.
2. Compiled the original delivery, which compiled despite its false holes.
   Compiled the repaired modules and scratch axiom audits. There is exactly one
   public named theorem left with whole-proof `sorry`, in the new fractions
   module. No forbidden declaration, hollow definition, or hidden proof hole
   appears. The axiom audit contains only the allowed axioms and the declared
   remaining `sorryAx`. Verdict: valid decomposition, not a complete proof.
3. Refuted both first-worker components by independently compiled small
   counterexamples. Replaced them with the true derived-unit fraction statement
   with its source proof and node. Checked S = {1}, zero localization, zero
   complex, arbitrary unbounded Q, and the absence of flatness assumptions on
   A or Q. The K-flat resolution is of B over R. Independent searches found
   no duplicate. Verdict: pass after repair.
4. Read the parent proof from its conclusion down to the derived fractions.
   The parent now contains the full model and scalar transport; no kernel or
   IsLocalizedModule assertion is needed. Imports are minimal for the selected
   statements and proof. All five removed direct proof dependencies are listed
   above and retained under the lower calculation. Read
   `dag/units/sk-thm-picard-semicon.json`; its existing `realized` entries are
   empty and unchanged. The chapter/unit route is preserved. Verdict: pass.
5. Checked the delivered node signatures against the Lean declarations and
   checked that proof_deps is the union of proof-step uses. The existing node
   keeps its statement and statement dependencies; only its proof route,
   proof_deps and proof_origin change. The new lower node has the required
   metadata and matching documented hole. Verdict: pass after repair.

Changed by the second reader: removed the two false components, their
localized-module wrapper and node/change record, the unchanged semilinear copy,
and the unnecessary import/linter option; added one documented derived-fraction
component and its node; proved the explicit counit-natural scalar transport;
updated the parent node and corrected the report's progress accounting.
