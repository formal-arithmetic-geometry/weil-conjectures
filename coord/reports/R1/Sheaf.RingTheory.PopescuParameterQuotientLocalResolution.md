## What changed

Replaced the complete proof hole in `Algebra.parameter_quotient_local_resolution` without
changing its signature, visibility, public imports, or existing docstring. The proof now
obtains flatness and an ind-smooth closed fiber, proves nilpotence of the reduced base's
maximal ideal, applies `Algebra.popescu_lift_nilpotent`, factors the localized source map
through a smooth stage, shrinks that stage to the required universe, and verifies all
four conditions of `IsPopescuResolution`.

The proved private helper `Algebra.powered_parameter_base_nilpotent` identifies every
prime of the powered polynomial quotient with the mapped origin ideal. The variables
are nilpotent, so that maximal ideal lies in the nilradical. Noetherian finite generation
gives a nilpotence exponent, preserved by localization. This also covers `d = 0`.

Added `Sheaf.RingTheory.IndSmoothFinitePresentationFactorization`, whose theorem
`Algebra.exists_smooth_factorization_of_ind_smooth` is fully proved from Mathlib's
finite-presentation factorization theorem. It explicitly constructs the equivalence
with rings under a lifted base, preserving the algebra colimit despite independent
carrier universes; the source is lifted only for the application of Mathlib's theorem.

Added `Sheaf.RingTheory.PopescuParameterQuotientLocalFlatFiberData`, containing the
remaining flatness and closed-fiber geometry step. Its statement has no source algebra,
source map, finite-presentation assumption, factorization, singular ideal, or resolution.
The existing proof-dependency modules for its argument are imported there. Updated the
original node and supplied nodes for both new modules. There are no interface changes
or forced adaptations to existing modules.

## Proved and sorry left

Closed the original hole in `Algebra.parameter_quotient_local_resolution` (node
`lem-weil-pbc-popescu-parameter-quotient-local-resolution`). The complete proof combines
the smaller geometry statement with existing nilpotent lifting and a proved factorization
lemma; it is a decomposition, not a claim that the entire geometric theorem is now closed.

Fully proved `Algebra.powered_parameter_base_nilpotent` (private helper in the item's
module) and `Algebra.exists_smooth_factorization_of_ind_smooth` (new node
`lem-weil-pbc-ind-smooth-finite-presentation-factorization`). Neither contains `sorry`.

One new hole remains, and this is the only direct `sorry` in the delivery:
`Algebra.parameter_quotient_local_flat_fiber_data`, node
`lem-weil-pbc-popescu-parameter-quotient-local-flat-fiber-data`, in
`Sheaf.RingTheory.PopescuParameterQuotientLocalFlatFiberData`. Its proof is exactly
`by sorry`; the docstring states the source and the complete argument, including the
quotient/localization identifications and the closed-fiber algebra structures.

Hole accounting: one original hole closed, one strictly smaller hole added, net zero.
The original module has zero direct holes. All three delivery modules compile together
without warnings using the required `lcompile.py --all` command.

Edge cases: the nilpotence proof works with the empty variable set (`d = 0`) and does
not presume positive dimension. The remaining geometry statement also includes `d = 0`:
the polynomial base is a field and hgen makes the target localization a field.
The positive-power assumption `1 ≤ c` ensures the powered ideal lies in the origin
ideal. The factorization lemma permits a zero ring and independent source/base/target
universes; the filtered presentation supplies its own nonempty connected index.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.FieldTheory.SeparableSmoothColimit`;
- `Sheaf.RingTheory.FlatOverRegular`;
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`.

They are relocated to the remaining geometry module, where their statements are needed.
`Sheaf.RingTheory.PolynomialOriginRegularLocal` remains a direct import for the proved
nilpotence helper and is also needed by the geometry argument. No old node or module is
claimed globally pruned: the original route is retained through the new geometry node.

The original node's direct dependencies for finite-presentation factorization are now
recorded through the proved independent-universe factorization node. Nilpotence is
proved from Noetherian nilradical theory rather than a new monomial-degree lemma.
No extra node or module for a combinatorial monomial bound is needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The existing quotient-map compatibility
hypothesis is retained unchanged but is unnecessary for the completed last part:
ind-smoothness of the target factors any finitely presented map into it.

The original plan did not expose the algebra-category and carrier-universe glue needed
by the finite-presentation Mathlib leaf. That glue is now proved explicitly, not left
as an additional assumption or a new hole.

The local clone has no `literature/stacks-project` contents. The source was read from
the already available Stacks checkout on this machine: `smoothing.tex`,
`lemma-resolve-special` (07FE), its final paragraph; and `algebra.tex`,
`lemma-characterize-finite-presentation` (00QO) and `lemma-when-colimit` (07C3).
The node source paths retain the project's canonical literature paths.

`blueprint_refs.py ancestor` cannot follow the existing node's `created.item`, which is
a module name from its stage-3 creation rather than a DAG node id. The new nodes retain
the existing node's recorded blueprint ancestor `thm-weil-pbc-finite-etale-lifting`,
with their exact places in subsidiary Lemma 07FE and the existing via chain.
Searches of the blueprint found no exact duplicate of the new statements. LeanSearch
returned HTTP 500 for both new-node queries; this is recorded as unavailable, not as
negative evidence. Loogle, LeanFinder, grep, source inspection, and compilation supplied
the useful results. The `sk-thm-p1` unit's statement and realized steps are unchanged.

## New nodes

`lem-weil-pbc-popescu-parameter-quotient-local-flat-fiber-data` records flatness of the
canonical reduced local map and ind-smoothness of its closed fiber, with no source-algebra
or resolution conclusion. Its module is
`lean/Sheaf/RingTheory/PopescuParameterQuotientLocalFlatFiberData.lean`.
Its docstring and three proof steps explain contraction to the origin, regular-parameter
flatness, quotient/localization compatibility, and the separable residue-field colimit.
It is the one remaining hole.

`lem-weil-pbc-ind-smooth-finite-presentation-factorization` records the proved bridge
from a `CommAlgCat` ind-smooth presentation to smooth-stage factorization when base,
source, and target carriers occupy independent universes. Its module is
`lean/Sheaf/RingTheory/IndSmoothFinitePresentationFactorization.lean`.
It reuses the existing Mathlib finite-presentation leaf and the connected-colimit
forgetful-functor leaf. No change record is needed: all existing interfaces are identical.

## Second reading by R1

1. **Visible interfaces.** Compared each delivered module with the repository version.
Existing declaration signatures and the target statement are byte-for-byte unchanged;
the only existing-module edits are proof imports and the proof body. The two added
modules and their DAG nodes are new declarations with matching statements.

2. **Compilation and axioms.** Compiled all three modules with
`lcompile.py --all`; compilation completed without errors or warnings. The original
target has no direct `sorry`. The sole remaining `sorry` is the named theorem
`Algebra.parameter_quotient_local_flat_fiber_data`, with its node and source-backed
docstring. No forbidden declaration forms or hollow definitions occur.

3. **Statement review.** Checked both split-off statements against their Lean types,
their DAG text, and the cited Stacks arguments. The flatness/closed-fiber statement is
strictly smaller than the resolution target and has the required contraction,
regularity, quotient, and separability hypotheses. The factorization statement is the
needed independent-universe finite-presentation consequence. Edge case `d = 0` is
addressed in the geometry docstring; no duplicate library statement was found.

4. **Proof route and pruning.** The target proof uses Mathlib nilradical and finite-type
facts, the two new declarations, and the existing Popescu lifting and singular-ideal
definitions. Removed imports are listed above and the updated node `proof_deps` matches
the proof. No old dependency is falsely claimed pruned.

5. **Unit and DAG consistency.** Read `dag/units/sk-thm-p1.json`; its statement and
realized steps are unchanged. The delivered nodes remain subsidiary to that route, and
their `proof`, `proof_deps`, `proof_origin`, Lean declarations, chapter, and unit fields
agree with the source files. No statement change or forced adaptation was needed.

No repair was necessary during this second reading.
