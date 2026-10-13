## What changed

Proved `AlgebraicGeometry.openExtension_projection_formula_of_adjunction` by the
explicit adjunction counit formula. Its existing signature and visibility are
unchanged. The sole original public import, DerivedTensorStructure, is unchanged;
the two new helper imports are proof-only.

Added two proved helper modules and nodes: OpenExtensionDerivedUnitIsIso and
OpenExtensionTensorCounitIsIso. The unit proof constructs the exact derived
extension functor explicitly, transports the ordinary invertible unit through
composition of exact derived functors, and uses full faithfulness and uniqueness
of left adjoints. Chosen adjunctions serve only proofs; no arbitrary object is
chosen to define a functor.

The second reader closed the initially split-off counit hole using existing
proved private support lemmas of DerivedOpenTensorHomBijective. A proof-only
`import all` makes those lemmas available without changing that existing module.
Its public theorem has stronger universal-open localization hypotheses, whereas
its private support and tensor-stalk lemmas need only the hypotheses supplied
here. The counit criterion translates invertibility into restriction Hom
bijectivity; the support criterion and tensor-stalk vanishing preserve that
property under tensoring. No new geometric assertion is left unproved.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.openExtension_projection_formula_of_adjunction`
(node `lem-pc-open-extension-projection-aux`).

Both new helper theorems are proved:
`AlgebraicGeometry.openExtension_derived_unit_isIso`
(node `lem-pc-open-extension-derived-unit-isiso`) and
`AlgebraicGeometry.openExtension_tensor_counit_isIso`
(node `lem-pc-open-extension-tensor-counit-isiso`).

No sorry remains in any delivered module. Holes closed: one original, plus the
first worker's proposed counit hole. Holes added relative to the repository: zero.
This is no longer a one-for-one decomposition: the original hole is closed using
existing library proofs. Explicit #print axioms for all three theorems shows only
propext, Classical.choice and Quot.sound, with no sorryAx.
No definitions or target statements changed, and no data or definition has a hole.

## No longer needed

No original import is removed and no module is claimed globally pruned. The old
proof_deps are accounted for individually:

- `def-pc-scheme-derived-tensor-structure` remains necessary for the statement's
  fixed tensor and is retained as a public import and statement dependency.
- `lem-sc-derived-open-restriction-adjunction-exact` is no longer a direct proof
  dependency of the item; it is used by the derived-unit proof and by the existing
  support lemmas.
- `lem-weil-pbc-module-stalk-exact` is no longer a direct proof dependency of the
  item; the proved support and tensor-stalk lemmas encapsulate that calculation.

The item's direct proof_deps are now exactly the proved unit and counit nodes.
The counit node uses the unit and `lem-sc-derived-open-tensor-hom-bijective`.
No standalone supported-reflection node is required for the categorical assembly.

## Where the brief, the DAG or earlier work was wrong

An adjunction Hom equivalence does not generally preserve isomorphisms. The
proof uses its actual counit formula and proves invertibility of that counit at
the tensor target. The original proof plan omitted these explicit steps.

The first worker missed the proved private support and tensor-stalk lemmas in
DerivedOpenTensorHomBijective. Reusing them closes the proposed counit hole.
The related upstream pro-etale coefficient-sheaf tensor-counit theorem concerns
ordinary sheaves in different categories and does not directly apply here.

The unit `sk-thm-picard-duality` has empty realized lists. This auxiliary node
lies below that unit; no unit statement, step or realization is changed.

## New nodes

`lem-pc-open-extension-derived-unit-isiso` records the proved derived-unit
statement and its exact-extension, derived-adjunction and full-faithfulness route.
`lem-pc-open-extension-tensor-counit-isiso` records the proved counit statement,
now reduced to the existing support and tensor-stalk lemmas and the proved unit.
Both have complete docstrings, source, searches, blueprint ancestry and Lean
records. No change record is required: all existing interfaces stay unchanged.

## Second reading by V3

1. Compared the item with the repository using diff: the existing theorem
   signature is byte-for-byte unchanged, as are all existing data definitions,
   local instances and public imports. The two other delivered modules are new.
   The existing node changes only proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled every module through lcompile.py in dependency order without errors
   or warnings. Inspected all delivered code for sorry, axiom, unsafe, opaque,
   implemented_by and extern: none remains. Explicit axiom printouts and the
   delivery probe check the three theorem declarations and helper constants.
   Each #print axioms output contains only propext, Classical.choice and
   Quot.sound, with no sorryAx. Verdict: pass.
3. Independently searched LeanFinder, Loogle, Mathlib and both library roots with
   support, tensor-stalk and counit queries. Found and reused the existing proved
   support lemmas rather than introducing another hole. Empty and total opens,
   zero factors, arbitrary adjunctions and arbitrary strong monoidal structures
   are covered: support vanishing is vacuous for the total open, detects zero
   objects for the empty open, and tensor preserves vanishing; adjoint uniqueness
   handles every supplied adjunction. No split-off statement remains open.
   Verdict: pass.
4. Read downward from the projection mate to its unit and supported counit. The
   counit uses existing proved helpers; the item composes two invertible maps by
   homEquiv_counit. All delivered imports are needed and proof-only where possible.
   Every old proof dependency is accounted for above. The unit realization record
   is untouched. Verdict: pass.
5. Read every delivered node alongside its Lean proof. The union of step uses is
   exactly proof_deps; source, proof_origin, statements and Lean records agree.
   The counit node now names the existing tensor-Hom/support node, not a new
   geometric hole. Verdict: pass.

Changes by the second reader: proved the tensor-counit theorem by reusing private
support lemmas with proof-only import all; updated its node and the proof-origin
summaries; corrected the item's proof docstring; rewrote the report to record
zero new holes and explicitly account for every old proof dependency.
