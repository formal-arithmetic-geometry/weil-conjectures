## What changed

Proved the body of `AlgebraicGeometry.affine_perfect_open_represent_cohomology_core`
without changing its signature or any definition. Perfectness uses
`affine_perfect_koszul_principal_unit` at exponent `e + 1`; the two tail constructions
are definitionally equal. Two proved private helpers identify the degree-zero boundary
with the linear form and prove chain-level power/augmentation compatibility; functoriality
then gives compatibility in the derived category.

The triangle clause is reduced to the module-level cone comparison in the new module
`Sheaf.AlgebraicGeometry.KoszulOpenConeComparison`. The main proof transports that
comparison through termwise tilde using Mathlib's cone comparison and its inclusion law,
then through `DerivedCategory.Q`; it builds the triangle isomorphism explicitly and
uses the standard distinguished mapping-cone triangle. It does not choose data for any
definition. The sole existential cone witness is used inside the theorem proof.
The old local instance attributes are retained. A local unused-variable
linter option retains the fixed unused `E` binder without a warning.

Both delivered modules compile together cleanly with `lcompile.py --all`.
The DAG proof/dependencies now follow these three separate arguments. The unit record
`sk-thm-picard-duality` has no realized nodes in this item's route; its statement and steps
were not changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affine_perfect_open_represent_cohomology_core`
(node `lem-sc-affine-perfect-open-represent-cohomology-core`). There is no `sorry`
in the item's module. This is a decomposition, not a complete sorry-free proof of the
structural facts: one original hole closed and one strictly smaller hole added (net zero).

The only added/remaining delivery hole is
`AlgebraicGeometry.koszulOpen_module_cone_comparison`
(node `lem-sc-koszul-open-cone-comparison`). It concerns only an isomorphism of complexes
of A-modules and compatibility with the degree-zero inclusion. Its source and complete
degreewise proof are in the docstring and node. It contains neither a derived category,
a perfectness clause, nor a transition compatibility clause.

The existing imported `AlgebraicGeometry.affine_perfect_koszul_principal_unit` is still
`sorry` in the library; no change to it is delivered. The main theorem also retains the
existing proof dependencies of the real definitions in `KoszulOpenSystem`.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison`:
  node `lem-sc-affine-koszul-cech-derived-comparison` is not used by this structural proof.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  node `lem-pc-affine-qcoh-derived-equivalence` is not used; the fixed `E` binder is irrelevant
  to the structural conjunction. The inherited `tool_uses` metadata is outside worker-owned
  fields and can be reconciled by the maintainer.
- `Sheaf.Paper.KoszulComplex`: redundant direct import; its declarations are still used
  through the public import of `KoszulOpenSystem`. The Koszul-complex node is not pruned.

These removals apply to this proof; the Čech and affine-equivalence modules may still be
needed elsewhere in the targets' import closure. No globally unreachable-module claim
is made.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan did not expose a triangle/cone identification or the
augmentation equality. The Čech derived-section comparison does not supply either
structural identity and is unnecessary here. The principal-unit lemma supplies exactly
the perfectness clause, despite using a differently named but definitionally equal tail.

The local `literature/stacks-project/perfect.tex` is absent. The source construction
was read at https://stacks.math.columbia.edu/tag/08CX, opening paragraphs of Section 36.9.
LeanSearch returned an Internal Server Error; its search record is marked unavailable,
not as evidence of no match. LeanFinder, Loogle/source inspection, and repository/Mathlib
grep were used. `blueprint_refs.py ancestor` reports no imported blueprint ancestor for
this stage-3-created item; the new node follows the item's existing recorded ancestry.
No mathematical statement was found false and no interface was adapted.

## New nodes

`lem-sc-koszul-open-cone-comparison`, in
`dag/nodes/sec-picard-framework/lem-sc-koszul-open-cone-comparison.json`, records
`AlgebraicGeometry.koszulOpen_module_cone_comparison` in
`lean/Sheaf/AlgebraicGeometry/KoszulOpenConeComparison.lean`. It states the negative-tail
augmentation cone identification before sheafification or localization, including the
right-inclusion equation needed by the triangle proof. The proof compares the two
summands in each degree and the boundary matrix, including degrees -1 and zero.
The empty family and zero ring are explicitly checked. No existing node or declaration
states this identification: the coordinate-cone lemma instead adjoins one generator.
No change record is needed: all existing signatures and public imports are unchanged.

## Second reading by H3

1. The delivered module preserves the target declaration signature byte for byte. The
   proof closes the original theorem using the cone comparison, the existing principal
   unit perfectness result, and the explicit augmentation compatibility argument.
   Verdict: pass.
2. The split-off cone comparison statement is true and strictly smaller: it is a
   module-level complex isomorphism with the right-inclusion equation, before derived
   categories or sheafification. Its docstring gives the degreewise construction and
   covers empty families and the zero ring. Verdict: pass.
3. The proof was compiled with `lcompile.py --all`; no forbidden declarations occur and
   the only remaining `sorry` is the named split-off theorem with its DAG node.
   Verdict: pass.
4. The imports removed from the original proof are unused by the delivered proof and
   are listed above. The remaining public imports are needed by the statement or proof;
   the proof-dependency record follows the actual route. Verdict: pass.
5. The unit route is preserved: the module still realizes the structural triangle,
   perfectness, and transition compatibility clauses of the existing unit, while the
   new node is a below-unit module reduction. Verdict: pass.

The second reading found no statement, definition, or proof defect requiring a change.
