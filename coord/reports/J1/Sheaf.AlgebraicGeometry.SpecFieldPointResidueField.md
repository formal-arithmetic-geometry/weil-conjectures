## What changed

Proved `AlgebraicGeometry.spec_field_point_residue_field` using Mathlib's
`Scheme.Spec.residueFieldIso`, its compatibility lemma,
`Ideal.ker_algebraMap_residueField`, and the existing `IsFractionRing` instance.

The second reader also proved `spec_field_point_residue_field_affine_open`.
Choose a preimage of the point using `IsAffineOpen.range_fromSpec`, compose the
open immersion's residue-field isomorphism with `Scheme.Spec.residueFieldIso`,
and obtain the factorization from the affine canonical-point identity and
residue-field naturality. All declaration signatures and docstrings are unchanged.

Removed the redundant public imports `Mathlib.AlgebraicGeometry.AffineScheme`
and `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`. Both are already publicly
available through `Mathlib.AlgebraicGeometry.ResidueField`; the module compiles
with that single import.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.spec_field_point_residue_field`.
- `AlgebraicGeometry.spec_field_point_residue_field_affine_open`.

Original sorries left, both belonging to node
`lem-weil-pbc-spec-field-point-residue-field`:

- `AlgebraicGeometry.spec_field_point_residue_field_map`.
- `AlgebraicGeometry.spec_field_point_residue_field_generic`.

No new declarations, nodes, or sorries were split off.
The two proved declarations use only `propext`, `Classical.choice`, and
`Quot.sound`; the two open declarations additionally use `sorryAx`.

## No longer needed

Removed the redundant direct imports:

- `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.

No DAG nodes or modules are pruned: the declarations of the removed imports
remain needed and available through the remaining public import. Every old
`proof_deps` entry still serves the two completed clauses or the two unchanged
remaining proof plans. In particular, the morphism-from-a-field-spectrum node
still serves the open map clause.

## Where the brief, the DAG or earlier work was wrong

The first report missed the short Mathlib proof of the affine-open clause and
the redundant imports. No mathematical error or statement change was found.
The named unit source file is not present on this machine; its complete statement,
steps, and `realized` route were reviewed from `dag/units/sk-thm-p1.json`.

## Second reading by J1

1. Compared the delivered module with the repository using `diff -u`. All four
   existing declaration signatures, hypotheses, conclusions, and docstrings are
   byte-for-byte unchanged. There are no definitions or signature change records. The public-import
   cleanup is documented in the record named below. Verdict:
   unchanged mathematical interface.
2. Compiled the final module through `lcompile.py` without errors or warnings.
   Scanned the entire delivered Lean file: its only two `sorry` occurrences are
   exactly the named original map and generic theorems listed above; no forbidden
   declarations or attributes, and no hollow definitions. Compiled a scratch copy
   with `#print axioms` for all four declarations: the two completed proofs use
   only the three permitted axioms, and only the original open declarations use
   `sorryAx`. Verdict: both completed proofs are kernel checked.
3. There are no newly split-off statements. Reviewed the original remaining
   statements and their complete sourced docstring arguments against the node.
   The zero ring admits no prime or map to a field, so the relevant clauses are
   vacuous; an empty affine open has no point satisfying `hx`. For a field and
   the identity ring map the map and generic clauses assert the expected residue
   isomorphism; for a general domain the fraction-field hypothesis supplies the
   required injectivity and surjectivity. The remaining statements are true,
   unchanged work, not new restatements. Searched Mathlib by canonical-point
   naturality and affine-open range, and searched the project Lean for residue
   fields and field-spectrum factorizations. Verdict: no duplicate additions.
4. Read the proof from its top-level conjunctions downward. The first proof
   directly uses the exact Mathlib matches already recorded by the planned nodes.
   Closed the affine-open clause by the planned range, residue-isomorphism,
   naturality, and affine-identification steps. Removed both redundant direct
   imports and documented the absence of DAG pruning. Inspected `sk-thm-p1`'s
   `realized` statement and steps: this item is below that route, and none of its
   realizing nodes is bypassed or changed. Verdict: short proofs, preserved route.
5. Read the item's node and every old dependency's statement and Mathlib/Lean
   records. The first two planned proof steps describe exactly the two completed
   Lean arguments; their cited nodes are the exact Mathlib matches used here.
   The remaining steps describe the unchanged open declarations. Thus `proof`,
   `proof_deps`, and the sourced `proof_origin` remain accurate without changes.
   No new nodes require validation. Verdict: DAG and Lean agree.

Second-reading changes: proved the affine-open clause, removed two redundant
imports, and corrected this report. No statement, definition, or DAG change.

Public-import cleanup record:
`coord/changes/SpecFieldPointResidueFieldImports.md`. The dry run required this
record for removed public imports. It documents both retained public import
chains and the complete downstream list, whose interfaces require no adaptation.
