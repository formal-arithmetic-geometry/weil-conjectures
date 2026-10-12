## What changed

Proved `Algebra.exists_firstOrder_powerSeries_comparison` with its signature and all
existing public imports unchanged. Its private coefficient-field helper derives a residue
section from `IsLocalRing.exists_coefficient_subring`: the characteristic of the base field
also annihilates the coefficient subring, whose reduction ideal is consequently zero.
The inclusion descends through that zero ideal and the inverse residue isomorphism.
No field structure or arbitrary existence witness is installed in a public definition.

Added three independently proved modules:

- `Sheaf.RingTheory.LocalFirstOrderCoordinates`: constructs the ring equivalence from
  `A/m²` to the trivial square-zero extension using a cotangent basis, and proves its
  compatibility with the residue map. The scalar action is kept equal to the canonical
  residue-field action before installing the algebra structure from the section.
- `Sheaf.RingTheory.PowerSeriesQuadraticIdeal`: constructs coefficientwise series grouped
  by a chosen pair of variable factors. The finite sum of their products with the two
  variables recovers every series with vanishing constant and linear terms.
- `Sheaf.RingTheory.PowerSeriesFirstOrderCoordinates`: constructs the constant-and-linear
  ring map, proves its kernel is the quadratic variables ideal, proves surjectivity using
  an explicit constant-plus-linear representative, and proves the variables-ideal criterion.

The comparison composes the quotient map with the local equivalence and the inverse
power-series equivalence. Surjectivity follows by composition. Ideal extensionality,
the two residue-coordinate formulas, and `residue_eq_zero_iff` prove the preimage equality.
Updated the original node's proof, proof dependencies, and proof origin to match this proof.
All three new nodes carry their proved declarations and detailed arguments.

Validation: all four modules compile together through the prescribed `lcompile.py --all`
without errors or warnings. Edge cases were included in the proofs: an empty variable set,
zero cotangent dimension, arbitrary characteristic, and even the zero coefficient ring in
the quadratic-ideal lemma. No existing statement, definition, or visibility was changed.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_firstOrder_powerSeries_comparison`
(`lem-weil-pbc-first-order-power-series-comparison`).

Also proved, with no holes:

- the private helper `Algebra.exists_coefficient_field_section`;
- `IsLocalRing.exists_firstOrder_coordinates`
  (`lem-weil-pbc-local-first-order-coordinates`);
- `MvPowerSeries.mem_span_X_sq_of_coeff_eq_zero`
  (`lem-weil-pbc-power-series-quadratic-ideal`);
- `MvPowerSeries.exists_firstOrder_coordinates`
  (`lem-weil-pbc-power-series-first-order-coordinates`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: none. This is a proof,
not a decomposition into new unproved statements. The coefficient-subring theorem remains
an existing dependency; this delivery makes no assertion that all its transitive dependencies
are already sorry-free.

## No longer needed

No original library module or node is pruned. The original proof-only import
`Sheaf.RingTheory.ExistsCoefficientSubring` is used. Nakayama remains needed through the
proved cotangent-dimension theorem in `LocalFirstOrderCoordinates`; its DAG reference was
moved to that node rather than discarded. The Noetherian and multivariate-series definitions
also remain needed by the statements and the new coordinate lemmas.

Removed redundant imports added while developing the proof:
`Mathlib.RingTheory.LocalRing.ResidueField.Basic` from the comparison module and
`Mathlib.LinearAlgebra.FiniteDimensional.Defs` from `LocalFirstOrderCoordinates`.
Their declarations are already provided by the coordinate module's public cotangent import.
The span-rank operations import in the new local coordinate module is proof-only.
The original public statement imports were preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound. Its steps 3 and 5 called the square-zero
coordinate arguments elementary, but they required substantial Lean construction and
instance management. The earlier proof dependency list contained no declaration supplying
these decompositions or the quadratic power-series ideal criterion. All three are now
stated and proved, rather than left as unsupported glue.

LeanSearch was unavailable with Internal Server Error for all attempted queries; the search
records say unavailable. LeanFinder, Loogle, direct Mathlib/library searches, and blueprint
searches found the component APIs but no existing theorem giving these decompositions.
The ancestor helper returned None for this newer module-created node, so the new nodes retain
the existing node's recorded blueprint ancestor and prepend this item to its via chain.

## New nodes

`lem-weil-pbc-local-first-order-coordinates`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-local-first-order-coordinates.json`, records the
proved equivalence for a Noetherian local ring with a residue section. It requires neither
completeness nor an external base field; those are only used to supply the section upstream.

`lem-weil-pbc-power-series-quadratic-ideal`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-power-series-quadratic-ideal.json`, records the
proved finite monomial-factor grouping argument over any commutative coefficient ring.

`lem-weil-pbc-power-series-first-order-coordinates`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-power-series-first-order-coordinates.json`, records
the proved quotient equivalence and its variables-ideal membership criterion.

No change record is needed: no existing interface changes, and no adaptations of other
modules are included. The unit's realized statements and steps are preserved.

## Second reading by N3

1. **No accidental visible changes.** Compared the delivered comparison module with the repository version. The existing theorem signature and all existing declarations are byte for byte unchanged; the three added modules are new files and no existing interface was edited. Verdict: pass.

2. **Proof and kernel checks.** Compiled all four modules with `lcompile.py --all`; compilation completed without errors or warnings. Searched the delivered Lean files for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none occur. The proofs use only ordinary definitions and imported theorems. Verdict: pass.

3. **Statements and split nodes.** Checked each new theorem against its DAG node and its edge cases (empty variable set, zero cotangent dimension, arbitrary characteristic, and zero coefficient ring). Each statement is strictly a component lemma needed by the comparison and has a source, proof description, and matching Lean declaration. Searches recorded in the node files found no existing equivalent theorem. Verdict: pass.

4. **Pruning and route.** The comparison proof uses the coefficient-section helper and all three coordinate lemmas; proof-only imports are kept only where used, while redundant development imports were removed as recorded above. The unit route and realized steps remain unchanged. Verdict: pass.

5. **DAG agreement.** Updated proof, proof dependencies, and proof origin agree with the Lean proof, and each added node records its module, declaration, statement, source, and proof. Verdict: pass.

Changed during second reading: added this review section to satisfy the delivery report contract; no Lean proof or statement changes were necessary.
