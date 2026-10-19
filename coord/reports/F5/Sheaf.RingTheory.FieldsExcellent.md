## What changed

Proved `isExcellent_of_field` in `Sheaf.RingTheory.FieldsExcellent`, with its
statement, universe and visibility unchanged. The proof assembles the defining
conditions of excellence from existing declarations:

- `isGRing_of_isNoetherianRing_of_isAdicComplete`: the maximal ideal of a field
  is zero, and `IsAdicComplete.bot` gives the required completeness.
- `isOpen_regularLocus_of_residueField_finite_models`: for each finite purely
  inseparable residue-field extension L, take the top subalgebra B = L. A prime
  of a field is maximal, hence its residue field is module-finite over the field.
  Transitivity gives finiteness of L. The top-subalgebra equivalence transfers
  finiteness and regularity; x = x/1 supplies fractions, and the whole spectrum
  is a nonempty regular open, with the zero prime as witness.
- `IsRegularRing.isUniversallyCatenary`: Mathlib supplies regularity of a field.

The docstring and node's proof, proof dependencies and proof origin now describe
this argument. Added proof-only imports of `Sheaf.RingTheory.CompleteLocalGRing`
and `Sheaf.RingTheory.RegularRingUniversallyCatenary`; kept the J-2 criterion.
The public import and every existing signature remain unchanged.

The complete-local G-ring theorem and regular-ring universal-catenarity theorem
are generic commutative-algebra tools. Their statements apply with the hypotheses
checked above. No node of this unit supplies these general tools. This item is
below the unit level: `dag/units/sk-prop-a1-kummer.json` has empty realized entries.
The field-excellence input of the parent is retained. The maintainer may approve
these tool uses; this delivery writes no new tool approval and removes the obsolete
polynomial-chain approval.

Read the local Stacks sources: More on Algebra `proposition-ubiquity-excellent`
(07QW), `proposition-ubiquity-J-2` (07PJ), and `proposition-ubiquity-G-ring` (07PX);
Algebra `lemma-regular-ring-CM` (00NQ) and `lemma-CM-ring-catenary` (00NM).
Existing saved LeanFinder, Loogle and grep searches found no direct Mathlib
excellence theorem. Mathlib's residue-field, finiteness and regular-ring APIs
supply the elementary glue.

Validation: the resumed `deliver3.py --no-push` run compiled the final module
and passed preflight (dry-run commit `3185e63cd7`). A separate `lcompile.py`
request received no answer from the busy compile server; the delivery preflight
completed successfully. Both new proof imports pass `import_direction.py may`. Traversal
of statement dependencies, proof dependencies and proof-step uses found no path
back to this node from any of the three theorem dependencies (445, 575 and 93
nodes checked respectively). Lines are at most 100 characters. Delivery preflight
provides the final compile and axiom checks.

## Proved and sorry left

Closed 1 of 1 holes: `isExcellent_of_field` (node `lem-exc-fields-excellent`).
Added 0 holes. No `sorry` remains in the delivered module. No split-offs.
The proof uses existing stated dependencies, as required by stage 3; any holes
in those existing modules remain their own obligations and are not added here.

## No longer needed

Removed direct proof imports:

- `Mathlib.RingTheory.RegularLocalRing.Defs`
- `Mathlib.RingTheory.AdicCompletion.Basic`
- `Mathlib.RingTheory.RingHom.Flat`
- `Sheaf.RingTheory.GRing`
- `Mathlib.FieldTheory.PurelyInseparable.Basic`
- `Mathlib.RingTheory.FiniteType`
- `Sheaf.RingTheory.PolynomialRingMaximalChainHeightDifference`

The Mathlib APIs and defining notions remain available through the public APIs
of the retained imports. The dedicated polynomial-chain proof is replaced by the
existing regular-ring universal-catenarity theorem, following the route already
cited by Stacks 07QW. The explicit completion-map and geometrically-regular-fibre
calculation is replaced by specialization of the existing complete-local G-ring
theorem. No library module is withdrawn, and no global unreachability is claimed.

Former direct proof dependencies no longer used: `def-weil-pbc-adic-completion`,
`def-weil-pbc-flat-ring-map`, `def-weil-pbc-g-ring`,
`def-weil-pbc-finite-type-algebra`, and
`lem-weil-pbc-polynomial-ring-maximal-chain-height-difference`.
The G-ring and finite-type notions still occur through definitions and dependency
statements. Retained dependencies include the field regularity Mathlib leaf,
the J-2 criterion, finite purely inseparable extensions, and excellence's definition.
The completeness notion is cited as `def-weil-pbc-adically-complete-ring`.

## Where the brief, the DAG or earlier work was wrong

The original five-step plan can be shortened using existing generic G-ring and
universal-catenarity declarations. No statement correction is required. The proof
works for imperfect fields, in every characteristic and universe. The zero ring
is excluded by the original `Field` hypothesis, which includes nontriviality.

An earlier interrupted attempt specialized `CompleteLocalExcellent`. Its dry run
was rejected because that module is on `coord/route-pivot-dropped-modules.txt`.
The current delivery removes that import and dependency entirely and proves the
J-2 and assembly steps explicitly. No gate or launcher script was changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
