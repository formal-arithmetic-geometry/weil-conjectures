## What changed

Proved `AlgebraicGeometry.derivedDirectImage_cohomology_coproduct` with its statement
unchanged, from two strictly smaller steps of the existing Stacks 08DZ argument.
The main module now imports `DerivedDirectImageTruncatedCoproduct` and
`DerivedDirectImageCoproductAffineTruncation`, plus Mathlib's sheaf affine-basis criterion.
Its proof establishes the naturality square by coproduct extensionality, evaluates it
on each affine open, cancels the right vertical isomorphism, and reflects the resulting
additive sheaf isomorphism back to module sheaves. This is a complete Lean proof.

Added one theorem per new module. The first comparison is only for a common lower
truncation, where the bounded-below spectral sequence applies. The second assertion
provides the two vertical maps over a single affine open, using the uniform upper bound
rather than the objectwise eventual-truncation clause. It does not include the target's
comparison or assume it invertible. The original nine ingredient modules are now divided
between these two new modules, with DAG proof steps and docstrings giving their full
remaining arguments. The target's DAG copy records the actual two-lemma combination.
No definition, existing signature, public import, unit statement or unit step changed.

Validation: all three modules compile together with `lcompile.py --all`, without warnings.
Checked the natural-language arguments against Stacks Tags 08DZ and 08D5 on the official
site because this machine's read-only literature tree omits perfect.tex. The new
assertions cover the empty family, zero objects, q<a, arbitrary integer truncation
indices and non-quasi-compact Y. In the affine lemma the left map is evaluation of the
sheaf coproduct map: no commutation of sections with coproducts is asserted.

## Proved and sorry left

Proved: `AlgebraicGeometry.derivedDirectImage_cohomology_coproduct`
(node `lem-pc-derived-direct-image-cohomology-coproduct`); no sorry remains in the item.

Remaining named whole-proof sorries added by this delivery:

- `AlgebraicGeometry.derivedDirectImage_truncated_cohomology_coproduct`, node
  `lem-pc-derived-direct-image-truncated-coproduct`.
- `AlgebraicGeometry.exists_derivedDirectImage_coproduct_affine_truncation`, node
  `lem-pc-derived-direct-image-coproduct-affine-truncation`.

These are two independent parts of the proof, rather than a renamed target.
The main proof requires both, proves the commuting square itself, and performs the
isomorphism cancellation and affine-basis gluing in Lean.

## No longer needed

Removed from the item's direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum`
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`
- `Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum`
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `Sheaf.Paper.HigherDirectImagePresheaf`

The old direct `proof_deps` removed from the item are:

- `lem-pc-derived-ambient-direct-sums`
- `lem-weil-pbc-quasi-coherent-module-direct-sum`
- `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections`
- `lem-sc-derived-k-injective-restrict-open`
- `lem-pc-derived-direct-image-uniform-truncation-bound`
- `thm-sp-truncation-e2`
- `lem-weil-pbc-qcqs-cohomology-direct-sum`
- `lem-weil-pbc-higher-direct-image-presheaf`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`

All nine are retained as planned dependencies of the new intermediate modules; their
nodes remain reached. Thus no original node or module is pruned transitively. Nothing
realizing a blueprint unit statement or step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction to the original statement or route was needed. The ingredient
theorems do not themselves state the common-truncation comparison or the uniform
familywise affine comparison; these are the two glue steps split off here. In particular,
objectwise eventual truncation cannot justify an index uniform over an infinite family.
The new affine statement explicitly uses the separate uniform upper-bound clause.

The local `/tmp` inode limit was exhausted during validation; temporary files were moved
to this item's sandbox via TMPDIR, without changing the project tools. The existing
`DerivedQCohDirectSumsAux` source was also inspected, but its compiled module was absent
locally; the delivery retains the original ambient/finite-sum/colimit route instead of
adding that import. No duplicate declaration of its closure result was added.

## New nodes

`lem-pc-derived-direct-image-truncated-coproduct` is the bounded-below spectral-sequence
part of Stacks 08DZ, specialized to the actual canonical lower-truncation cofan. Its
module is `Sheaf.AlgebraicGeometry.DerivedDirectImageTruncatedCoproduct`.

`lem-pc-derived-direct-image-coproduct-affine-truncation` is the affine uniform-bound
part of Stacks 08DZ using 08D5(2), with the actual canonical vertical maps in the square.
Its module is `Sheaf.AlgebraicGeometry.DerivedDirectImageCoproductAffineTruncation`.

Both inherit the item's chapter, unit and blueprint ancestry. No change record is needed.

## Second reading by B3

1. Compared the item with the repository by `diff` and byte comparison of its
   theorem signature. Verdict: unchanged signature, definitions and public imports;
   only proof imports and the proof changed. The other two modules are new.
2. Compiled all three modules with `lcompile.py --all`: no errors or warnings.
   Inspected every declaration and searched for prohibited constructs: exactly the
   two reported named whole-proof sorries remain, with no hollow definitions.
   A scratch `#print axioms` check of all three declarations returned only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` (the split claims).
   Thus the item has a complete reduction, not an axiom-free completed target.
3. Read both split statements and their word proofs against Stacks 08DZ, 08D5(2)
   and 015J. Tested the empty family, singleton, zero objects, q<a, arbitrary
   integer bounds and non-quasi-compact Y. Verdict: true, strictly separate parts
   of the argument, with no renamed copy of the original target. The affine
   assertion takes sections of a sheaf coproduct map and never exchanges sections
   with coproducts. Its uniform choice uses the upper-bound clause, not the
   objectwise eventual-truncation clause. Independent leanfinder, loogle and grep
   searches (recorded in searches.jsonl), plus rg over both source roots, found
   generic truncation and homology tools but no existing result closing either
   split claim. The existing affine truncation comparison is only objectwise.
   Neither remaining proof can be closed by a few-minute application of those tools.
4. Read the proof downward: naturality on coprojections gives the square; affine
   evaluation and cancellation give local invertibility; the Mathlib basis
   criterion and reflection give the sheaf isomorphism. Verdict: valid reduction.
   Proof-only imports are private, and each ingredient import of the split modules
   belongs to its documented remaining argument. All nine removed direct nodes
   are now explicitly listed above and remain transitive dependencies. Read
   dag/units/sk-thm-picard-duality.json: its realized arrays are empty; none of
   its statement or steps is replaced or bypassed. No transitive pruning.
5. Checked every node's Lean signature against the file, the dependency union
   against its proof steps, and all required new-node fields. Verdict: consistent.
   The existing node records the actual naturality/cancellation/gluing proof;
   the new nodes retain source, blueprint ancestry, chapter, unit and searches.

Second-reading changes: made the sufficient common bound a ≤ q-N and the
shifted vanishing threshold N+a-1 explicit in the affine theorem's word proof;
listed the nine old direct dependency node IDs in No longer needed; appended this
review. No Lean statement, definition or proof term was changed.
