## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.AmplePullback` by a complete Lean proof of
`AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_of_isAffineHom`, with its signature
unchanged. The proof installs the compactness supplied by ampleness, obtains compactness of the
source from the quasi-compact affine morphism, chooses the affine nonvanishing open at the image
of each point, and pulls that open back using `IsAffineOpen.preimage`. It rewrites the new section's
nonvanishing locus to finish the ampleness criterion.

Added the proof-only import
`Sheaf.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback`. This new module states
the generic algebraic section/locus transport needed for the proof. Its sole theorem has no
ampleness, compactness or affine-morphism hypothesis: it treats one given section of one tensor
power, independently of any affine cover. Its docstring and node give the tensor-power induction,
section construction, quotient-to-fibre calculation and field-extension nonzero argument.

Updated the item's proof, proof dependencies and proof origin to describe the actual Lean route.
Both delivery modules compile cleanly through `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_of_isAffineHom`
(node `lem-weil-pbc-pullback-ample-invertible`). No direct sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_nonvanishing_pullback`
(node `lem-weil-pbc-tensor-power-section-nonvanishing-pullback`). This is a decomposition,
not a sorry-free proof: one upper hole closed, one lower hole added, net zero direct holes.
The unchanged signature still uses the existing `invertible_pullback_tensor` theorem for its
invertibility instance; that dependency's existing sorry was not altered or counted as added.

An independent sandbox compiler experiment verifies the fibre criterion explicitly using
`TensorProduct.quotTensorEquivQuotSMul`, its `mk_one_tmul` formula, quotient membership, and
reflexivity identifying the two presentations of the module germ. This experiment does not
add a library declaration or a hole.

## No longer needed

No existing import was removed: all five public imports supply names or structures in the
unchanged statement, and changing their visibility would change the public interface.

The item's proof no longer needs `lem-weil-pbc-affine-scheme-qcqs`, its separate finite affine
cover argument, or a new theorem for finite unions of compact opens. Quasi-compactness follows
from the already established affine-morphism quasi-compact instance and
`QuasiCompact.compactSpace_of_compactSpace` (the existing Mathlib leaf
`lem-weil-pbc-qcqs-morphism-permanence`, clause (2)). The affine-morphism base-change and
source-affineness clauses are unnecessary here: `IsAffineOpen.preimage` gives the desired
open directly from the definition `pqf-def-affine-morphism`.

No additional Sheaf modules implementing these geometric steps were imported. This does not
assert that the removed dependency is unreachable from every other target route.

## Where the brief, the DAG or earlier work was wrong

The original DAG step says the binary tensor/fibre theorem directly supplies the tensor-power
section used by the ampleness criterion. Its Lean signature supplies binary tensor comparisons,
section formulas and fibres, but not a tensor-power section with inverse-image nonvanishing locus.
This transport therefore remains the named algebraic intermediate theorem of this delivery.

The original finite-cover argument is valid but unnecessary in Lean because Mathlib already
proves that an affine morphism is quasi-compact and that a quasi-compact morphism with compact
target has compact source. No existing statement or definition was changed; no mathematical
statement dispute was found. The item's node is not a unit statement or realized unit step in
`dag/units/sk-thm-p1.json`; the unit's route is unchanged.

Local Stacks source files were absent. The source statements and the explicit inverse-image
nonvanishing equality were checked on the official Stacks pages for Tags 0892, 01CD and 01CT.

## New nodes

`lem-weil-pbc-tensor-power-section-nonvanishing-pullback` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-tensor-power-section-nonvanishing-pullback.json`.
Its module is
`lean/Sheaf/AlgebraicGeometry/Modules/TensorPowerSectionNonvanishingPullback.lean`.
It isolates step 1 of the original argument. For any scheme morphism, invertible module,
positive tensor exponent and section, it provides a section of the corresponding power of the
pullback whose nonvanishing locus is the inverse-image locus. The proof has no geometric
ampleness conclusion. Empty schemes, zero sections, identity morphisms and positive exponent
one obey the same fibre argument; no nonempty or surjective hypothesis is needed.
Blueprint searches for "pullback nonvanishing", "nonvanishing" and "tensor power" found no
existing blueprint statement of this fact. Logged LeanFinder, Loogle and grep searches found only partial
matches, including the quotient-to-fibre tensor equivalence. The required LeanSearch
query was also run but its service returned an Internal Server Error, recorded as unavailable. No change record is required.

## Second reading by H2

1. Compared both delivered modules with the repository: the section-transport module is new;
the existing ampleness theorem's signature and docstring are byte-for-byte unchanged. Its only
changes are the proof and one plain, proof-only import. No existing definition changed.

2. Both modules compile cleanly with `lcompile.py --all`. Scratch copies with `#print axioms`
for both declaration names show exactly `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`. The latter is expected: the split theorem remains open, and the existing
`invertible_pullback_tensor` in the unchanged signature is also open. There is exactly one
direct delivered hole, the named transport theorem; no hollow definition or forbidden
declaration is present. The worker's quotient-to-fibre scratch calculation was also checked.

3. Read the new theorem, its docstring, and its node against Stacks
[0892](https://stacks.math.columbia.edu/tag/0892),
[01CD](https://stacks.math.columbia.edu/tag/01CD), and
[01CT](https://stacks.math.columbia.edu/tag/01CT). Its argument constructs a section by the
pullback unit and tensor-power comparison, identifies fibre values, and uses faithful scalar
extension of fields. Module isomorphisms preserve the maximal-ideal submodule. Zero sections
give empty loci, identity morphisms preserve the locus, exponent one is ordinary section
pullback, and empty schemes impose no point conditions. No surjectivity is needed. The
statement isolates section transport without compactness, affine opens, or ampleness, so it
is strictly a part of the argument, not a restatement of the item. Closing this transport
theorem requires additional formal section and stalk bookkeeping, beyond a short repair.

Independently searched LeanFinder for "section of line bundle under inverse image has
vanishing set equal to preimage" and Mathlib grep for
`generatingLocus|vanishingLocus|nonvanishingLocus`. Results concern structure-sheaf zero loci,
not this module section. Local searches found the proved
`nonempty_pullback_tensorPow_iso` for the usual pullback and only the one-sided
`preimage_generatingLocus_le`; neither states the tensor-formula section/locus equality.
The existing binary tensor/fibre theorem supplies ingredients but not this conclusion.

4. Checked the proof from the ampleness goal down: compactness follows from the affine
quasi-compact instance; the affine neighborhood at `g y` pulls back by `IsAffineOpen.preimage`;
the locus equality rewrites the final criterion pointwise. All added imports are needed by
statements or proofs, and the new import is plain. The sole old dependency removed is
`lem-weil-pbc-affine-scheme-qcqs`, already listed above. No module is claimed globally pruned.
Neither node is in `dag/units/sk-thm-p1.json`'s realized statement or steps; that route stays.

5. Compared the existing node diff: only `proof`, `proof_deps`, and `proof_origin` changed.
Their union names the compactness criterion, affine permanence instance, quasi-compact
source lemma, affine-preimage definition, new transport theorem, and the invertibility
theorem used in the signature. The new node matches its Lean signature, source, proof in
words, searches, creation record, chapter and unit. Its proof dependencies match the planned
tensor comparison and residue-quotient calculation.

Verdict: valid decomposition, one upper hole closed and one strictly simpler hole added,
net zero direct holes. Second reading changed only this report; the Lean and nodes required
no repair. Temporary axiom-probe source files were removed before delivery.
