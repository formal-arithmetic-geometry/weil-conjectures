## What changed

Replaced `AlgebraicGeometry.diagonalConormal_affine_ideal_class`'s hole by a compiling
composition of the affine chart/kernel lift and the cotangent equivalence/unit comparison.
The proof constructs q as e composed with Mathlib's `KaehlerDifferential.fromIdeal`, restricted
to A-scalars. Surjectivity follows by composition, and the displayed section formula follows by
applying the comparison to a lifted kernel section. Added two proof-only imports, two new
modules and their nodes; updated the parent's proof dependencies. No existing signature changed.

## Proved and sorry left

Closed `AlgebraicGeometry.diagonalConormal_affine_ideal_class` (1 original hole).
Added two holes, so this is a decomposition rather than a complete axiom-free proof:

- `AlgebraicGeometry.diagonalConormal_affine_ideal_class_core`
  (`stage3-diagonal-conormal-affine-ideal-class-core`): tensor chart and actual kernel lift.
- `AlgebraicGeometry.diagonalConormal_affine_ideal_class_q`
  (`stage3-diagonal-conormal-affine-ideal-class-q`): cotangent equivalence and unit formula.

## No longer needed

No import removed from the existing item. Removed the unused public
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` import from the new core module.
All four former direct proof dependencies now occur in the split nodes:
`def-sc-diagonal-conormal`, `lem-pc-module-pullback-adjunction`,
`lem-weil-pbc-diagonal-immersion`, and `lem-weil-pbc-affine-conormal-sections-existence`.
They remain needed transitively, so no existing node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found in the original statement. The affine conormal theorem applies to
an actual closed immersion ideal module, not directly to the global diagonal's actual kernel.
Its public signature does not supply the required open restriction and unit comparison; that
comparison remains explicitly isolated in the new cotangent lemma. The new lemma assumes both
projection formulas and uses exactly the canonical algebra structure from f, preventing an
arbitrary ring equivalence or arbitrary algebra action from making its statement false.

Read the source online: Stacks Tags 08S2 (affine diagonal calculation), 01KJ (local closed
restriction), and 01R3 (cotangent quotient). LeanFinder found `diagonal_Spec_map`; Loogle found
`fromIdeal` and `fromIdeal_surjective`, used in the main proof; grep found no exact comparison.
LeanSearch returned an internal server error, which is recorded as unavailable.

Checked the empty affine chart (zero rings/modules), an open immersion (zero multiplication
ideal), and a general nonseparated morphism (only the local diagonal is required). The unit
route and original target signature are preserved. All three modules compile cleanly.

## New nodes

`stage3-diagonal-conormal-affine-ideal-class-core`, in
`lean/Sheaf/AlgebraicGeometry/DiagonalConormalAffineIdealClassCore.lean`, states the ring
coordinate and actual kernel-section part of the calculation. It neither constructs q nor
proves its surjectivity.

`stage3-diagonal-conormal-affine-ideal-class-q`, in
`lean/Sheaf/AlgebraicGeometry/DiagonalConormalAffineIdealClassQ.lean`, states the A-linear
cotangent equivalence and its unit formula for a supplied kernel section. It does not give
ring coordinates or kernel lifts. The parent constructs and proves surjectivity of q itself.
No change records are required.

## Second reading by U3

1. **Statements and interfaces.** Compared the delivered item module with the repository version byte for byte at the declaration signature; only the proof body and proof-only imports changed. The two added theorem signatures match their DAG node statements and preserve the original target unchanged. Verdict: pass.

2. **Proof checks.** Compiled all three modules with `lcompile.py --all`; they compile without errors. The target theorem has no `sorry`; the two intentionally split lower theorems retain exactly their named `sorry`s, with no `sorry` in definitions and no forbidden declarations. Their intended proofs are documented in the declarations and nodes. A scratch-copy `#print axioms` check for all three declarations returned only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected for this decomposition. The scratch copy was removed. Verdict: pass.

3. **Truth and strength of split statements.** The core statement isolates the affine tensor chart and actual kernel-section lifts; the q statement isolates the cotangent equivalence and unit formula under precisely the two projection formulas. Both are strictly simpler than the parent and retain the required hypotheses and conclusions. For empty U all rings and modules in the conclusion are zero; for an open immersion the multiplication ideal and conormal are zero; for a nonseparated morphism only the restricted diagonal U → U ×_V U must be closed. The two projection identities determine r on all pure tensors, so Q cannot use an arbitrary incompatible coordinate ring map. Checked against [Stacks 08S2](https://stacks.math.columbia.edu/tag/08S2), [01R3](https://stacks.math.columbia.edu/tag/01R3), and [01KJ](https://stacks.math.columbia.edu/tag/01KJ). Verdict: pass.

4. **Shortest route and pruning.** The parent now composes the two split results with Mathlib's `KaehlerDifferential.fromIdeal` and its surjectivity theorem. The two added parent imports are proof-only. Removed the unused public adjunction import from the new core module and added a plain import of AffineConormalSectionsExistence to the q module, matching its planned proof dependency. The old direct geometric dependencies remain transitively required by the split nodes. Independent searches used new LeanFinder queries about global kernel sections and actual diagonal pullback, Loogle on `fromIdeal_surjective`, and grep/rg for cotangent, conormal, and kernel sections. Results included `Scheme.ker_of_isAffine`, `Scheme.Hom.ker_apply`, and `Algebra.Extension.cotangentEquiv`; these concern quasi-coherent ideals or algebraic tensor quotients and do not supply the actual-kernel/open-restriction/unit comparison. Read both existing affine conormal section modules and Mathlib's definition of `KaehlerDifferential`/`fromIdeal`; no immediate closure of either geometric comparison was found. Verdict: pass; no pruning available.

5. **DAG and unit route.** Updated the parent node's `proof` and `proof_deps` to exactly match the composed Lean proof, and added complete node records for both split theorems with source, proof, searches, and Lean attachments. The unit `sk-thm-picard-duality` realized record is unchanged (its statement and step lists are empty); no realized unit step is bypassed. Verdict: pass.

Second reading changed only the new modules' imports and this report: removed the unused public adjunction import from Core, added the proof-only affine conormal dependency to Q, and listed all four former direct proof dependencies. The first worker's proof and split statements were retained. No existing statement or definition was changed.
