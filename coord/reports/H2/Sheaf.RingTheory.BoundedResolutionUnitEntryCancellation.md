## What changed

The target module now proves `ModuleCat.exists_bounded_resolution_unit_entry_cancellation` from a chain-level cancellation theorem and performs the projective-resolution, boundedness, finite-free, and rank bookkeeping. Two new helper modules provide the chain-level deformation-retract construction and the proved unit-entry specialization. Only the deformation-retract assembly remains a named `sorry`.

## Proved and sorry left

Closed original hole: `ModuleCat.exists_bounded_resolution_unit_entry_cancellation`. Also proved `ChainComplex.exists_nat_homotopy_cancellation_of_isUnit_entry`. Added one lower hole; this is a decomposition, with net zero holes.

Sorry left: `ChainComplex.exists_nat_homotopy_equiv_of_split_functionals` (node `lem-weil-pbc-nat-split-functionals-homotopy`).

## No longer needed

The original direct dependency `lem-weil-pbc-free-complex-unit-entry-splits` and import `Sheaf.Algebra.Homology.UnitEntrySplits` are no longer used directly by the target proof; the unit-entry helper uses the kernel-basis and split-functional route. The proof route also avoids `lem-weil-pbc-split-identity-from-functionals` / `Sheaf.Algebra.Homology.SplitIdentityFromFunctionals` and `lem-weil-pbc-split-submodules-stable` / `Sheaf.Algebra.Homology.SplitSubmodulesStable`. The original `def-weil-pbc-exact-sequence` is no longer a direct proof dependency (it remains a statement dependency of the chain-level helpers). `lem-weil-pbc-kernel-basis-unit-value` stays needed. These are local route removals, not claims about global target reachability.

## Where the brief, the DAG or earlier work was wrong

The DAG describes restriction and augmentation transfer in prose but provides no natural-degree deformation-retract interface. The delivery expands that missing interface in a new helper. Direct natural-degree kernels avoid extension to integer degrees. The hypothesis `j < d` is preserved but not needed by the implemented boundedness proof. Tags 00MT and 00OA were read online because the cited local TeX file is absent. Edge cases checked mathematically: `j=0` has zero outgoing differential by chain shape; off-pivot terms use the full submodule; zero basis sizes cannot occur at either supplied pivot; zero rings are allowed in both helpers; boundedness follows from injectivity even above the pivot. Search: LeanFinder found only generic homotopy/complex infrastructure, Loogle found quasi-isomorphism instances of homotopy equivalences, source grep found no split-functional homotopy theorem; LeanSearch returned Internal Server Error. The two-term direct-sum equivalence node concerns a different result and cannot assemble this deformation retract.

## New nodes

`lem-weil-pbc-nat-split-functionals-homotopy` records the natural-degree deformation retract from two split functionals. `lem-weil-pbc-nat-unit-entry-homotopy-cancellation` records the unit-entry specialization with finite bases and rank equations.

## Second reading by H2

1. Compared every delivered module with the read-only repository. The two helper modules
   are new. Restored the original theorem signature's final-line indentation and verified
   its entire signature byte for byte. No existing statement or definition changes;
   the revised proof docstring describes the implemented route.
2. All three modules compiled locally. Explicit `#print axioms` in a scratch copy showed
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the original theorem
   and both helper theorems. The sole
   direct hole is that named public theorem with its full proof docstring and node.
   No forbidden declarations or hollow definitions. All existential data and basis choices
   are local to theorem proofs; no arbitrary witness becomes a public data definition.
3. Checked the split-functional construction, both projection equations and the negative
   homotopy sign against Mathlib's convention. It is true for j=0, the zero ring, and the
   elementary identity complex R→R (the complementary terms are zero). Empty pivot index
   types rule out zero basis sizes. Its hypotheses contain no freeness, boundedness or
   augmentation, so it is strictly a lower step rather than a renamed original assertion.
   Its docstring and node give the complete restriction/retraction/homotopy construction.
   Independent LeanFinder search for cancellation of a contractible summand returned
   cylinder and Dold–Kan results; Loogle returned generic homotopy equivalence operations;
   grep and library searches found no matching natural-degree kernel-complement theorem.
   Read the existing proved integer-degree `nonempty_homotopyEquiv_of_split_identity`:
   it requires an already assembled integer splitting and does not supply the natural
   complement or the required degreewise injective map. Closing the remaining assembly
   requires substantial dependent chain-map/homotopy work, not a short lemma application.
4. Read from the original resolution theorem down to normalization, kernel bases and
   split-functionals. The augmentation, projectivity, zero-above-d, and rank arguments
   are actual checked reductions. Retained the kernel-basis dependency. The report lists
   both old direct proof dependencies removed and the avoided integer splitting modules.
   Read `dag/units/sk-thm-p1.json`, including `realized`: these subordinate cancellation
   nodes are not unit realization steps. The unit route is preserved. Checked Stacks
   [00MT](https://stacks.math.columbia.edu/tag/00MT) and
   [00OA](https://stacks.math.columbia.edu/tag/00OA) against the stated reduction.
5. Verified the three recorded Lean statements against the files, the union of each
   proof's `uses` against `proof_deps`, sources, creation/blueprint/chapter/unit metadata,
   and the new-node search records. Corrected the original node's inaccurate claim that
   bases are uniquely chosen: their existences are eliminated inside a theorem proof.

Changes: restored signature whitespace; minimized the new unit-entry helper's public
imports to Homotopy, ModuleCat.Basic, and Matrix.ToLin, removing proof-only QuasiIso,
Abelian and FreeModule.Basic imports from it. Added a plain ModuleCat.Abelian import
where its instances are actually needed, in the original module's proof. Retained
FiniteType after confirming it supplies the commutative-ring strong rank condition.
No proof hole closed or added by this second reading. Verdict: valid decomposition,
original hole closed and one strictly lower hole added; net zero holes.
