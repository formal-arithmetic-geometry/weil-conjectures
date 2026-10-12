## What changed

Filled both original theorem proofs without changing any signature, definition, visibility,
or import. Map the supplied isomorphism through each homology functor. For vanishing, compose
with `DerivedCategory.homologyFunctorFactors` and apply
`HomologicalComplex.isZero_single_obj_homology`. For the surviving degree, compose with
`DerivedCategory.singleFunctorCompHomologyFunctorIso`. In the shifted theorem first compose
with `DerivedCategory.singleFunctors.shiftIso (-i) i 0` to identify the shifted degree-zero
single object with the single object in degree `i`.

The existing three-step DAG plan is implemented unchanged: invariance, single-object
computation, and shift identification. No new nodes or intermediate statements remain.

## Proved and sorry left

Closed both original holes:
- `AlgebraicGeometry.cohomology_of_iso_invertible_single_zero`.
- `AlgebraicGeometry.cohomology_of_iso_locallyFree_shift`.

Both belong to `lem-pc-degree-zero-properties`. No sorry remains in the delivered module;
no holes were added. Local compilation passed without warnings.

## No longer needed

No imports removed and no DAG nodes or modules pruned. All three original public imports
supply types or instance classes appearing in the unchanged statements. No proof-dependency
modules were imported; Mathlib supplies all required computations.

## Where the brief, the DAG or earlier work was wrong

The historical Mathlib search recorded no match for the single-functor homology comparison.
The current Mathlib has `DerivedCategory.singleFunctorCompHomologyFunctorIso`, confirmed by
Loogle and its source. LeanFinder confirmed `HomologicalComplex.isZero_single_obj_homology`.
The original DAG proof is correct and requires no change.

## Second reading by E2

1. PASS: Compared the complete delivered module with the repository using `diff -u`.
   Only the two original `sorry` proof bodies changed. Both signatures, all docstrings,
   visibility, imports and universes are byte-for-byte unchanged; no definitions or
   change records were added.
2. PASS: Compiled the delivered module locally through `lcompile.py` without errors or
   warnings. Compiled a scratch copy with `#print axioms` for both declarations: each
   uses only `propext`, `Classical.choice`, and `Quot.sound`. No sorry, forbidden
   declaration mechanism, or data construction from an unproved existence remains.
3. PASS: No statements were split off, no new declarations or nodes were added, and
   there are no lower holes to validate. Read the Mathlib definitions of
   `singleFunctorCompHomologyFunctorIso`, `isZero_single_obj_homology` and
   `SingleFunctors.shiftIso`. The shift condition is `-i + i = 0`, so the argument
   covers zero, positive and negative degrees. The homology computation also applies
   to the zero object and rank zero; freeness and invertibility need not be used.
4. PASS: The proofs directly transport the Mathlib single-complex computations along
   the given isomorphisms. Searched the existing Lean library for single-object
   cohomology and shifted computations; no shorter complete replacement was found.
   All three public imports provide names or instance classes in the signatures.
   The old `proof_deps` is empty, so `No longer needed` is complete. Read
   `dag/units/sk-def-picard-f.json`: its realized statement/step lists are empty,
   and this delivery bypasses no unit or step.
5. PASS: Read `lem-pc-degree-zero-properties.json` in full. Its three elementary
   steps are exactly isomorphism invariance, single-degree homology computation,
   and the shifted single-degree identification implemented here. Its empty
   `proof_deps` and blueprint `proof_origin` remain accurate; no node edit is needed.

Changed only this report to record the independent second reading. The Lean proofs
and DAG were correct and were retained unchanged. Closed two original holes, added
zero holes, and pruned no modules.
