## What changed

Proved `AlgebraicGeometry.Scheme.strict_local_root_torsor_unique` in
`Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootTorsorUnique`, preserving its full
signature and existing docstring. Added the proof-only import
`Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity`.

The proof uses the existing cardinality and unit-separation theorem to show that
restriction along any ring map H → Ω is bijective on nth roots of unity. It lifts
the ratio of the two root images and checks equality on constants and the root.
Cancellation of the nonzero root image proves uniqueness. No new statements or
objects chosen from unproved existence theorems are introduced.

Updated the item's DAG proof and proof dependencies to match this argument.
The original regularity and divisor hypotheses remain in the statement; they
are not needed by this proof. Anonymous local hypotheses reference these binders
without changing the signature or disabling any linter.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.strict_local_root_torsor_unique`
(node `lem-sbc-strict-local-root-torsor-unique`).

Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
The roots-of-unity input is already proved in the library. The proof handles
positive n including n=1, arbitrary field Ω, and noninjective maps H → Ω;
injectivity is required only on the finite root group and follows from units.

## No longer needed

The former proof dependency `lem-sbc-root-algebra-regular-at-root`, module
`Sheaf.RingTheory.RootAlgebraRegularAtRoot`, is not needed by this proof and is
removed from the item's proof_deps. No claim is made that it is unused by other
parts of the library.

Imports removed: none. The three original public imports remain because they
provide the signature's root rotation, regularity, and regular-element notions.
The proof does not use the fixed-ring theorem in StrictLocalRootInvariants;
that existing public import remains required for the rootRotation definition.
No other planned proof dependencies are omitted.

## Where the brief, the DAG or earlier work was wrong

The previous DAG named root-algebra regularity as its sole proof dependency,
but that statement does not supply the roots-of-unity comparison used in its
proof text. The required input is the existing
`lem-sbc-strict-local-roots-of-unity`. The ratio argument itself is correct.
The containing-root regularity calculation is unrelated to comparing punctured
field-valued points. The unit's statement and route remain unchanged; its
realized lists contain neither of these intermediate nodes.

## Second reading by D2

1. **Interface comparison.** Compared the delivered module with the repository version. The
   theorem signature, hypotheses, conclusion, and docstring are byte-for-byte unchanged;
   only a proof-only import and proof body were added. The DAG change records only proof and
   proof-dependency metadata.

2. **Proof checks.** Compiled the module with `lcompile.py` successfully. The proof contains
   no `sorry`, axioms, unsafe declarations, opaque declarations, or hollow definitions. The
   argument uses the defining AdjoinRoot relation, the proved strict-local roots-of-unity
   theorem, and finite-cardinality injectivity/surjectivity; cancellation is justified by
   the supplied nonzero image. The n = 1 case is included by the same argument.

3. **Statement review.** No new Lean statements or split-off holes were introduced. The
   existing target statement is proved exactly as written, including all original
   regularity and maximal-ideal hypotheses.

4. **Route and pruning.** The proof takes the direct ratio-and-root-of-unity route. It uses
   `lem-sbc-strict-local-roots-of-unity` and no longer uses the former root-algebra
   regularity dependency. The proof-only roots-of-unity import is minimal for the added
   declarations; the three public imports remain required by the interface and definitions.

5. **DAG and unit consistency.** Updated `proof`, `proof_deps`, and `proof_origin` in
   `lem-sbc-strict-local-root-torsor-unique` to match the Lean proof. The unit record and
   its realized route are unchanged, and no unit step is bypassed.

Changed in this second reading: added this review record and corrected the item's DAG proof
metadata to name `lem-sbc-strict-local-roots-of-unity` as the actual dependency.
