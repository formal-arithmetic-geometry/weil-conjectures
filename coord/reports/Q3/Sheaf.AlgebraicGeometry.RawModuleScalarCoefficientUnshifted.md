## What changed

Proved both theorems in Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted without changing any existing signature, definition, or public import. Added proof-only imports of WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor, Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquareCore, and Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition.

The shift proof uses three proved private bounded-below comparison helpers, following the existing private helpers in RawModuleScalarCoefficientSquare. The coefficient proof specializes the generic source-square core using the canonical sheaf composition equation, inverts that equation, and cancels the derived comparison. Updated both nodes to record the actual proof dependencies. No new public statements or nodes were needed; the unit route is unchanged.

Searches run: msearch leanfinder for shift compatibility of derived natural isomorphisms, loogle for CategoryTheory.NatTrans.CommShift, and grep for mapDerivedCategoryPlusCompIso. Local rg found the exact proved helpers and the generic source-square theorem. The generic comparisons and canonical sheaf equation suffice, including identity morphisms and zero coefficients.

## Proved and sorry left

Closed 2 holes:
- AlgebraicGeometry.Etale.rawModuleScalar_derivedPullbackIso_commShift (lem-sbc-raw-scalar-derived-pullback-shift).
- AlgebraicGeometry.Etale.rawModuleScalar_coefficient_unshifted (lem-sbc-raw-scalar-coefficient-unshifted).

No sorry remains in the item. No holes added or split off. All private helpers are proved.

## No longer needed

No original imports removed. Both nodes no longer need lem-sbc-raw-scalar-source-square, module Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare: the shift proof is independent of the source square, and the coefficient proof directly specializes its proved generic core with the canonical sheaf equation. Consequently the coefficient argument does not need the wrappers in Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors (def-sbc-raw-scalar-source-factors) or Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso (def-sbc-raw-scalar-derived-pullback-iso). These are local dependency prunings; other importers may still need those modules. The generic core and sheaf composition nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

The shift node incorrectly listed the source square as a proof dependency: shift compatibility follows from the derived comparison API alone. Also, importing the concrete source-square module would introduce its RawModuleScalarComparison.derivedPullbackIso abbreviation, colliding with the existing definition of the same name in this item. The proof avoids that collision by using the core theorem directly, with exactly the same identity-map specialization and inversion argument. No interface repair is part of this delivery.


## Second reading by Q3

1. Compared the complete module with the repository version. PASS: all existing
   signatures, the derivedPullbackIso definition, docstrings, and public imports
   are byte-for-byte unchanged. Only proof bodies, three private proved helpers,
   and three proof-only imports were added. No interface change record is needed.
2. Compiled the delivered module locally with lcompile.py, without errors or
   warnings. Inspected every proof and the definition: no sorry or forbidden
   declaration is present. A scratch copy prints axioms for the definition,
   both public theorems, and all three private helpers; each uses only propext,
   Classical.choice, and Quot.sound.
3. No statement was split off and no hole was added. The helpers establish
   bounded-below comparison compatibility by reflection through the fully
   faithful inclusion; they do not assume the item. The coefficient proof
   specializes the already proved generic core and the canonical sheaf equation.
   Identity arrows and zero coefficients require no nonzero or cancellation
   hypothesis: cancellation is exclusively by canonical isomorphisms.
4. Searched lean/Sheaf, the upstream exact-functor modules, and Mathlib's
   DerivedCategory/ExactFunctor for bounded-below comparison shift instances
   and compatibility lemmas. The matching helpers elsewhere are private
   (including the caller, which cannot be imported without a cycle); the
   public unbounded instances are used here. Each added import supplies a
   proof ingredient; the original public import supplies the signatures.
   The sole old proof dependency, lem-sbc-raw-scalar-source-square, is reported
   as no longer needed for both nodes. The unit sk-lem-failure-field and its
   realized fields are unchanged; this is a calculation below its steps.
5. Compared both node diffs and read their dependency statements. PASS: only
   proof, proof_deps, and proof_origin changed. The coefficient node names
   exactly the generic core and sheaf composition used; the shift node records
   its upstream API argument without a spurious source-square dependency.
   No new node or statement change is hidden in the delivery.

Second reading changed only the report: clarified that no new *public*
statements were introduced and recorded this independent review. The Lean
proofs and node updates needed no repair.
