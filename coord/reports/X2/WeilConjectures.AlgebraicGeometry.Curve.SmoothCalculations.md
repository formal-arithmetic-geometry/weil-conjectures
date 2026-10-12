## What changed

Reduced C3 by splitting q = 2 from q > 2: the latter uses the existing C1 theorem.
The degree-two obligation is stated in the new proof-only module
`Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo`; its docstring explains the
Artin–Schreier, Ext comparison, arbitrary-coefficient, large-index and dimension-zero cases.
The original module imports it privately in place of the direct ArtinSchreierDimension import.
Updated `lem-sc-c3` to match the actual reduction. Existing signatures and definitions are
unchanged. The first writer's explicit `dsimp` in `constantModSheaf_curveCalculations` remains.

## Proved and sorry left

The C3 theorem `subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP` is reduced to the
new degree-two obligation and the existing C1 bound. The existing proofs of `Etale.nsmul_id_constantModSheaf`,
`Etale.isTorsion_constantModSheaf`,
`subsingleton_sheafH_constantModSheaf_of_two_lt`,
`subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine`, and
`constantModSheaf_curveCalculations` compile. The new intermediate `subsingleton_sheafH_constantModSheaf_of_charP_two` retains a sorry (node `lem-sc-c3-degree-two`). The remaining declarations retain their pre-existing
sorries: `finite_sheafH_constantModSheaf_of_ne_zero`, `finite_sheafH_constantModSheaf_of_isProper`,
`bijective_cohomologyMap_constantModSheaf_of_ne_zero`,
`bijective_cohomologyMap_constantModSheaf_of_isProper`,
`surjective_cohomologyMap_constantModSheaf_two`,
`assertions_constantModSheaf_of_ne_zero`, and `assertions_constantModSheaf_of_charP`.

## No longer needed

For `lem-sc-c3`, the old direct proof dependencies are replaced by `lem-sc-c3-degree-two`
and `lem-sc-c1`: `lem-sc-artin-schreier-dimension`, `def-sc-constant-sheaves`,
`def-weil-pbc-eight-curve-assertions`, `def-weil-pbc-primary-torsion`, and `def-weil-pbc-C3`
are no longer direct proof dependencies of C3. ArtinSchreierDimension remains needed through
the new intermediate theorem. No module becomes unreachable; no unit-level node is pruned.
The direct proof import `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` is replaced
by `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo`. The remaining original imports
carry the unchanged plans of the still-open declarations and are retained.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original new helper had an incomplete docstring proof,
was placed in the item's module instead of a new Sheaf module, copied unrelated historical
audit fields into its node, and did not update the C3 node's proof route. These are repaired.
The dimension-zero case matters because IsCurve means dimension at most one, whereas the
imported Artin–Schreier theorem assumes IsConnectedCurve (dimension exactly one). The imported Artin–Schreier dimension theorem is stated for the
`ZMod` constant sheaf and does not directly match the arbitrary coefficient ring formulation,
so it was not used as a false definitional shortcut.

## New nodes

Added `lem-sc-c3-degree-two`, isolating the degree-two Artin–Schreier calculation as the sole
remaining intermediate sorry used to prove the full C3 vanishing statement.

## Earlier second reading (a previous round; superseded)

The full C3 statement is reduced by a genuine degree split: only degree two is isolated as a new
intermediate theorem, while degrees above two use the existing C1 theorem. The new node records
that intermediate theorem.

## Second reading by X2

1. Compared both delivered modules with the repository baseline and checked the existing
   declaration table: no existing statement, definition, target signature or public import
   changes. The added helper is in a new Sheaf module and is imported only for the proof.
2. Inspected all proof bodies and scanned for prohibited constructs: no axiom, unsafe,
   opaque, extern, implemented_by or hollow definition. The seven original open theorems
   remain named and documented; the sole added sorry is the degree-two helper with its node.
   Both modules compile locally. The explicit #print axioms probes show only propext,
   Classical.choice, Quot.sound and sorryAx from the named open obligations. The two
   torsion helper lemmas use only the three allowed axioms. The delivery tool also
   probes every declaration and compiles the independent helper on the server.
3. The helper is a strict degree-two part of C3, not a restatement. Checked q = 2 and q = 3,
   the zero coefficient ring, Λ = Z, infinite-dimensional Λ/pΛ, and zero-dimensional C.
   Added the missing coefficient-extension argument and the large-index continuity theorem.
   Independent leanfinder, loogle and grep searches found no direct matching theorem;
   the required LeanSearch query returned Internal Server Error, recorded as unavailable.
   local library search found the existing ZMod result, Ext comparison and large continuity
   interface used in its proof plan. None is redeclared.
4. The C3 reduction uses C1 in degrees greater than two. The unit sk-thm-p1 still realizes
   C1 and C3 in its curve-calculation step; neither is bypassed. The No longer needed list
   accounts for every old C3 proof dependency absent from the new direct route, distinguishing
   dependencies still used through the helper. Existing unresolved proof plans are retained.
5. Updated C3 proof/proof_deps/proof_origin to the degree split. Rebuilt the new helper's node
   with a self-contained statement, current search results, matching Lean signature/location,
   provenance and actual proof dependencies. The unit record needs no change.

Changed: moved the helper to ConstantModCharPDegreeTwo; completed its docstring proof,
including arbitrary coefficients and dimension zero; corrected its node and the C3 route;
corrected the report's proof and pruning inventory. Final verification is recorded below.

Final local verification: both modules compiled after the existing large filtered-colimit
module reached the published build. Existing declaration signatures compare unchanged.
No new unsupported axiom is used. There remain seven original sorry declarations in the
item and one new, documented degree-two obligation; one of the original eight sorry
bodies has been reduced by a genuine proof. This is a partial delivery, not a claim that
C3 or the aggregate calculation is independent of all open lemmas.

Dry-run repair: the static validator groups Loogle and LeanFinder as one kind and also
requires LeanSearch. Ran the latter independently; its service returned Internal Server
Error and this is recorded without claiming a negative result. The dimension-zero route
now cites the existing zero-dimensional cohomology theorem directly, rather than attaching
a general affine bound to a node whose declared affine bound assumes dimension exactly one.

Final dry run: deliver3.py --no-push printed OK; both modules compile and preflight passes.
The delivery is correctly classified CODEX because it adds a helper module and node.
