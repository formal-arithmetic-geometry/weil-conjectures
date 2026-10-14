## What changed

Proved AlgebraicGeometry.affinePushforwardComparison_factorization in
lean/Sheaf/Algebra/Homology/AffinePushforwardComparisonFactorization.lean,
without changing its signature or docstring. The proof installs the already available
exactness instances for restriction of scalars followed by tilde, applies naturality
of DerivedCategory.homologyFunctorFactors.inv to the termwise comparison, then
ShortComplex.homologyMap_mapNatTrans to C.sc i. A private proved categorical
cancellation helper cancels the inverse and forward homology comparison. Explicit
functor coordinates avoid unfolding the homology comparison during cancellation.
The proof follows the existing two-step DAG plan. Imports are unchanged.
Second reading updates the existing node proof_origin to record the actual V4
proof and its Mathlib ingredients; proof and proof_deps remain unchanged.

## Proved and sorry left

Closed one hole: AlgebraicGeometry.affinePushforwardComparison_factorization
(node lem-pc-affine-pushforward-comparison-factorization).
No sorry remains in the item; no holes were added or split off.
The private cancellation helper is proved. The file compiled with lcompile.py
within the unchanged 60-second limit.
The argument is categorical and uses no boundedness or nonzero-ring assumption.

## No longer needed

None. The sole public import AffinePushforwardComparisonCoordinates supplies
the statement and its canonical comparison maps. No proof imports were added.
Both existing DAG proof steps and their sole dependency are used.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The earlier sandbox held only the original holed
module and search records; its searches correctly identified the needed Mathlib
naturality lemmas. Naive simplification unfolds ShortComplex.mapHomologyIso
into kernel and cokernel constructions; the private abstract cancellation helper
and explicit coordinates avoid that expensive unfolding.

## Second reading by V4

1. Compared the entire sandbox module with the repository version using diff.
   The only Lean changes are the closed theorem body and the private proved
   cancelComparison helper. The existing theorem signature and docstring are
   byte-for-byte unchanged; no definition or public import changes. PASS.
2. Read the concrete definition affinePushforwardCohomologyMapOfComparison in
   AffinePushforwardComparisonCoordinates. It constructs its maps explicitly;
   no arbitrary witness from an unproved existence theorem is introduced.
   Compiled a scratch copy with #print axioms for both declarations: the main
   theorem uses exactly propext, Classical.choice, Quot.sound; the helper uses
   propext and Quot.sound. No sorry or forbidden declaration is in the file.
   The scratch copy compiled in 52.0 seconds under the unchanged 60-second
   limit. The first ordinary compile timed out; subsequent validation is
   through the prescribed local compiler and delivery probe. PASS.
3. No new public statement, node, or split-off sorry is introduced. The private
   helper is just associativity and the inverse-isomorphism identity, valid in
   every category, including zero objects. The main argument applies to zero
   complexes, all integer degrees, and zero rings without extra assumptions.
   No boundedness or quasi-coherence condition is used. PASS.
4. Read Mathlib ShortComplex.PreservesHomology lines 685–728 and
   DerivedCategory.HomologySequence lines 30–51. The former supplies exactly
   the conjugation by mapHomologyIso; the latter supplies the localization
   comparison whose inverse naturality is used. Independently searched with
   LeanFinder for componentwise exact-functor comparison through localization,
   and rg for comparison factorization and app_homology in the library and
   upstream sources. Found generic naturality ingredients, no shorter exact
   affine factorization. The proof uses these generic ingredients directly.
   The sole public import is needed by the statement. All old proof_deps are
   used, so No longer needed is complete. Read sk-thm-picard-semicon.json:
   its realized fields are empty and no unit route is replaced. PASS.
5. Read lem-pc-affine-pushforward-comparison-factorization.json against Lean.
   Step 1 is hn plus expansion; step 2 is hh plus cancelComparison.
   Both use the existing comparison-coordinates node; proof_deps agrees.
   Updated stale proof_origin from the earlier split to the actual V4 proof,
   without changing statement, lean signature, blueprint, or unit. PASS.

Changed only the node proof_origin and this report. The Lean proof is retained
as written. Closed one existing hole; added zero holes; split off zero; pruned
none. This is a proof, not a decomposition.
