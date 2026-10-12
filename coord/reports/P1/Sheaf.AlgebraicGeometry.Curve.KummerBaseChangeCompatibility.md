## What changed

Completed `AlgebraicGeometry.kummer_base_change_compatibility` without changing its
signature. The proved private helper `kummer_comparison` constructs the short-complex
morphism using additivity and the kernel universal property. Both Kummer sequences are
short exact because the ground-field unit n maps to global sections of C and then P.
The existing pullback ladder and `Sheaf.H.map_δSucc` give the three cohomology squares.
The existing Picard pullback theorem gives degree zero and degree one. Uniqueness of
left adjoints identifies its tensor pullback with the pullback defining `Pic.map`.
Base-change curve structure is transported to the specified pullback square.

Added `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` for the strictly
smaller affine Picard-torsion clause. Its canonical subtype map is well defined by
preservation of powers. The final existential map in the item is this explicit map,
with bijectivity supplied by the new theorem and its underlying-value formula proved
by reflexivity. The new statement has the compactification/Jacobian argument in its
docstring and node; the main proof is a real combination of independent parts.

Updated the item's proof route and dependencies. Replaced broad public imports with the modules providing the signature, and
added the new module and the Picard comparison theorem as plain proof imports. Compiled
the two modules in import order through lcompile.py. No target or definition changed.

Repair of return C1/C4: added plain imports of Curve.Compactification and
Curve.PicAffineQuotient to the affine split module, and their nodes to the first proof
step and proof_deps. Its node and docstring now explicitly obtain the compactification,
Jacobian, and nonempty boundary from the cited results. Injectivity on all Jacobian
points is justified separately by recovery of the image point and residue-field map
after the injective field extension, rather than attributed to the torsion estimate.

## Proved and sorry left

Proved `AlgebraicGeometry.kummer_base_change_compatibility` (the item's one original
sorry) and the private helper `AlgebraicGeometry.kummer_comparison`.

The delivery leaves exactly one sorry:
`AlgebraicGeometry.affine_picard_torsion_base_change`, node
`lem-sc-affine-picard-torsion-base-change`. Its proof is exactly `:= by sorry`.
Existing imported theorems can still depend on sorry; these are intended stage-3
successor items, not new gaps hidden in this proof.

Edge checks of the new statement: n=1 gives singleton torsion subtypes; n=0 is excluded;
the characteristic-dividing case is excluded; genus-zero affine curves have trivial
Picard groups; the supplied arbitrary pullback square is accounted for by canonical
pullback isomorphism transport. The map is specifically Pic.map, not an unspecified
bijection of two groups.

## No longer needed

Removed these direct plain imports from the item:
- `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility`;
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`;
- `WeilConjectures.AlgebraicGeometry.Curve.Brauer`;
- `WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic`.

Changed `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
from a plain to a public import because the signature uses its `Etale.cohomologyMap`.

The first and fourth remain mathematical dependencies of the new affine torsion node;
they are not globally obsolete. `def-sc-field-extension` remains supplied transitively.
`thm-av-final` is similarly a dependency of the new affine node rather than a theorem
applied in the main proof. Second reading also removed direct imports of Curve.Kummer, Curve.Affine,
Picard.Jacobian, AbelianVariety.Final, and EtaleCohomologyPullbackDegreeZero.
Public imports now provide only the signature: Curve, Sites.Kummer, Sites.GmPicard,
and UpperLowerStar.TopologicalInvariance. GmPicardPullback is a plain proof import.
The new affine node imports its six planned mathematical dependencies privately;
they remain needed for its documented successor proof.

Every old proof dependency absent from the new direct proof route is listed here:
`lem-sc-pic-affine-base-change-compatibility`, `thm-av-final`, and
`lem-sc-divisible-quotient-torsion` move to the affine split theorem;
`lem-weil-pbc-cohomology-pullback-degree-zero` is supplied by the Picard comparison;
the remaining pruned dependencies are `lem-sc-kummer-les`,
`lem-sc-brauer-zero-all-curves`, and
`lem-weil-pbc-right-derived-universal-delta-functor`. No Brauer vanishing or identification
of the individual cohomology groups is needed to prove naturality of their maps.
`Sheaf.H.map_δSucc` proves the needed connecting-map naturality directly, so the generic
universality theorem is unnecessary here. The separate direct dependency
`lem-weil-pbc-cohomology-pullback-degree-zero` is unnecessary because the units assertion
is already the second clause of `lem-sc-h1-gm-pic-pullback`.
No blueprint unit is bypassed; the unit record's realization lists are empty and the
Kummer naturality and affine Jacobian-torsion steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt's `base_change_hypotheses : True` proved no required clause;
it has been removed. The Kummer morphism and long-exact-sequence ladder can in fact be
constructed from available declarations. Kernel lifting handles the former, and the
already proved ladder plus `Sheaf.H.map_δSucc` handles the latter.

The original node planned to invoke Brauer vanishing and the specialized Kummer LES
identifications, but its Lean conclusion only asks for naturality, so those invocations
are unnecessary. `GmPicardPullback` states the Picard assertion on invertible modules
using tensor pullback, whereas this item states it on Picard classes using
`Modules.pullback`; the proof supplies the missing representative and adjunction glue.
LeanSearch was unavailable (Internal Server Error); LeanFinder and Mathlib source grep
found no affine Picard torsion base-change theorem.

The returned delivery omitted the sources of compactification and nonempty boundary
in its split-node proof plan (C1), and incorrectly attributed injectivity on all points
to the abelian-variety estimate (C4). Both descriptions and dependencies are repaired.

## New nodes

`lem-sc-affine-picard-torsion-base-change`, in
`dag/nodes/sec-curve-estimates/lem-sc-affine-picard-torsion-base-change.json`, records
`AlgebraicGeometry.affine_picard_torsion_base_change` in the new module
`lean/Sheaf/AlgebraicGeometry/Curve/AffinePicardTorsionBaseChange.lean`. It isolates only
the affine Picard torsion assertion, with the Jacobian quotient, divisibility, torsion
comparison and arbitrary-pullback transport argument specified for the next worker.
Import-visibility change record: `coord/changes/kummer-base-change-proof-imports.md`.
Existing signatures and definitions are unchanged.


## Earlier second reading (a previous round; superseded)

1. PASS: diff against the repository shows the existing theorem's signature is byte
   for byte unchanged, with no changed definition or added hypothesis. Restored its
   original docstring. Only the proof, private helper, and imports change in that file.
   The split theorem is new. The public-import adjustment has change record
   `coord/changes/kummer-base-change-proof-imports.md`; the sole direct importer
   privately imports the item and independently imports its removed geometric inputs.
2. PASS: both modules compile locally in import order without errors or warnings.
   There is exactly one named theorem with `:= by sorry`, as listed above, no definition
   with sorry, and no axiom/unsafe/opaque/implemented_by/extern. Scratch axiom probes
   verify the private helper uses standard axioms; the main proof and split theorem
   also use sorryAx through the explicitly reported open dependencies.
3. PASS: the new theorem is strictly the affine torsion clause, not the entire item.
   Its canonical map is well defined by preservation of powers. Reviewed compactification,
   boundary subgroup identification, injectivity, divisibility correction, and torsion
   lifting. For n=1 both torsion subtypes are singleton; n=0 and characteristic divisors
   are excluded. IsConnectedCurve requires dimension exactly one, so the chosen affine
   compactification has nonempty boundary. Genus zero gives trivial affine Picard groups.
   The canonical pullback transport accounts for arbitrary P. The docstring gives the
   complete mathematical argument and a source, and the node states the same claim.
   Independent LeanFinder, Loogle, Mathlib grep and project rg searches found no theorem
   closing this clause. One Loogle query did not know the project's Pic identifier;
   a second used Mathlib's torsionBy identifier. Closing the geometric argument requires
   substantial formalization and cannot be done as a short repair.
4. PASS after import repair: the kernel lift and direct connecting-map naturality
   give a short route for all non-affine clauses. No redundant new restatement is used.
   Replaced broad public imports by the signature's provider modules, made the Picard
   comparison a plain proof import, and added plain imports for the split node's planned
   proof dependencies. The No longer needed section now enumerates every old dependency
   missing from the new direct route, distinguishing those moved into the split node.
   Read dag/units/sk-prop-ext-invariance.json: realized lists are empty; the Kummer
   naturality and affine compactification/Jacobian route are preserved.
5. PASS: only proof, proof_deps, proof_origin differ in the existing node. Its four
   steps follow the Lean proof; dependencies are exactly their union. The new node has
   source, searches, status split, creation metadata, blueprint origin, chapter, unit,
   and a verbatim Lean statement. Its imports now expose its plan to the successor.

Changes by second reader: repaired import visibility and removed unused broad imports;
restored the existing declaration docstring; completed the pruning list and corrected
this report's earlier claim that every public import was retained. No proof body or
statement needed repair. Added the import-visibility change record requested by preflight, with the full
downstream table and direct-importer review. Local compile, axiom probes, and delivery dry run are recorded
by the prescribed tools.

The sole direct importer, ConstantInvariance, also compiled successfully in a scratch
copy against the revised sandbox modules (15.8 s); no adaptation was necessary.

## Second reading by P1

1. PASS. Independently diffed the delivered item against the current repository.
   The existing theorem signature is byte for byte identical, and its original
   docstring is unchanged. No existing definition or target statement changes.
   The changed public imports have the explicit import-change record.
2. PASS. Both delivered modules compiled cleanly through lcompile.py in import
   order (2.7 s and 17.4 s). Independently scanned the delivered sources: exactly
   one sorry, in the reported named affine theorem, and no forbidden declarations
   or hollow definitions. Scratch #print axioms probes show only propext,
   Classical.choice and Quot.sound for the private comparison helper, and these
   plus sorryAx for the main theorem and the explicitly open affine theorem.
3. PASS. The split is only the affine torsion clause, strictly smaller than the
   original conjunction. Checked its hypotheses and canonical Pic.map subtype
   map, n=1 (singleton types), excluded n=0 and characteristic divisors, genus-zero
   curves, and arbitrary pullback transport. Read the compactification, Picard
   quotient compatibility, Jacobian representation and abelian-variety estimate
   declarations. The quotient injectivity and divisibility-correction proof in
   words is valid; injectivity of all rational points is justified separately.
   Independent LeanFinder search for finite-order line-bundle pullback, Loogle
   search for torsionBy/Bijective, Mathlib grep with different words, and project
   rg found no theorem closing this clause. It requires substantial geometric
   formalization, not a short repair. Its source, complete proof and node agree.
4. PASS. Read the proof from its conclusion downward: kernel lifting constructs
   the comparison, the existing pullback ladder and map_deltaSucc provide the
   squares, and the Picard pullback theorem plus uniqueness of left adjoints
   provide the degree-one formula. No shorter available route found. Signature
   imports are public, proof imports private. The pruning section enumerates
   every old proof dependency missing from the new direct route. Read the unit
   record: realized lists are empty and its Kummer and affine Jacobian routes
   remain intact. Updated stale downstream information: there are now three
   direct plain importers, not ConstantInvariance alone. ConstantKummerNaturality,
   ConstantLowDegreeBaseChange and RootTrivializationBaseChange all compile in
   scratch copies against the revised sandbox modules (24.0, 3.9, 2.1 s).
5. PASS. Existing node changes only proof, proof_deps and proof_origin. Both nodes'
   proof_deps equal the union of step uses. The new node's Lean statement matches
   the source verbatim and it carries the required source, search, split status,
   creation, blueprint, chapter and unit metadata. The main node's four steps
   match the actual proof and the split node documents its successor argument.

Changes in this reading: refreshed the import-change record to the current three
plain importers and all 112 transitive downstream modules, and added this independent
review. No Lean proof, statement, definition, import or node needed further repair.
The earlier review's single-importer assertion is historical and superseded here.
