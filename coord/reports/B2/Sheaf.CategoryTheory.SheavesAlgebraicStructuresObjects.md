## What changed

Retired Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects, the depth-zero duplicate listed
in coord/retire-items.tsv, through deleted.txt. Removed its unused finite-products wrapper and
redirected all seven direct consumers to the official upstream library. All seven consumers
replace a private import or drop an already redundant one; the three held consumers only drop
private imports. LocalizationInverseImageCoherence also drops its unused
ExactFunctorDerivedFunctor proof import to repair repeated 60-second timeouts after retirement;
the declaration and proof source is unchanged. All declarations and proofs in consumers stay
verbatim. The DAG attachment now records the unchanged upstream theorem and its exact signature.
Change record: coord/changes/retire-sheaves-algebraic-structures-objects-B2.md.

The return at head 01cb941338 is repaired: the change record names
Sheaf.CategoryTheory.LocalizationInverseImageCoherence and its current holder A4. The change
record also records B4 as the current holder of
Sheaf.CategoryTheory.Sites.GeometricInverseImageExact. The Localization consumer copy is
refreshed from current main, preserving all subsequently landed proofs and reapplying only the
two private import removals.

## Proved and sorry left

The assigned module had zero holes and is withdrawn: 0 of 0 sorries closed, 0 added, 0 split
off. No proof completion is claimed. The existing proved theorem
CategoryTheory.sheaves_algebraicStructures_objects supplies all algebraic-object clauses;
Mathlib's CategoryTheory.Sheaf.instHasFiniteProducts supplies finite products. Existing holes in
consumer modules are unchanged; this delivery adds no theorem or hole.

## No longer needed

The entire Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects module and its unused
CategoryTheory.sheaves_algebraicStructures_objects_with_finiteProducts wrapper are pruned. All
seven imports of that Sheaf module are removed. The unused private import
Sheaf.CategoryTheory.ExactFunctorDerivedFunctor is also removed from
LocalizationInverseImageCoherence to avoid the elaboration blow-up described below. Its
duplicate direct Mathlib imports and private abelian/ring component imports disappear with it;
the unchanged upstream proof still needs both component nodes, so neither dependency is claimed
as pruned. The node lem-weil-pbc-sheaf-algebraic-structures-objects remains realized upstream.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief is stale for this item: its current Lean module has no sorry.
coord/retire-items.tsv and the human's 2026-10-20 hand-off in coord/changes/retire-sheaf-
twins-20261020.md identify the actual work as retirement. The DAG's declaration name was already
upstream's, but its module and file were still those of the duplicate wrapper. The upstream
theorem omits only an explicit Nonempty finite-products conjunct, which is supplied
unconditionally by an existing instance. No user calls the extra wrapper. No upstream
declaration, definition, public import, unit realization, or target type is changed.

## Forced adaptations

Sheaf.CategoryTheory.ConstantLeftModuleInverseImage (H3) and
Sheaf.CategoryTheory.LocalizationInverseImageCoherence (A4) lose the private import of the
retired module. Sheaf.CategoryTheory.Sites.GeometricInverseImageExact (B4) drops the obsolete
private import; its existing imports supply the API. LocalizationInverseImageCoherence
additionally loses its unused private import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor. No
public import or declaration changes. This is necessary to remove the final references to the
retired module under the explicit retirement instruction. A physical withdrawal would make those
imports unavailable; the delivery tool represents withdrawal as an empty module. The existing
imports already expose the upstream API. All three held consumer adaptations are included in the
compile set. All seven consumer modules compiled without warnings on the project server (2.0 to
17.8 seconds per file).

The first standalone set compiled all seven consumers (2.0 to 17.8 seconds each), but subsequent
delivery and standalone runs repeatedly timed out at 60 seconds on
LocalizationInverseImageCoherence. The original with its obsolete import also timed out, so the
timeout is not attributed solely to removal of that import. A whole-file low-heartbeat
diagnostic localized the cost to equality checks in localizationInverseImage_comp and
localizationComparisonDerived_id. An imports-only diagnostic compiled; the full file without
unused proof imports compiled in 18.8 seconds. Narrowing that change to removal of just
ExactFunctorDerivedFunctor compiled the complete unchanged proof source in 18.2 seconds. That
import is unused: the file's public upstream ExactFunctor import already supplies its
definitions. No definition was split or changed, no proof was replaced by sorry, and the
60-second limit was preserved. This one extra import removal is retained to make the necessary
consumer adaptation compile reliably.

The repair dry run rejected an unnecessary replacement import in B4's module. That adaptation
now only drops the obsolete private import, preserving its other imports.

## Forced adaptations

### Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

### Sheaf.CategoryTheory.LocalizationInverseImageCoherence
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

### Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
