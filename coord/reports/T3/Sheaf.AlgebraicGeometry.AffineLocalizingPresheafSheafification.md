## What changed

Replaced the proposed circular reuse in
`Sheaf.AlgebraicGeometry.AffineLocalizingPresheafSheafification` by a genuine
reduction. The private, fully proved `isIso_unit_on_basis` establishes the
canonical sheafification-unit comparison using Mathlib's cover-dense basis
inclusion, induced-topology sheaf equivalence, and sheafification universal
property. The original theorem evaluates this comparison on an affine open
and reflects isomorphisms through the forgetful functor to abelian groups.
Its existing signature, docstring, visibility and definitions are unchanged.

Added `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafBasisSheaf` with the named
remaining localization-to-affine-basis sheaf-condition obligation. Its docstring
contains the principal-localization and affine-refinement proof. Both modules
compile locally without errors or warnings. The item imports the new module
and Mathlib's sheaf-condition/sites comparison only for its proof. The new
module's four public imports supply types occurring in its statement.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.isIso_sheafificationUnit_app_of_affine_localizing`
(node `lem-pc-affine-localizing-presheaf-sheafification`). The private categorical
helper `isIso_unit_on_basis` is fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.isSheaf_affineBasis_of_localizing`
(node `lem-pc-affine-localizing-presheaf-basis-sheaf`), in its own module.
This is a decomposition: one original hole closed, one strictly simpler
localization/basis-sheaf-condition hole added, net zero. The algebraic gluing
argument remains; the categorical extension and canonical-unit comparison
are now proved. There are no other sorries or new definitions in the delivery.

Explicit scratch `#print axioms` checks show only `propext`, `Classical.choice`
and `Quot.sound` for the categorical helper. The item and remaining obligation
add only `sorryAx`, from the named basis-sheaf theorem. No prohibited declarations
or data chosen from an unproved existence theorem occur.

## No longer needed

Removed the first worker's proposed proof-only import
`Sheaf.AlgebraicGeometry.AffineLocalizationSheafification`. It cannot be used
because that module now imports and applies the present item. No repository
import is removed and no module is claimed globally pruned.

All old direct proof dependencies are replaced by the new affine-basis node:
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-sheaf-on-basis-extends`, and `def-weil-pbc-sheafification`.
The tilde-sections node remains a dependency of the remaining algebraic
obligation; the basis-extension step is now carried out with proved Mathlib
tools. Sheafification remains a statement dependency and its Mathlib module
remains publicly imported.

## Where the brief, the DAG or earlier work was wrong

The first worker's duplicate-theorem application compiled against stale compiled
artifacts. The repository now has
`affineLocalization_sheafification_unit_isIso` proved by applying this item, and
its module imports this item. The import-direction check returned NO and the
first delivery dry run rejected the two-module import cycle. That proposed
proof and its DAG dependency have been removed, rather than exploiting the
compiled artifact's old sorry.

Searches repeated with different phrasing using LeanFinder, Loogle and grep.
LeanSearch was attempted and returned a service-unavailable error; that is
recorded without an absence claim.
LeanFinder returned ring-localization/affine-site interfaces; Loogle returned
Away and local algebra detection tools; grep returned Mathlib's comparison
lemma and ordinary isIso_toSheafify. Read `ModuleSheafificationAffineRestriction`:
it requires an already supplied affine-basis identification with a sheaf and
cannot supply the algebraic part here. Read Mathlib's `tilde.toOpen`,
`tilde.toOpen_res`, its Away localization instance, the cover-dense restriction
Hom equivalence and induced-topology sheaf equivalence. No existing theorem
for the remaining module-presheaf affine-basis sheaf condition was found.

Sources checked directly: [01HV](https://stacks.math.columbia.edu/tag/01HV)
provides associated-module principal sections and compatible restrictions;
[009N](https://stacks.math.columbia.edu/tag/009N) and
[009Q](https://stacks.math.columbia.edu/tag/009Q) provide extension from a basis.
The unit `sk-thm-picard-coherence` has empty realized statement/step lists; this
reduction retains the original principal-localization and basis-extension route.

## New nodes

`lem-pc-affine-localizing-presheaf-basis-sheaf` records the strictly smaller
algebraic/sheaf-condition portion of the original proof. It concerns gluing on
the affine site, with no sheafification or canonical unit in its statement.
Its module, verbatim signature, source, complete proof plan, searches, creation
record, blueprint origin, chapter and unit are recorded. No change record is
needed because no existing public statement or definition changes.

## Second reading by T3

1. Compared the delivered item to the repository and checked declarations with
   the project's signature parser: no existing signature changes. The only
   existing public declaration retains its exact statement, visibility and
   docstring. No repository module or statement belonging to another item is
   adapted. Verdict: pass.
2. Compiled both delivered modules in import order through `lcompile.py`.
   Reviewed the categorical proof and explicitly printed its axioms and those
   of the item and new obligation in a scratch copy. The helper uses only the
   allowed axioms; the item has exactly the named remaining basis obligation
   through `sorryAx`. No axiom, unsafe, opaque, implemented_by, extern, hollow
   definition or hidden sorry exists. Verdict: pass as a decomposition.
3. Checked the new obligation against its principal-open gluing proof and the
   sources, and searched LeanFinder, Loogle, repository sources and Mathlib.
   It does not restate the canonical-unit assertion. On the empty affine open,
   the a=0 localization hypothesis makes P(empty) zero, so the empty cover
   glues uniquely. The zero ring, zero element and nonseparated ambient scheme
   cause no exception: all intersections are refined inside an affine open.
   No stronger finiteness or separation assumption was introduced. Verdict:
   true, needed, strictly a part of the argument; left open.
4. Checked the route from the top downward, imports, all three old direct
   proof dependencies, and the unit record. The generic categorical bridge
   uses existing Mathlib constructions; the localization step is retained.
   Proof-only imports stay private. All old direct dependencies and absence
   of global pruning are reported above. Verdict: pass.
5. Read both DAG nodes against their Lean declarations. The item's proof and
   dependency now describe the basis-condition reduction; the new node's
   fields describe exactly the remaining hole and its source proof. Its Lean
   statement is copied verbatim. No unchanged metadata or target meaning is
   altered. Verdict: pass.

Second reading changed the circular duplicate application to the independently
proved categorical comparison, added one named affine-basis obligation with its
module and node, updated the item's proof metadata, and rewrote the report to
count the result honestly as a decomposition.

Final delivery dry run: OK; both modules compile and the preflight passes.
The delivery is CODEX because it adds the remaining obligation and its node.
