## What changed

Proved `AlgebraicGeometry.Scheme.exists_small_finiteSubsum_diagram` in
`Sheaf.AlgebraicGeometry.QcqsCohomologySmallSubsumDiagram`, with its signature unchanged.
The fully proved private helper `small_coproduct_support` injects nonzero indices into
endomorphisms of the given coproduct. This follows the already proved private helper
`coproduct_small_support` in `Sheaf.CategoryTheory.CompactTestsRightAdjointCoproducts`;
its module is not imported, since that helper is private.

The proof removes zero summands by the coproduct universal property, shrinks the
remaining indices, and uses Mathlib's finite-subcoproduct colimit construction.
Finite-set image equivalences and genuine biproduct isomorphisms give the finite-stage
component equations. Added proof imports for the filtered construction and module-sheaf colimits. Updated the
existing node's proof route; added the module docstring and updated the theorem's
proof description. No definitions or existing statement signatures changed. The public-import change
is recorded in `coord/changes/small-finite-subsum-proof-imports.md`; the sole direct
importer independently imports the enough-injectives module through module cohomology,
so no adaptation is required.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_small_finiteSubsum_diagram`
(node `lem-weil-pbc-module-coproduct-small-subsum-diagram`).
No holes remain in the delivered module, and no holes were added or split off.
The private helper `AlgebraicGeometry.Scheme.small_coproduct_support` is fully proved.
This is a proof, not a decomposition into new sorried dependencies.

The compiler checks the original arbitrary indexing universe, the small diagram
universe, all colimit data, and the original component equations. Empty support and
empty finite stages are retained; restricting a completely zero family still gives
the original coproduct by uniqueness of maps from zero objects.

## No longer needed

Removed the import `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`.
Its enough-injectives theorem and node
`lem-sc-ringed-space-module-sheaves-enough-injectives` are not used by this proof.
The statement only needs `moduleRings`, obtained directly through the public import
`Sheaf.Paper.DerivedHomMayerVietoris`; the abelian instance needed by finite biproducts
is already available through that public import.
This prunes the item's import edge, without claiming this module is unreachable from
other targets. The original four DAG proof dependencies remain used; none is pruned.
No other original import was removed.

## Where the brief, the DAG or earlier work was wrong

The section-by-section smallness argument in the original docstring is unnecessary:
local smallness of the module-sheaf category gives a direct injection into End(S).
The DAG's finite-subsum dependency already points to the usable Mathlib theorem
`CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone`.
The item is not a node realizing a unit statement or step in `sk-thm-p1`, and the
unit's route is unchanged. No statement dispute or forced adaptation was needed.
The referenced Stacks source files are not present in this machine's literature
folder; the formal proof uses the recorded Mathlib construction and the proved
library small-support argument, without introducing any unproved source claim.

## Second reading by P3

1. Compared the delivered Lean file with the repository version and mechanically
   checked the existing theorem signature byte for byte: identical. The only new
   declaration is a fully proved private helper; no definition changed. The public
   import replacement is declared in the supplied change record. Checked the sole
   direct importer and its independent public cohomology import: no adaptation is
   required. Verdict: pass.
2. Independently compiled the delivered file. Printed axioms of both the private
   helper and the public theorem in a scratch copy: exactly `propext`,
   `Classical.choice`, `Quot.sound`, with no `sorryAx`. No sorry, axiom, unsafe,
   opaque, implemented_by, extern, or hollow definition occurs. Checked the
   projection/inclusion injection, removal of zero summands, equivalence transport,
   finite-stage reindexing, and final component equation. Verdict: pass.
3. No statement was split off and no hole was added. The private helper repeats
   the existing private support argument because that declaration is inaccessible.
   Independently searched Mathlib and both library roots for small coproduct support
   and nonzero-support results; no public replacement or shorter complete theorem
   was found. Empty index types, all-zero families, and empty finite stages are
   covered; every object is constructed from actual coproduct universal properties
   or explicit equivalences, with no arbitrary witness from an unproved theorem.
   Verdict: pass.
4. The proof uses Mathlib's finite-subcoproduct construction after the necessary
   universe reduction. All four old proof dependencies remain used, so none is
   missing from the pruning report. Checked `dag/units/sk-thm-p1.json`: this node
   realizes no unit statement or step, and the unit route is unchanged. Independent
   removal checks found two redundant newly added proof imports: removed
   `Mathlib.CategoryTheory.EssentiallySmall` and
   `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`. The combined
   removal compiles and passes the same axiom check. The module-sheaf Colimits
   import is necessary once the upstream import is removed: removing it too fails
   to synthesize colimits of the finite-subset shape. Verdict: pass after pruning.
5. Compared node JSON with the repository: changes are confined to `proof`,
   `proof_deps`, and `proof_origin`. These describe the actual support injection,
   shrinking, Mathlib colimit, and biproduct reindexing proof. No new nodes or
   statement changes are needed. Verdict: pass.

Second reading changed only the two redundant proof imports and the corresponding
report and import change record. The mathematical proof was retained. One original
hole is closed, zero holes are added, and zero statements are split off.
