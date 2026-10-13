## What changed

The original signature and visibility of
`CategoryTheory.exists_cartanEilenberg_comparison_column_step` are unchanged.
Its complete Lean proof now combines two separate comparison stages. A private,
fully proved `shortExact_cycles_image` helper identifies the outgoing image factor
as a cokernel of the cycle inclusion. Exactness of the mapped row constructs the
outgoing boundary map, without a further existence assumption. The proof derives
its degree-zero augmentation from the object augmentation, and derives incoming
image compatibility by cancelling the mapped image-factor epimorphism.

Added two modules, each with one public statement and one whole-proof `sorry`:
`Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage` and
`Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage`. The first only constructs
an augmented cycle map from the incoming boundary comparison. The second only
constructs an augmented object map from a supplied cycle map. They are distinct
halves of the two alternating horseshoe applications, not renamed copies of the
column theorem. In particular neither asserts its four conclusions or the pair
of maps in its conclusion.

The original module's proof imports now name those two modules. The original
horseshoe and model-category proof imports are retained in the two new modules
as the planned inputs for their remaining proofs. Updated the original DAG node
and added one DAG node for each remaining statement. No existing interface or
other module was changed; no forced adaptations or change records are needed.

## Proved and sorry left

Closed the original one hole:
`CategoryTheory.exists_cartanEilenberg_comparison_column_step`
(node `lem-weil-pbc-ce-comparison-column-step`). Its body contains no `sorry`.
The private `CategoryTheory.shortExact_cycles_image` is also fully proved using
Mathlib's kernel, image and exactness APIs.

Added exactly two holes, with no holes in definitions:

- `CategoryTheory.exists_cartanEilenberg_comparison_cycle_stage`
  (`lem-weil-pbc-ce-comparison-cycle-stage`), in
  `Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage`.
- `CategoryTheory.exists_cartanEilenberg_comparison_object_stage`
  (`lem-weil-pbc-ce-comparison-object-stage`), in
  `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage`.

This is a decomposition, not a proof with all dependencies closed: one upper hole
closed and two strictly smaller holes added. The delivery's text-level net is -1;
the pinned sorry ledger determines the actual closure count. The existing
`CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift_exact_source`
remains an unchanged dependency outside this delivery.

All three modules compiled together in import order with `lcompile.py`, without
warnings. The column module also compiled individually after removing unnecessary
local elaborator options. Its signature was compared with the original by the
same declaration parser used for the stage-3 checks.

## No longer needed

No DAG node or module is claimed pruned. The direct imports
`Mathlib.Algebra.Homology.ModelCategory.Injective` and
`Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource` were removed from
the column module, but remain planned proof dependencies through the new stages.
They are relocated imports, not elimination of their transitive work. Both
original proof-dependency nodes remain used by the new stages. All existing
public imports of the original module remain unchanged.

The outgoing boundary augmentation and boundary square are no longer separate
unfinished steps: the column proof derives both from the constructed object map
and the cokernel property. No new theorem is required for either conclusion.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or changed. The original plan is mathematically usable,
but explicitly lifting a second outgoing boundary map in the column module is
unnecessary once the object map commutes with cycles. The cokernel factor is
unique, and its augmentation follows by evaluation of its factorization equation.
This is a refinement below the unit level; the two alternating comparison stages
and the unit route remain intact (`sk-prop-h2` has no realized node replaced).

The source files cited by the DAG are not present in this read-only local clone.
Read the primary Stacks pages for Tags 015I, 015K and 013P, and downloaded
`derived.tex` into the sandbox scratchpad to check the cited construction. The
new proof texts explicitly expand the functoriality remark using the existing
exact-source horseshoe theorem. No source document was modified.

Searched before splitting: LeanFinder returned eight injective-resolution API hits,
Loogle returned cycle/kernel infrastructure, and searches of Mathlib and both
library roots found no ready-made column comparison. LeanSearch was unavailable
for both new-stage queries (Internal Server Error). Both imported-blueprint
searches returned no matching blueprint node. These searches are recorded in the
new nodes. Checked the edge cases in the statements: arbitrary integer horizontal
degrees remain allowed, nonnegative resolution indexing supplies boundedness,
zero columns give the zero comparison, and no injectivity of F-images is assumed.
The cycle-stage statement has no outgoing-column assumptions; the object-stage
statement has no incoming-boundary or homology data.

## New nodes

`lem-weil-pbc-ce-comparison-cycle-stage` states the boundary/cycles/homology
half of the comparison, with the augmentation written on the actual single-
bicomplex cycles evaluated at degree zero. Its incoming equation is stated after
precomposition with `toCycles`, avoiding any duplicate boundary-inclusion
definition. The node and docstring give the full proof via the existing lifting
and exact-source horseshoe declarations.

`lem-weil-pbc-ce-comparison-object-stage` states only the extension from a
prescribed augmented cycle map to an object map, using the cycle/object/outgoing-
boundary row. Its two conclusions are object augmentation and cycle compatibility.
It does not assert an outgoing map. The original module constructs that map and
proves the rest of the comparison. No change record accompanies either new node,
since no existing public statement or definition is altered.

## Second reading by K2

1. **Interfaces: pass.** Read the diff against the repository column module. The
   existing theorem signature, including every hypothesis, conclusion, transport,
   and visibility, is byte for byte unchanged. All original public imports remain.
   The only added declaration there is a private proved helper. The two additional
   modules are new statements, not modifications of another group's interface.
   No definition or target statement changed, so no change record is required.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all three
   modules in import order with `lcompile.py`, without warnings. Read the entire
   column proof, including exactness reflection across the image inclusion,
   preservation of the short exact row, the cokernel construction, cancellation
   of the incoming image-factor epimorphism, and the degree-zero augmentation
   calculation. A scratch copy with `#print axioms` confirms that the private
   helper uses only `propext`, `Classical.choice`, and `Quot.sound`. Each new stage
   and the column theorem uses only those axioms and `sorryAx`. Exactly the two
   reported public stage theorems retain whole-proof `sorry`; there are no data
   definitions, hidden holes, or forbidden declarations. Existential stage witnesses
   are eliminated inside a theorem proof, not used to define unspecified data.
3. **Split statements: pass.** Read both signatures, docstring proofs and nodes,
   and the existing exact-source horseshoe signature. Each is one alternating
   short exact row: the first constructs only cycles from incoming boundaries;
   the second extends a supplied cycle map only to the object column. Neither
   restates the column comparison. Their hypotheses supply exactly the source
   augmentation quasi-isomorphisms and target termwise injectivity needed for
   the stated lifting argument; injectivity of F-images is never required.
   Nonnegative resolution indexing makes the single-object quasi-isomorphism
   monomorphic, including degree zero, and supplies boundedness. Checked zero
   bicomplexes (all comparison maps zero), zero incoming images (the incoming
   equation is automatic), zero outgoing images (the cokernel equation is zero),
   identity augmentations concentrated in resolution degree zero (the induced
   maps on boundaries, cycles and objects give both statements), and arbitrary
   negative horizontal p (only q=p+1 is used). These cases introduce no extra
   hypothesis. Read the local Stacks derived.tex construction and functoriality
   remark, Tags 015I and 015K. Independently searched with different wording via
   LeanFinder, Loogle and Mathlib grep, and searched both library roots and the
   upstream checkout. Hits concern K-injectivity, complex-shape extensions and
   comparison infrastructure, not either prescribed-map stage. No existing
   statement closes either stage in a few minutes; neither is a duplicate.
4. **Route and pruning: pass.** The proof first derives the outgoing map and both
   boundary equations using proved Mathlib image/kernel/cokernel APIs, leaving
   just the two horseshoe comparison stages. The stage imports in the column
   module and the lifting/horseshoe imports in the new modules are plain imports
   because they serve proofs only. The original two proof-dependency nodes remain
   transitive dependencies of both stages, so they are relocated rather than
   pruned; the report's `No longer needed` section accounts for both. Read
   `dag/units/sk-prop-h2.json`: its realized statement and step lists are empty,
   and no unit realization or unit-level route is replaced. No pruning is claimed.
5. **DAG agreement: pass.** The original node changes only `proof`, `proof_deps`
   and `proof_origin`; its five steps follow the actual Lean argument. Its new
   direct dependencies are the two stage nodes. Both new nodes have their own
   source, full proof steps, dependency union, searches, creation and blueprint
   provenance, chapter/unit, and Lean records matching the new declarations.
   Their mathematical statements express the actual augmentation equations and
   distinguish horizontal from resolution degrees. Both retain the two original
   planned proof dependencies. No declaration or node is silently retired.

Second reading changed only this report by adding the independent checks and
axiom results. No Lean or DAG repair was needed. The result remains a decomposition:
one original hole closed, two stage holes added, with no module claimed pruned.
