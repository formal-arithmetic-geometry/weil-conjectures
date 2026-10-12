## What changed

Split the construction into two helper modules and combined them in the target module. The target theorem is decomposed by combining two admitted helper conclusions: one hole closed and two holes added; this is a decomposition, not a completed proof.

## Proved and sorry left

`CategoryTheory.Functor.cartanEilenberg_cone_filtration` has its original hole closed by decomposition, using two admitted strict intermediate results; this is not a completed proof. One hole is closed and two are added (net minus one). The helper declarations `cartanEilenberg_cone_filtration_data` and `cartanEilenberg_cone_filtration_properties` remain `sorry`, with nodes `lem-sp-cartan-eilenberg-cone-filtration-data` and `lem-sp-cartan-eilenberg-cone-filtration-properties`.

## No longer needed

Removed the unused imports Mathlib.Algebra.Homology.HomotopyCategory.Acyclic, Sheaf.CategoryTheory.DoubleComplexTotal, Sheaf.CategoryTheory.Filtration, and WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic from all three modules. The item now uses the two helper nodes directly. All five original direct proof dependencies are no longer direct dependencies of the parent node: `def-sp-cartan-eilenberg-presentation`, `def-sp-double-complex-total`, `def-sp-filtered-complex-subquotients`, `def-sp-filtration`, and `lem-pur-quasi-iso-cone-acyclic`. They remain required by the helper statements or their proof plans; no whole module is claimed to leave the targets’ import closure. The public Acyclic import is replaced by the narrower public MappingCone import under the change record.

## Where the brief, the DAG or earlier work was wrong

The original proof plan compresses substantial subobject and graded-complex constructions into one step; these are exposed as two strictly smaller sourced statements.

## New nodes

`lem-sp-cartan-eilenberg-cone-filtration-data` states existence of the filtration with its prescribed image-sum formula; its proof is the original steps 1 and 2.

`lem-sp-cartan-eilenberg-cone-filtration-properties` assumes any filtration with that formula and states its finite bounds and graded homology calculation; its proof is the original steps 3 and 4.

Change record: `coord/changes/cartan-eilenberg-cone-filtration-imports.md`.

## Earlier second reading (a previous round; superseded)

Repair verification of the existing second reading; the independent second reader
must check these revised files before delivery.

1. **B2: helper statements.** The data node now contains the original mathematical
statement from “Let” through the finite-supremum/empty-sum sentence. The properties
node contains the complete original statement, with an arbitrary filtration and
its degreewise formula as hypotheses. These agree with the two Lean signatures:
existence and formula for data; bounds and graded homology for properties.

2. **B: proof records.** Removed the copied A2 `reviewed` and `reviewed_proof`
objects from both new nodes. Data has original proof steps 1 and 2; properties
has original steps 3 and 4. Each `proof_deps` is the union of its steps' `uses`.

3. **C: parent DAG.** The delivered parent node now has one elementary combination
step using exactly the two helper nodes, matching the Lean `obtain`/`exact` proof.
Its `proof_origin` identifies the Q2 decomposition. The original statement,
signature, source, chapter and unit are unchanged; no unit route is bypassed.

4. **H9 and A: imports and users.** All four unused imports were removed from
all three modules. The target's two helper imports are plain proof-only imports.
MappingCone remains public for the signatures. The change record includes the
actual importer, `Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso`
(unclaimed), whose original source requires no adaptation.

5. **F: progress and pruning.** This is one upper hole decomposed into two named
helper holes, not a completed proof. The item directly uses the two helper nodes;
the helpers retain the original four-step argument and its dependencies. Removal
of explicit imports does not claim that those modules leave the entire target
closure: they can remain transitively required elsewhere.

Verification after repair: `lcompile.py --all` compiled all three delivered
modules cleanly. A temporary unchanged copy of
`Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso` compiled against the
sandbox overlay (exit code 0), then was removed from the delivery. Node field,
proof-dependency union, review-record removal and Lean line-width checks passed.
The independent second reader must rerun the delivery dry run before pushing.


## Second reading by Q2

1. **Unchanged interface — pass.** Read the full diff against the repository.
   The existing theorem signature is byte for byte identical; only its proof and
   imports change. No definition is added or altered. The public import change
   is covered by `coord/changes/cartan-eilenberg-cone-filtration-imports.md`.
   Its only source importer is `CartanEilenbergAugmentationQuasiIso`; its unchanged
   source compiles against the delivered overlay without adaptation.

2. **Proof and axioms — pass as a decomposition.** Compiled all three modules
   in import order with `lcompile.py --all`, without warnings or errors.
   Scratch copies with `#print axioms` for each of the three declarations report
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The only delivered holes are the two named helper theorems. There are no
   definitions choosing data from an unproved existence result, forbidden
   declarations, or hidden holes. The parent combines the helpers correctly.

3. **Split statements — pass.** Data asserts only existence and the pinned
   formula; properties assumes any filtration with that formula and asserts
   only bounds and graded homology. Neither restates the whole parent theorem.
   Checked zero bicomplex/complex, empty diagonals, `n < b-1`, `n=b-1`,
   `p < b`, and `p > n+1`. At `n=b-1` only the `K^b` cone summand can survive;
   at lower degrees the cone is zero. For `p < b` the column and successive
   graded quotient are zero. The graded index `n-p` puts `K^p` in column-cone
   degree -1. With the flipped bicomplex, the resolution differential is the
   first total differential (coefficient one); the complex-degree differential
   disappears in the quotient. The docstrings give sourced construction and
   quotient proofs, with matching new nodes. Independent LeanFinder and Loogle
   searches and `rg` found no exact existing result. Read the related
   `firstQuadrant_vertical_cone_filtration` (still admitted, different shape,
   no pinned formula) and `boundedBelow_secondFiltration` (total complex,
   no augmentation cone); neither closes either helper by direct application.

4. **Route and pruning — pass.** The parent is below the unit level. The unit
   `sk-prop-av-pqf-finite` has no realized node naming this item, and its
   realization record is unchanged. The original four construction/calculation
   steps are preserved across the two helpers. Remaining public imports supply
   signature vocabulary; helper imports in the parent are proof-only. Expanded
   the pruning inventory to name every old direct parent proof dependency,
   without claiming whole-closure module pruning. Neither helper can be closed
   in a few minutes by the available results.

5. **Nodes — pass.** Checked all three node files against their Lean signatures
   and docstrings. Every `proof_deps` is precisely the union of step `uses`.
   The parent records the actual two-helper combination and its agent origin;
   the new nodes preserve the sourced original steps, have separate Lean
   modules, creation/blueprint/chapter/unit/search fields, and no copied review
   certification. The parent's statement, source, chapter and unit are unchanged.

Second reading changed only this report: completed the direct-dependency pruning
inventory and recorded the independent checks. Lean proofs and statements required
no repair. This remains one hole closed and two added (net minus one), not a
sorry-free proof. Scratch axiom/importer copies are removed before delivery.
