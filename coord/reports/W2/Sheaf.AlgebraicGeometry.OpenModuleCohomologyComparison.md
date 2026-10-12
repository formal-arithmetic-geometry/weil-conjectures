## What changed

Filled the sole proof of
`AlgebraicGeometry.nonempty_openModuleCohomology_addEquiv_restrict_H` in
`Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison`, preserving its statement,
public imports, and definitions. The proof constructs the restricted injective
resolution and the natural section-complex isomorphism, commutes the exact
forgetful functor with homology, applies the existing module-to-abelian comparison,
and constructs the terminal-open Ext identification.

Added proof-only imports of
`Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`,
`Mathlib.CategoryTheory.Preadditive.Injective.Preserves`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`.
Updated the existing node's proof and dependencies to record the actual Lean route.
The unit's realized statement/steps are empty; its proper-quasi-finite route is
unchanged. The source arguments were checked against Stacks Tags 01E1 and 03FD.
Local compilation passed without warnings in 29 seconds, within the file limit.

## Proved and sorry left

Closed: `AlgebraicGeometry.nonempty_openModuleCohomology_addEquiv_restrict_H`
(node `lem-pqf-open-module-cohomology-comparison`): 1 of 1 original holes.
No `sorry` remains in the item's module. No holes or declarations were added,
and nothing was split off. This is a proof from existing dependencies, not a
new decomposition.

The proof intentionally uses the existing unproved
`AlgebraicGeometry.module_cohomology_iso_underlying_abelian`
(node `lem-sc-module-abelian-zariski-cohomology`), as required by stage 3.
This delivery does not claim to close its transitive holes.
The constructions work uniformly at degree zero and for the empty open.

## No longer needed

Removed the redundant proof-only import
`Sheaf.Topology.RingedSpaceModuleCohomology`: it is already publicly imported
by `Sheaf.Topology.OpenModuleCohomology`. Its definitions and node remain needed.

A trial import of `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`
was omitted from the final delivery: restriction additivity is proved locally
by reflexivity instead of loading that module just for its instance.

No planned dependency node or module is pruned from the transitive closure.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan needs the finite-limit and
finite-colimit assertions of `open_restriction_adjunction_exact` explicitly to
build the transported resolution; the original proof dependency list omitted
that direct use. It has now been recorded, together with the enough-injectives
lemma used to select the starting resolution. The terminal-open identification
is not yet provided by Mathlib's sheaf cohomology API (its module lists it as a
TODO); the concrete singleton free-abelian argument already used in the source
library supplies it here. No new intermediate theorem is needed.

## Second reading by W2

1. Interface: PASS. Compared the sole delivered Lean module with the repository
   using a full diff and a byte comparison of the unchanged declaration/docstring
   region. The existing signature, namespace, docstring and public imports are
   unchanged. Only its proof and proof-only imports differ; no change record is
   required. There are no new definitions or declarations.
2. Proof: PASS. Independently compiled with lcompile.py: no errors or warnings,
   30 seconds. A scratch copy with `#print axioms
   AlgebraicGeometry.nonempty_openModuleCohomology_addEquiv_restrict_H` compiled in
   31 seconds and reported exactly propext, Classical.choice, Quot.sound and
   sorryAx. The last is inherited from existing open dependencies, including
   module_cohomology_iso_underlying_abelian; the item itself has no sorry and no
   forbidden declaration or attribute. I is Mathlib's injective resolution, and
   J is constructed termwise with its explicit augmentation; no arbitrary data
   is selected from an unproved existence theorem.
3. Split statements: PASS (none). No holes, nodes or statements were added.
   Checked the argument at p = 0, U = bottom and U = top: no positivity,
   nonemptiness, affineness or quasi-coherence premise is used. For the empty
   scheme the terminal-open representable still has exactly one morphism from
   every open, so its free-abelian/constant-integer identification remains valid.
4. Route and pruning: PASS. Read the restriction-resolution, exact restriction,
   enough-injectives and module/abelian comparison declarations. Checked the
   section naturality equation, exact forgetful homology isomorphism, and the
   orientation of Ext.precompAddEquiv. Searched the library by restricted
   cohomology and terminal-open/free-representable terminology and searched
   Mathlib through msearch.py. Mathlib explicitly lists the terminal-open
   comparison as TODO; upstream EulerChar supplies the same singleton argument,
   rather than an available reusable comparison declaration. No shorter proved
   replacement was found. The removed RingedSpaceModuleCohomology import is
   redundant via the unchanged public OpenModuleCohomology import. All old
   proof_deps remain used, and No longer needed lists the only import removal;
   no module is pruned from the closure. Read sk-prop-av-pqf-finite.json: its
   realized.statement is empty and realized.steps is [[]]; its route is preserved.
5. DAG: PASS. The sole delivered node differs only in proof, proof_deps and
   proof_origin. Its three steps match the constructed restricted resolution,
   section-complex/homology comparison and terminal-open Ext identification.
   The two added dependency ids record actual direct uses; no existing
   dependency has silently disappeared. The Lean statement record is unchanged.

Second reading changed only this report by adding the independent checks above.
No repair to the Lean proof or DAG was necessary. One original hole is closed,
zero holes are added, and zero statements are split off; the transitive open
comparison is explicitly accounted for in Proved and sorry left.
