## What changed

Completed `AlgebraicGeometry.Scheme.product_residue_h1_injective` with its original
signature. The proof obtains bijective scalar maps on the residue fibres by evaluating
the structure-sheaf adjunction unit at the top open, base changes the sections to
rational points, and applies `picard_h1_product_injective`. A fully constructed
pullback-pasting isomorphism identifies the two products and their slices. Explicit
cohomology composition and identity equalities transport injectivity back.

Added proof-only imports of
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf` and
`Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackFunctorial`.
All existing public imports and declarations retain their original interfaces.

Repair of the landing-tool return at head `773993a6e`: replaced the duplicate
private `appTop_isIso_of_tensor_unit` with the genuinely more general private
`app_isIso_of_tensor_unit`, whose explicit binder `(U : B.Opens)` gives the
isomorphism of the structure-sheaf ring map on any open `U`. Both scalar-map
arguments specialize it to `⊤`. The theorem in
`Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization` is private
and therefore cannot be used by importing that module. This repair uses the
return's generalization option and adds no import of that unrelated proof.
Updated the existing node's proof route to record these two dependencies.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Scheme.product_residue_h1_injective`
(node `lem-sc-product-residue-h1-injective`). No holes added or split off;
no `sorry` remains in the delivered module. The private helper `app_isIso_of_tensor_unit` for sections over arbitrary opens, pullback pasting,
and cohomology transport are proved. This proof uses the existing field-product and
functoriality results; it does not claim to eliminate their transitive dependencies.

## No longer needed

The duplicate top-open helper `appTop_isIso_of_tensor_unit` is removed and
replaced by its arbitrary-open generalization. No import is removed. Every original import and every original proof-dependency node is still used.
The unit route is preserved, and no modules are asserted to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's route is correct but omitted two explicit proof dependencies:
`lem-weil-pbc-module-pullback-structure-sheaf` for the top-open scalar comparison,
and `lem-sc-structure-sheaf-cohomology-pullback-functorial` for transport.
Both are existing nodes, now recorded in the delivered node copy.
The earlier sandbox attempt stopped before cohomology transport; its saved draft
provided the pullback construction. Broad rewriting of cohomology composition in
that draft was expensive, so the completed proof uses explicitly typed equalities.
The pullback-pasting helper is generalized to a category with pullbacks, avoiding
repeated unfolding of scheme structures. This keeps compilation below the file limit.
The cited Stacks proofs were checked at
[Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3) and
[Tag 0BED](https://stacks.math.columbia.edu/tag/0BED).


The returned delivery duplicated a private top-open theorem already present in
`PicardLocusClosedValuativeFactorization`. The repair generalizes its conclusion
to every open, with explicit scheme and open binders; the public target signature
is unchanged. The prior second-reading record was removed because it predates
this repair; the dispatcher will obtain a fresh independent reading.

## Second reading by G1

1. Compared the delivered module with the repository version. The target theorem
   signature and all existing declaration interfaces are unchanged; only proof
   code, proof-only imports, authorship, and the recorded DAG route differ.
2. Compiled the module with `lcompile.py`; it succeeds with no diagnostics. The
   delivered module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The target's remaining `sorryAx` dependency comes only from
   imported open statements.
3. Checked the new private helpers and the existing node. The pullback isomorphism
   and cohomology transport are genuine intermediate reductions, while the target
   statement remains unchanged and no new split-off statement was added.
4. Read the proof from the target downward. It uses the field-product injectivity,
   structure-sheaf pullback comparison, and cohomology functoriality dependencies;
   the explicit pullback pasting preserves the unit's route. Both added imports are
   proof-only and are used.
5. Compared the node's proof, dependencies, and origin with the Lean proof. The
   two omitted dependencies are now recorded, and the node still points to the
   same unit and source statement.

Changed only the report and the already described generalization of the private
top-open helper; no target statement or definition was changed.
