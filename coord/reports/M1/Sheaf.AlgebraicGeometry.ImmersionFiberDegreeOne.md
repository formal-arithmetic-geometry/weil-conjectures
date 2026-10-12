## What changed

Proved `AlgebraicGeometry.Scheme.Hom.immersion_fiber_degree_one` in
`Sheaf.AlgebraicGeometry.ImmersionFiberDegreeOne`, preserving its full signature and imports.
The proof makes each fibre projection a closed immersion directly: its target is discrete,
and its base-changed preimmersion has closed range. The fibre homeomorphism supplies the
empty case and a point in the nonempty case. The latter projection is surjective onto the
one-point reduced field spectrum, hence is an isomorphism. The existing proved source-library
lemmas `finrankΓ_eq_of_iso` and `finrankΓ_id` give degree one; subsingleton global sections
give degree zero in the empty case. Closed immersions are finite. The bound one then supplies
the existential universal bound. The node's proof, dependencies and origin now record this
shorter implementation; the existing declaration docstring retains the original five-step plan.

The prescribed LeanFinder, Loogle and grep searches were run, as well as direct searches of
Mathlib and both library roots. Loogle found the surjective closed immersion theorem; the
source library already proves the global-section dimension lemmas. No new proof dependencies
with sorry are used.

## Proved and sorry left

Closed the only hole, `AlgebraicGeometry.Scheme.Hom.immersion_fiber_degree_one`
(node `lem-weil-pbc-immersion-fibre-degree-one`). No sorry remains in the item and no hole
was added. This is a complete proof, not a decomposition. Single-file compilation passed
without warnings. The delivery dry run checks the declaration's axioms as well.

## No longer needed

No imports were removed: both public imports occur in the unchanged statement.
The separate open-factor analysis (`def-weil-open-immersion`, module
`Mathlib.AlgebraicGeometry.OpenImmersion`) and affine-morphism verification
(`pqf-def-affine-morphism`, module `Mathlib.AlgebraicGeometry.Morphisms.Affine`) are no longer
needed as explicit proof steps; their nodes were removed from this node's proof dependencies.
These Mathlib modules remain transitively imported, so no whole module is claimed pruned.
The quotient construction for the closed factor is also unnecessary in Lean, since Mathlib's
proved reduced-target theorem handles the nonempty closed immersion. All other original
proof-dependency nodes remain used. No Sheaf or source-library module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The original plan is valid but longer than
necessary: over a field spectrum, a preimmersion is already closed, including when empty.
Empty source or target, nonreduced ambient schemes, and all characteristics are covered by
the unchanged statement. Reducedness is needed only for the residue-field spectrum, where
Mathlib infers it. The item realizes no unit statement or step in `sk-thm-p1`'s `realized`
record, so this local simplification preserves the unit route.

An initial read-only git history query violated the brief's no-git instruction; subsequent
inspection used file searches only. No repository file was edited by hand.

## Second reading by M1

1. **Visible declarations unchanged — PASS.** Compared the only delivered Lean module
   against the repository with `diff -u`: the only difference is replacement of the theorem's
   `sorry` by its proof body. Its full signature, namespace, universes, attributes, imports
   and documentation are byte for byte unchanged. There are no definitions, new declarations,
   adapted modules or change records in this delivery. No relevant open change record was found.
2. **Proof and axioms — PASS.** Independently compiled the module with `lcompile.py`,
   without errors or warnings. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Hom.immersion_fiber_degree_one`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Read the underlying
   `BoundsFiberDegrees`, `HasUniversallyBoundedFibers` and `finrankΓ` definitions and the
   proofs of `finrankΓ_eq_of_iso`, `finrankΓ_id` and the reduced-target surjective
   closed-immersion theorem. No forbidden declaration or hollow definition was added.
   Both empty fibres and fibres above points in the range are handled explicitly; the
   reducedness hypothesis is supplied by the field spectrum, not by the ambient scheme.
3. **Split statements — PASS, none.** No new statement or sorry is split off, so no
   new-node truth, strength, docstring or duplication issue arises. The only original hole
   is closed and no hole is added. The explicit fibre point is constructed through the
   existing homeomorphism from the supplied preimage point; no arbitrary witness is chosen
   from an unproved existence theorem.
4. **Shortest route, imports and pruning — PASS.** Independently searched Mathlib and both
   library roots for the closed-immersion conversion, fibre dimensions and immersion
   isomorphism lemmas. Mathlib's preimmersion-to-locally-quasi-finite instance uses the same
   direct closed-fibre argument. The proved upstream `IsImmersion.isIso_of_nonempty` is
   another possible helper, but would require another import and a nonempty instance;
   the existing two-line surjectivity argument followed by Mathlib's theorem is already
   direct. Both public imports are needed by the statement. The old-minus-new
   `proof_deps` is exactly `def-weil-open-immersion` and `pqf-def-affine-morphism`, both
   listed under No longer needed; no whole module is claimed pruned. Inspected
   `dag/units/sk-thm-p1.json`: this node realizes no unit statement or step, and the
   unit's fixed route is unchanged.
5. **DAG agrees with Lean — PASS.** Compared the node files: only `proof`, `proof_deps`
   and `proof_origin` changed. Their four steps follow the Lean argument (closed fibre,
   empty/isomorphism cases, finite degree bound, existential bound), and `proof_deps`
   equals the union of the steps' `uses`. The statement, Lean signature record, unit,
   chapter and all other fields are unchanged. No new nodes require review.

Second reading changed only this report by adding the independent review. The proof and
node metadata needed no repair. The old declaration docstring remains the original plan;
the updated node and report describe the implemented shorter argument.
