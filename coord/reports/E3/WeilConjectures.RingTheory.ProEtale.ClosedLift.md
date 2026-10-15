## What changed

Proved both holes in `lean/WeilConjectures/RingTheory/ProEtale/ClosedLift.lean`.
All existing signatures, instances, visibility, definitions and public imports are unchanged.
The two new imports are proof-only: `Sheaf.RingTheory.EtaleAlgebraLift` and
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`. They supply the coefficient-lift
theorem and relative ind-etale cancellation. The second reading removed the redundant added
imports `Mathlib.RingTheory.TensorProduct.Quotient` and
`Mathlib.RingTheory.Localization.Away.Basic`; their APIs are already available transitively.

Filteredness uses finite polynomial presentations, tensor-product successors, and the quotient
by the image of the diagonal ideal to equalize parallel arrows. The diagonal ideal is finitely
generated and idempotent; its image has the same properties, making the quotient etale.

Reduction surjectivity lifts representatives from etale stages using the existing coefficient-lift
theorem. Base change and relative ind-etaleness make the reduction flat. The pure-kernel element
equation and a complete local proof that units lift force its kernel to vanish.

Updated the two existing DAG nodes' proof, proof_deps and proof_origin to match the Lean proof.
No new modules, nodes, statements with holes, semantic interface changes, or forced adaptations.
The instance-body/notation change record is `coord/changes/closed-lift-filtered-proof.md`;
the static scanner treats proposition-valued instance proofs as interface changes.
The unit record has empty realized statement/step lists; its route is unchanged.

## Proved and sorry left

Closed `Algebra.ClosedLift.isFiltered_index`
(node `lem-exc-closed-lift-filtered`) and `Algebra.ClosedLift.bijective_reduction`
(node `lem-exc-closed-lift-reduction`): 2 original holes closed, 0 holes added,
0 split-offs, and no sorry left anywhere in this delivery.

All five new private helpers are proved: `exists_index`, `toAlgHom_ι`, `exists_rep`,
`isUnit_of_isUnit_image`, and `surjective_toAlgHom` (inside `Algebra.ClosedLift`).
The reduction proof uses the existing coefficient-lift theorem; the final compiled proof
has no transitive sorry dependency either. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound` for each of the two original declarations.

Validation: the whole delivered module compiles cleanly through lcompile.py (approximately
8–12 seconds); the axiom probe also passes. The second reader's complete delivery dry run passes compilation and preflight.
The proofs use arbitrary rings and ideals: no nonzero-ring, nilpotence, finite-type
condition on C, or extra choice data is introduced into any public definition.

## No longer needed

No original imports were removed. The second reading removed two redundant proof-only import
additions: `Mathlib.RingTheory.TensorProduct.Quotient` and
`Mathlib.RingTheory.Localization.Away.Basic`. No entire module is asserted globally unreachable.

For the filteredness proof, the separate geometric fibre-product and finite-limit machinery
of `lem-weil-pbc-fibre-product-affine-spectra` and
`lem-weil-pbc-etale-base-change-finite-limits` is no longer needed. Those two proof-dependency
edges are pruned. Their modules are not imported for this argument. Ring base change and the
Mathlib diagonal-ideal/cotangent API replace them. Etale composition remains used.

For the reduction proof, `Sheaf.RingTheory.ProEtale.ClosedLiftUnits`
(node `lem-exc-closed-lift-units`) is not imported: its entire required localization argument
is proved locally, so this dependency edge is pruned and its direct prerequisites are recorded.
The independent module may still be needed by other consumers; it is not withdrawn here.
The bundled `Sheaf.RingTheory.IndEtaleStability` and
`Sheaf.RingTheory.IndPrincipalZariski` modules need not be imported for the reduction:
the existing source-library base-change, cancellation, and weak-etaleness API provides exactly
the needed stability clauses. The mathematical stability node remains a dependency.
Likewise, `Sheaf.RingTheory.ProEtale.ClosedLiftMap` is not imported; the construction and cocone
maps needed here already belong to the item itself, and its postcomposition API is unused.

## Where the brief, the DAG or earlier work was wrong

The mathematical statements are unchanged and no false statement was found.
Several dependency attachments cannot be imported literally into this module:
`ClosedLiftUnits` and `ClosedLiftMap` already import it, so importing them here would create
cycles. The required unit statement is proved privately in this module from its original
localization argument; postcomposition maps are unnecessary. The DAG's geometric pullback
argument for filteredness is correct but its ring calculation is shorter in the available API.

The existing coefficient-lift theorem returns a ring isomorphism with a specified reduction
formula, not an algebra isomorphism. The proof verifies coefficient compatibility explicitly
before composing with each etale stage. No statement adaptation was needed.

## Second reading by E3

1. **Existing interfaces: PASS.** Read the complete repository and delivered modules and their
   unified diff. Every existing declaration header, section variable, instance name, visibility,
   public import and data-valued definition is unchanged. Only the two original proof bodies,
   five new proved private helpers, proof-only imports and tensor notation were added. The
   change record accurately explains the scanner's treatment of the proposition-valued instance;
   the `IsFiltered (Index A C)` signature is literally unchanged. No targets change meaning and
   no other module is delivered or adapted.

2. **Proof and trust: PASS.** Independently compiled the original delivery through `lcompile.py`
   with no errors or warnings. A scratch copy with `#print axioms` for `isFiltered_index`,
   `bijective_reduction`, `indEtale`, `toAlgHom` and `reduction` reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, with no transitive `sorryAx`. The delivery contains no
   `sorry` or prohibited axiom/implementation command. All choices in `exists_index` and
   `surjective_toAlgHom` are local witnesses inside proved propositions: the colimit and its
   structure maps remain the original constructions, and no arbitrary data is selected from an
   unproved existence claim. Recompiled successfully after the import repair below.

3. **Split-offs and mathematics: PASS; none split off.** Read all five private helpers and both
   original proofs. The small-model presentation retains the specified map to C. Tensor
   successors are etale by base change and composition. For parallel arrows the diagonal ideal
   K is finitely generated and idempotent; these properties pass to its image J. The quotient
   Y/J is etale, its map to C descends because the two composites agree, and the explicit tensor
   differences show that it equalizes the arrows. The reduction proof explicitly checks the
   coefficient lift's A-linearity, rather than treating its ring isomorphism as an algebra
   isomorphism without justification. Relative ind-etaleness gives flatness of the surjection;
   the pure-kernel equation x=x*e and the proved localization unit argument force x=0.
   Checked the edge cases A or C zero, I=top, I=bot, and localization at zero: none needs a
   nontriviality or nilpotence assumption. In particular when I=top the quotient algebra C is
   zero, and localization at zero is allowed when its target is zero.

4. **Route, searches and pruning: PASS after import repair.** Read the source argument in
   [Stacks 097P](https://stacks.math.columbia.edu/tag/097P) and the coefficient construction in
   [Stacks 04D1](https://stacks.math.columbia.edu/tag/04D1). The proof retains their tensor,
   quotient, coefficient-lift, flatness and localization route. Inspected the source checkout's
   ClosedLift module (both original holes remain), the current ClosedLiftUnits module (imports
   ClosedLift, so cannot be imported back here), and the existing coefficient-lift/cancellation
   APIs. Independent LeanFinder search for common successors and parallel-arrow equalizers
   returned etale composition and related general facts, no ready-made filteredness theorem;
   Mathlib grep for filtered etale categories/coequalizers found no match. Local searches in
   lean/Sheaf and lean/WeilConjectures found no shorter applicable closed proof. The unit
   `sk-prop-sf-open-closed-triangle` has empty realized statement and step lists, and its route
   is untouched. Compared old/new proof_deps: precisely the two geometric filteredness edges
   and the ClosedLiftUnits edge were removed, all listed under No longer needed. No globally
   unreachable module is claimed. Each remaining added import provides a needed named theorem.

5. **DAG records: PASS.** Opened both complete node JSON files and every cited dependency's
   statement/Lean or Mathlib attachment. The only changed fields are proof, proof_deps and
   proof_origin. For each node, proof_deps is exactly the union of the steps' uses. The
   filteredness steps describe the actual K/J construction; the reduction steps describe the
   coefficient-lift map, tensor quotient identification, relative flatness, pure kernel and
   private unit proof in the file. The direct cotangent, finite-generation and formally-etale
   quotient calculations are the displayed short Mathlib applications, not unproved split-offs.
   No new node is required for a remaining hole, and no historical statement or unit field was
   changed.

**Changes by the second reader.** Removed the redundant proof-only imports
`Mathlib.RingTheory.TensorProduct.Quotient` and
`Mathlib.RingTheory.Localization.Away.Basic`: each omission compiled independently, and then
both omissions compiled together. Corrected the report's import inventory and pruning account.
The proof terms, signatures, definitions, node records and change record required no repair.
Two original holes closed, zero holes added, zero split-offs; this is a proof, not a decomposition.
