## What changed

`lean/Sheaf/AlgebraicGeometry/FiniteRelationDescent.lean`: replaced the sole sorry in
`AlgebraicGeometry.finiteRelation_module_map_descent` by a complete reduction. For each relation,
subtract the two maps, use additivity of tensor pullback to get a zero map at the limit, apply
single-map eventual vanishing, and use additivity again to recover equality at its stage.
`Finset.exists_le` produces one upper bound for all chosen stages and the initial stage.
Naturality of the tensor-pullback composition isomorphism and cancellation prove persistence
at the common stage. The transition equation is proved using `Spec.map_comp` and `R.map_comp`.
All original public signatures and visibility are unchanged.

Two proved private helpers establish module-base-change additivity from the proved tensor
adjunction, and persistence of equality under composite base change from the proved tensor
composition isomorphism. These do not add any holes. Added proof-only imports of
`Mathlib.CategoryTheory.Adjunction.Additive`, `Mathlib.Data.Finset.Order`, and the new single-map
vanishing module. The public imports are unchanged.

`lean/Sheaf/AlgebraicGeometry/FinitePresentationZeroMapDescent.lean` states the remaining
single-map finite-generator/finite-presentation vanishing argument. It only requires a
quasi-compact structural morphism, a finite type quasi-coherent source, and a finitely presented
quasi-coherent target. No Noetherianity, finite presentation of the structural morphism, or
quasi-separatedness assumption is needed. Its docstring contains the complete finite-affine,
finite-matrix, filtered-colimit argument and source. It introduces no definitions or chosen data.

Updated the item's node proof and proof dependencies, and added the matching new node.
Sources read: [Stacks Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR), clause (3) and its
first proof; [Stacks Tag 05N7](https://stacks.math.columbia.edu/tag/05N7), clause (3).

## Proved and sorry left

Closed: `AlgebraicGeometry.finiteRelation_module_map_descent`
(node `lem-pc-fp-relation-descent`). Its body contains no sorry.

Added and left: `AlgebraicGeometry.finitePresentation_zero_map_descent`
(node `lem-pc-fp-zero-map-descent`), in the new module
`Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent`; its entire proof is `:= by sorry`.

Thus 1 original hole closed, 1 lower hole added: this is a decomposition, not a net proof or an
axiom-free closure of the item. The remaining theorem concerns one map; the finite-family
synchronization, conversion between equality and vanishing, and subsequent-stage persistence
are proved in Lean. Both modules compile together through lcompile.py with no warnings.

Checked edge cases: `n = 0` selects an upper bound of the singleton containing `j`, with a
vacuous family conclusion; `M` empty is permitted whenever `src` and `tgt` can exist.
The new theorem allows zero source/target modules and empty `Xi`; it is then immediate.
For a singleton index diagram, the limit projection is an isomorphism and reflects zero.
The matrix argument also allows zero generators or zero relations and zero coefficient rings.
A preorder rather than a partial order causes no problem: a thin category has unique parallel
arrows, and all transition proof arguments are proof-irrelevant.

## No longer needed

Removed proof import: `Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent`.
Its declaration `AlgebraicGeometry.finitePresentation_module_map_descent` and node
`lem-pc-fp-module-map-descent` are not needed by this proof: the item already supplies the
fixed models and both sides of each relation. This also removes the route through its proof
import `Sheaf.Algebra.FinitePresentationColimit` / `lem-pc-fp-module-map-descent-affine` for
this item; neither its object nor its map lifting clauses are used. This is a claim about the
item's proof, not a claim that other targets no longer use those modules.

`lem-weil-pbc-spec-colimit-limit` and `lem-pc-filtered-colimit-commrings-elementwise` move from
the item's direct proof dependencies to the new zero-map node's proof dependencies. They
remain necessary there and are not claimed pruned. No unit statement or realized step was
removed; the unit's `realized` arrays contain no binding for this item.

## Where the brief, the DAG or earlier work was wrong

The existing module-map descent theorem has only object and morphism lifting clauses, not
an eventual-equality clause. It cannot by itself establish the item's relations.
Its affine dependency does have equality descent over a ring colimit, but its interface does
not supply the scheme-module/affine restriction transport and gluing required here. Existing
Hom-directed-colimit lemmas concern diagrams of modules on one fixed scheme, not this varying
base-change system. Those are not silently substituted for the missing argument.

The old node's step 2 literally says that zero pullback to the limit also makes the difference
zero at every later finite stage. That is false: for example a nonzero element of Z can die
when one transitions to Z/(2). Persistence applies after the map has become zero at some
finite stage. The new route states and uses this implication in the correct direction.

Searches: LeanFinder found structure-sheaf section descent lemmas in
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`, not module-map descent. Loogle's query
`Functor.Additive, _ - _` returned no hits because that identifier was unknown to the service.
LeanSearch returned Internal Server Error; this is recorded as unavailable, not as a negative
search result. Direct source searches covered Mathlib and WeilConjectures module APIs and
Sheaf's module-descent, tensor-pullback, and Hom-colimit files. Blueprint searches for
`module map zero` and `01ZR` found no blueprint node to reuse.

## New nodes

`lem-pc-fp-zero-map-descent`, at
`dag/nodes/sec-picard-framework/lem-pc-fp-zero-map-descent.json`, corresponds to
`AlgebraicGeometry.finitePresentation_zero_map_descent`. It isolates the single-map vanishing
part of steps 2–3 of the existing proof and synchronization of the affine cover for that map.
The original module proves finite synchronization across the relations. The new node retains
the existing generic Mathlib tools for affine limit coordinate rings and elementwise filtered
colimits. Its statement is strictly a component of the finite-family argument and has a
finite type source, rather than just renaming the original finite-family theorem.
No change records or forced adaptations are needed: no existing interface changed.


## Second reading by P2

1. **Interfaces: PASS.** Diffed the delivered module against the repository. The
   existing declaration's complete signature is byte-for-byte identical (also
   checked programmatically); its visibility and all public imports are unchanged.
   The only Lean changes are proofs, two private proved helpers, proof imports,
   and the new single-map theorem. No definition or target statement changed.
2. **Proof and axioms: PASS, with the declared lower hole.** Both modules compiled
   together through lcompile.py without errors or warnings. A scratch copy with
   `#print axioms` confirmed that the two private helpers use only `propext`,
   `Classical.choice`, and `Quot.sound`. The main theorem additionally uses
   `sorryAx` from `AlgebraicGeometry.finitePresentation_zero_map_descent`.
   This is the only delivered sorry; it is a named public theorem with its full
   proof and source in its docstring. There are no definitions, forbidden trust
   extensions, or arbitrary data chosen from an unproved existence assertion.
3. **New statement: PASS.** Read the finite affine-cover and finite-matrix proof,
   including extension-of-scalars transport and vanishing on a cover. The tail
   of indices above j is cofinal by directedness, so its affine ring colimit is
   the ring of the prescribed limit. Finite presentation of the target gives
   finite vectors witnessing vanishing; finite type of the source gives finitely
   many images to kill. Neither quasi-separatedness nor Noetherianity is used.
   Checked empty relation families, zero modules, empty schemes, singleton index
   sets and non-antisymmetric preorders. The split isolates one map and removes
   finite-family synchronization; it is a proper component, not the original
   family statement under another name. It cannot be closed in a few minutes
   with the available scheme-module interfaces.
   Independent msearch searches used `leanfinder` with finite-generator
   module-map vanishing, `grep` with eventual-zero/isLimit patterns, and `loogle`
   with `Functor.map_sub` (the latter reports an unknown identifier, not evidence
   of absence). Direct searches and reading the existing module-map descent and
   affine colimit interfaces found no theorem with this scheme-map conclusion.
   The relevant Mathlib hits concern structure-sheaf sections.
   Rechecked [Stacks 01ZR](https://stacks.math.columbia.edu/tag/01ZR) (3) and its
   first proof, and [Stacks 05N7](https://stacks.math.columbia.edu/tag/05N7) (3).
4. **Route and pruning: PASS.** Additivity, finite upper bounds, and naturality of
   the pullback composition isomorphism are proved from existing APIs. The old
   module-map lifting theorem does not assert eventual equality. Its proof
   import is correctly removed. All three old direct proof dependencies are
   accounted for: the lifting node is unnecessary here, and the two ring-limit
   tools move to the new node. Proof-only imports have plain `import`; public
   imports support the unchanged signatures. The unit's `realized` statement
   and step arrays are empty, so this route bypasses no realized unit step.
   The unchanged original theorem docstring still describes the former four-step
   plan and optional map alignment; the actual two-step route is recorded in
   the updated node and above. This is documentary history, not a proof premise.
5. **DAG: PASS.** Compared the old and delivered relation nodes: only `proof`,
   `proof_deps`, and `proof_origin` changed. Their two steps match the Lean proof.
   The new node has the required source, statement dependencies, complete proof,
   proof dependencies, search records, split status, provenance, chapter, unit,
   and Lean record. Its Lean statement matches the new declaration. Both lower
   dependencies are existing Mathlib leaves rather than missing declarations.

**Changes by the second reader:** appended this review and recorded independent
searches. No Lean or node repair was necessary. The result remains one original
hole closed and one strictly lower hole added: decomposition, zero net holes
closed, not an axiom-free proof of the target.
