## What changed

Repaired `Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk` against the synchronized
source. The private universal-homeomorphism lemma is proved using the upstream field
strict-henselization theorem, and the main additive-equivalence theorem is proved by composing
the strict-henselization stalk formula, derived-functor comparisons, topological invariance, and
pullback coherence. The proof imports were reduced to the modules actually used: the retained
field module, strict-henselization structural map, stalk formula, derived sheaf cohomology,
and topological invariance APIs. Both the item and its unchanged direct consumer
`WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension` compile against the
repaired module (24.8 seconds and 12.5 seconds, respectively). No consumer adaptation is needed.

## Proved and sorry left

The theorem
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure`
and the private helper
`isUniversalHomeomorphism_field_strictHenselizationEval` are proved. No `sorry` remains in the
item module; no new `sorry` is added. Thus 2 of 2 existing holes are closed, 0 are added,
and 0 are split off. The public theorem is attached to node
`lem-sc-field-higher-direct-image-stalk`; the other closed hole was a private helper.
The completed proof uses the existing strict-henselization structural-map and stalk-formula
statements; it makes no claim that all their transitive dependencies are sorry-free.

## No longer needed

The proof no longer imports `Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal`,
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`,
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`, or
`WeilConjectures.Mathlib.FieldTheory.IsSepClosed` directly. Node
`lem-weil-pbc-strict-henselization-chart-maximal-ideal` is removed from this node's proof dependencies; its general chart theorem is no longer needed by this proof.
The local-structure and purely-inseparable nodes remain dependencies through the upstream field
theorem. The field theorem supplies the
universal-homeomorphism construction, and the structural-map API supplies the project map.
A source import-closure comparison confirms that only
`Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal` leaves this module's closure;
the other removed direct imports remain transitively reachable. This is a local closure
comparison, not a claim about pruning from every target's closure.

## Where the brief, the DAG or earlier work was wrong

The return reports failure against the source after upstream synchronization. The retained sandbox
already had a proof, but the current repository baseline has two holes. This repair keeps that proof,
updates the dependency imports, and checks it against the synchronized published library.

The project `strictHenselizationScheme` is a separate small colimit construction from upstream
`strictLocalization`; they are not compatibility abbreviations. The proved private helper
`strictHenselizationComparison_over` verifies that the colimit comparison commutes with the two
structure maps. The proof transports the evaluation through this isomorphism before forming the
pullback, so it does not assume these schemes are definitionally equal.

Searches repeated with LeanFinder (8 unrelated stalk/etale hits), Loogle
(`"IsUniversalHomeomorphism"`: no hits), Mathlib grep (no hits), and local source search.
The exact field universal-homeomorphism theorem is now available in the source library.


## Second reading by K4

1. **Signatures and visibility — pass.** Read the complete repository/sandbox diff.
   The signatures of the existing private universal-homeomorphism helper, private
   strict-localization cohomology comparison, and public
   `AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure`
   are byte-for-byte identical. The four public imports are identical; all import changes
   concern proofs. No definition or target changed, and there is no consumer adaptation.
   The added `strictHenselizationComparison_over` is a proved private helper.

2. **Proof and axioms — pass with existing dependency holes.** Independently compiled the
   item cleanly using `lcompile.py` (25.1 seconds). A scratch copy with `#print axioms`
   checked all four declarations: the field helper and new structural-map comparison use
   only `propext`, `Classical.choice`, and `Quot.sound`; the strict-localization comparison
   and public theorem additionally inherit `sorryAx` from existing dependencies.
   The upstream field theorem itself has only the three permitted axioms. No `sorry` or
   forbidden declaration occurs in the delivered module. The choices of the restriction
   morphism and cohomology comparison occur inside a proof of `Nonempty`, not a definition.
   The structural map's defining existence theorem pins the map by its composites with
   every neighbourhood leg, so it determines the object used downstream.

3. **Split statements and shorter results — pass.** No split-off statement, new hole, or
   new public statement is delivered. Repeated LeanFinder search with the different query
   “Higher direct image evaluated at a geometric point over a field equals cohomology
   after extending scalars to an algebraic closure” returned cohomology definitions and
   unrelated residue-field facts, no equivalent stalk theorem. Loogle for
   `"strictHenselization"` and Mathlib grep for
   `strictHenselization|strictLocalization|sheafFiber.*rightDerived` returned no hits.
   Local searches found the exact proved upstream field theorem already used, and no
   existing project/upstream lemma replacing the structure-map comparison. Read the
   upstream field proof: injectivity uses reduced Artinian etale algebras, and the
   separable-element lifting theorem gives the purely inseparable extension. The
   algebraicity hypothesis follows from `IsAlgClosure K L`; no perfectness assumption
   enters. This covers both positive and zero characteristic, including an already
   algebraically closed ground field. The stalk formula takes the stated qcqs and torsion
   hypotheses; the argument also covers degree zero, the zero sheaf, and an empty source.

4. **Route and pruning — pass.** Read Stacks `etale-cohomology.tex`,
   `theorem-higher-direct-images` (Tag 03Q9) and `proposition-topological-invariance`
   (Tag 03SI), and blueprint `lem-sc-cd-ground-field.md`. The proof follows exactly the
   stalk-formula then purely-inseparable/topological-invariance route. Locally finite
   type over a field supplies local Noetherianity and quasi-separatedness; quasi-compactness
   is assumed. The colimit comparison's coprojection equality proves compatibility with
   the two actual structure maps before the pullback is formed. The pullback cancellation
   proves that `g` is a base change of the universal homeomorphism, and `upperStarComp`
   identifies the coefficient sheaf in the correct direction. The five removed direct
   imports and the sole removed old proof dependency are all listed above. All retained
   imports provide signature notions or named proof APIs. The unit record
   `dag/units/sk-prop-sf-cbc.json` has empty `realized.statement` and `realized.steps`;
   no recorded realization or unit route is bypassed or changed.

5. **DAG agreement — pass after clarification.** The node's Lean statement matches the
   unchanged public signature; its only changed fields are `proof`, `proof_deps`, and
   `proof_origin`. The proof dependencies equal the union of the steps' `uses`, and the
   chart-maximal-ideal node is the only removed old dependency. Read the local-structure,
   structural-map, Noetherianity, quasi-separatedness, and purely-inseparable spectrum
   node statements against their uses. Clarified step 2 to name the exact upstream field
   theorem and its field-specific argument, and to distinguish its retained transitive
   inputs from the direct structural-map comparison. No new node is needed for an open
   statement: none is introduced.

Second-reading changes: clarified the existing DAG proof step and provenance; corrected
pruning precision in this report and added the independent checks above. The Lean proof
was left as written because no defect was found. Two original local holes are closed,
zero holes are added, and zero statements are split off; the public theorem's inherited
`sorryAx` is explicitly reported rather than counted as a fully axiom-clean closure.
