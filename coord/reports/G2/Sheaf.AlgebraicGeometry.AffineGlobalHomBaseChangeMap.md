## What changed

Proved `AlgebraicGeometry.exists_affineDerivedExtension` in
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`. Specialize the existing
`CochainComplex.mixedTensor_kFlat_quasiIso` to the tensor unit concentrated in degree
zero. The single-complex comparison and left unitor identify its map with termwise
extension. Naturality transports the quasi-isomorphism through two arrow isomorphisms.
This supplies `PreservesKFlatQuasiIso`, so the existing source-library
`Adjunction.derivedAdjunction` applied to `ModuleCat.extendRestrictScalarsAdj` gives the
adjunction. Transport its right adjoint through exact restriction's
`rightDerivedFunctorIsoMapDerivedCategory`.

Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`,
`Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso`.
All existing signatures and visibility are preserved. The unused-section-variable
linter is disabled locally to retain the original theorem signature. Updated the
parent node's proof, proof dependencies, and proof origin.

Short-route searches: launcher LeanFinder found underived scalar adjunctions only;
Loogle `ModuleCat.extendScalars` found its underived functor and adjunction; launcher
grep for scalar extension/K-flatness returned no exact match. Direct repository
search found the mixed tensor theorem and the source-library derived adjunction.

## Proved and sorry left

Closed one of the original two holes:
`AlgebraicGeometry.exists_affineDerivedExtension`.
No holes were added or split off. The previously proved
`AlgebraicGeometry.exists_canonicalTensorHomAdjunction` remains proved.

The only remaining hole in the delivery is
`AlgebraicGeometry.exists_globalHomPullbackComparison`, at
`def-pc-affine-global-hom-base-change-map`. Its original statement and complete
natural-language proof are retained. This delivery is partial, not a decomposition.
The scalar-extension argument is valid also for zero rings and nonflat ring maps:
the mixed tensor theorem imposes no flatness hypothesis, and the two transports are
natural isomorphisms of unbounded complex functors.

## No longer needed

No baseline import, node, or module is pruned. The second reading removed the
redundant newly added proof imports `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`
and `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`; their declarations
are already publicly reachable through retained imports. No new statement module is needed for
scalar extension: existing mixed tensor and generic derived-adjunction theory suffice.
The previous sandbox-only `exists_globalHomPullbackComparison_data` was removed;
it neither appears in this delivery nor represents a useful reduction.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had an auxiliary theorem ending in a dangling conjunction,
so it did not compile. More substantially, deleting only the final explicitly defined
arrow from the comparison existential merely repackages its obligation. That approach
was discarded. The repository already contains a node of the proposed auxiliary name,
`def-pc-affine-global-hom-base-change-map-data`, but no corresponding theorem in the
baseline module; this delivery does not use or modify that record.

The original node's partial proof record covered only tensor-Hom adjunctions. It now
also records scalar extension and explicitly identifies the remaining global-comparison
obligation. The unit's realized statement and steps are not bypassed; the change is
within the construction node.


## Second reading by G2

1. **Visible declarations unchanged — pass.** Compared the entire delivered module
   with the repository using `diff -u` and the delivery declaration parser. All
   sixteen existing declaration signatures are byte for byte identical, with the
   same visibility, and every definition body is unchanged. Only the proof of
   `AlgebraicGeometry.exists_affineDerivedExtension` changes. No change record is
   required. Restored its original docstring rather than retaining the first
   worker's rewrite.
2. **Proof and axioms — pass for this partial delivery.** The final module compiled
   without errors or warnings; a scratch copy with explicit `#print axioms` compiled
   in 38.7 seconds. `exists_affineDerivedExtension`, `affineDerivedExtension`, and
   `affineDerivedExtensionAdjunction` use exactly `propext`, `Classical.choice`, and
   `Quot.sound`. The previously proved tensor-Hom theorem and final base-change map
   also use `sorryAx` through still-open dependencies. The only direct hole is the
   unchanged named theorem `exists_globalHomPullbackComparison`, with its source,
   complete proof docstring and matching node. There are no forbidden declarations,
   no holes inside definitions, and no new objects chosen from unproved arbitrary
   existence. The witness supplied by the new proof is the constructed source-library
   left derived functor with its derived underived scalar adjunction. The inherited
   pullback-normalization repair identified in `coord/hollow-definitions.md` and the
   module's REPAIR comment remains a separate open issue; this proof-only delivery
   does not claim to repair it. Two initial timed-out compiles were followed by a
   full successful compile in 36.5 seconds and the final scratch axiom compile;
   neither the file nor a proof was split for delivery, and the limit was not changed.
3. **Split statements — pass, none added.** There are no new statements or new nodes
   and no auxiliary restatement of the remaining comparison. Checked the existing
   mixed-tensor quasi-isomorphism theorem: its first clause applies to arbitrary
   coefficient complexes and K-flat source and target complexes. Specialization to
   the tensor unit in degree zero is valid for zero rings, identity ring maps,
   nonflat ring maps and unbounded complexes. Naturality gives both commuting arrow
   squares; neither transport adds a hypothesis. Independent LeanFinder search for
   unbounded scalar-extension adjunctions, Loogle for `extendRestrictScalarsAdj`,
   Mathlib grep for derived scalar-extension/K-flat statements, and repository
   searches found no shorter exact theorem. The available module K-flat base-change
   lemma proves preservation of K-flatness, a different obligation.
4. **Top-down route and pruning — pass.** The proof directly closes the existing
   scalar-extension obligation using the already proved mixed-tensor theorem and
   generic source-library derived-adjunction construction. The global comparison
   remains open rather than being renamed. Removed two redundant newly added proof
   imports: `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed` and
   `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`; retained imports
   publicly reexport their declarations. All added imports are proof-only. The
   sole old proof dependency `def-pc-canonical-derived-tensor-hom-bijection` remains
   used by the unchanged tensor-Hom proof; no baseline dependency is prunable.
   Read `dag/units/sk-thm-picard-duality.json`: its statement and step route are
   untouched, its `realized` lists are already empty, and this construction node
   realizes neither a unit statement nor a step. No unit is bypassed.
5. **DAG matches Lean — pass.** The sole delivered node changes only `proof`,
   `proof_deps` and `proof_origin`. Its two proof steps correspond to the retained
   tensor-Hom construction and the new scalar-extension construction. Their uses
   have exactly the recorded union: the canonical tensor-Hom node and
   `lem-pc-mixed-tensor-kflat-quasi-iso`. The record expressly marks the global
   comparison as unproved. No statement, source, unit or Lean declaration record
   changes, and there are no new-node fields to validate.

Second-reading changes: restored the original scalar-extension theorem docstring,
removed the two redundant proof imports, and corrected this report's import list and
pruning description. Mathematical proof bodies and DAG records needed no repair.
Net direct holes closed: one; holes added: zero; baseline modules pruned: none.
