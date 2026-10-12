## What changed
Removed the proposed ModuleCohomologyFMapCanonical module and its split node: comparing arbitrary data with the chosen datum is equivalent to the original independence theorem, so this was not a strict reduction. Restored the independence hole.

Proved source naturality and target naturality from the existing general composition clause and the identity clause of moduleCohomologyFMap_basic_properties. Proved pullback composition from general composition, target naturality, and the supplied adjunction-unit equation. Existing signatures, definitions, visibility, and docstrings are unchanged. Removed unused proof-only imports and updated the existing functoriality node to describe this partial realization.

## Proved and sorry left
Holes closed (3 of the original 6):
- AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_source_naturality
- AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_target_naturality
- AlgebraicGeometry.Scheme.Modules.moduleCohomologyPullback_comp

Holes added: none. These proofs use existing open statements; they do not yet give axiom-free cohomology functoriality.

Sorry left, all in node lem-weil-pbc-module-cohomology-fmap-functorial:
- AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_independent
- AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_comp
- AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_restriction

The proposed moduleCohomologyFMapData_map_eq_choice hole and node were removed, not delivered.

## No longer needed
Removed direct proof imports:
- Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
- Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
- Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso
- Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
- Sheaf.AlgebraicGeometry.TensorPullback
- Sheaf.Paper.PQFCohomology

Old proof_deps absent from the implemented partial proof (their comparison-resolution arguments are still plans for the three open clauses):
- def-pc-module-pullback
- def-pc-scheme
- def-sp-injective-resolutions
- lem-weil-pbc-complex-injective-resolution-mono
- lem-weil-pbc-derived-functor-map-via-lift
- lem-weil-pbc-homotopic-maps-equal-cohomology
- lem-weil-pbc-injective-resolution-lift-exists
- lem-weil-pbc-lift-along-injective-quasi-iso
- lem-weil-pbc-lift-to-injective-unique-up-to-homotopy
- lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso
- lem-weil-pbc-module-restriction-open-immersion-colimits
- lem-weil-pbc-scheme-modules-enough-injectives
- pqf-def-cohomology

No claim that these modules are globally unreachable: the cohomology-map definition and other imports may still reach them. The unlanded ModuleCohomologyFMapCanonical helper is removed from this delivery. No unit statement or realized step is bypassed or changed; this realizes the existing node's Step 7.

## Where the brief, the DAG or earlier work was wrong
The first worker's canonical-comparison assertion was equivalent to independence, not a strict intermediate lemma: independence implies it by comparing with Classical.choice of moduleCohomologyFMapData_nonempty, while two applications of it imply independence. Its proposed docstring also hid the full comparison argument. The earlier report's claim of a strict intermediate statement was incorrect.

Search: rg on lean/Sheaf and lean/WeilConjectures found no existing alternative proof of these clauses. Lean Finder query "cohomology maps along scheme morphisms composition and naturality" returned scheme-section composition lemmas, not these cohomology maps; Loogle query "Functor.map_comp" returned no identifier match. The shortest route for the three closed clauses is already the plan's identity special cases and adjunction-unit calculation.

## Second reading by U1
1. Compared all delivered modules against the repository using diff. All six existing declaration signatures are byte for byte unchanged; no definition or public import changed. No change record is needed.
2. Compiled the final module using lcompile.py. Only the three named original theorem holes remain. No axiom, unsafe, opaque, implemented_by, extern, or data-definition sorry is added. Scratch #print axioms checks for all six declarations admit only standard axioms and sorryAx from the remaining open statements/imports.
3. Rejected and removed the sole split-off theorem as equivalent to independence. No new statements or nodes remain. The new proofs quantify over arbitrary schemes, modules, maps, and all p, including zero, without extra assumptions; identity and zero morphisms require no separate cases because the categorical calculation applies uniformly.
4. The proofs follow the existing Step 7 from the top down, using the local composition clause and the imported identity property. Removed every unused direct proof import and listed every removed proof dependency above. Inspected dag/units/sk-thm-p1.json realized: the node is a tool below its realized unit steps, which are unchanged.
5. Updated the existing node's proof, proof_deps, and proof_origin to reflect the three implemented special cases and the three remaining open clauses. The statement, lean signatures, source, unit, chapter, and realized route are unchanged.

Second reading changed: removed equivalent canonical-choice split; restored independence hole; closed both naturalities and pullback composition; pruned six unused direct proof imports; aligned node and report with the partial proof.
