## What changed

Proved `AlgebraicGeometry.Etale.pullbackCohomology_longExact_ladder` in
`Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`, preserving its signature,
docstrings and imports. Updated its DAG proof to the direct Ext argument. The
existing source-library `Sheaf.H.δSucc` and exactness results are already available
through the original TopologicalInvariance import. No new module is required.

## Proved and sorry left

Proved the module's only sorry: `AlgebraicGeometry.Etale.pullbackCohomology_longExact_ladder`
(node `lem-weil-pbc-pullback-cohomology-long-exact-ladder`). The proof constructs the
pulled-back short exact sequence and both specified boundaries, proves both initial
injections and all six exactness assertions, and proves the three commuting squares.
No sorry remains in the item and none is added elsewhere. Local compilation passes.
The delivery dry run also checks axioms and compilation on the server.

## No longer needed

No original import was removed and no proof import was added. The following planned
proof dependencies are unnecessary for this module's direct Ext proof (this is local
pruning, not a claim that other users no longer need them):

- `lem-sf-derived-ses-triangle`
- `def-weil-pbc-derived-categories`
- `def-weil-pbc-abelian-etale-sheaves`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `def-weil-pbc-etale-cohomology`
- `lem-sf-derived-homology-long-exact`
- `def-weil-abstract-derived-category`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-cohomology-pullback-derived-unit`
- `def-weil-pbc-derived-inverse-image`
- `lem-sf-exact-functor-derived-triangulated`
- `def-weil-pbc-triangles-with-shift`
- `prop-weil-pbc-derived-inverse-image-adjunction`
- `lem-weil-pbc-kinjective-shift`
- `lem-weil-pbc-commshift-nattrans-triangle-morphism`
- `lem-weil-pbc-derived-cohomology-ladder`

In particular, the separate modules EtaleInverseImageExact, DerivedCategories,
EtaleModuleEnoughInjectives, EtaleCohomologyPullbackFunctorial and
CohomologyPullbackDerivedUnit need no proof import here. The planned derived-functor,
K-injective and triangle-ladder machinery is not needed. Statement dependencies and
the blueprint unit's realized statements and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The older searches in the node missed the now-present source-library lemmas
`Sheaf.H.δSucc`, `Sheaf.H.exact_map_δSucc` and `Sheaf.H.exact_δSucc_map`.
For the recorded Lean statement, no general derived pullback or comparison of
K-injective representatives is needed: exact functors preserve extension classes.
This delivery does not prove the independent bridge between Ext-defined cohomology
and the derived-global-sections encoding; that bridge remains separate as recorded
in the cohomology definition node. The existing statement explicitly specifies
postcomposition with extClass, and it is proved unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the complete delivered module with the repository using `diff -u`.
   Verdict: only the existing theorem's proof body differs; its signature,
   definitions, docstrings and imports are byte for byte unchanged. No change
   record is needed.
2. Compiled the module locally without errors or warnings. Scanned the whole
   module for sorry and forbidden declarations: none remain. Compiled a scratch
   copy with `#print axioms AlgebraicGeometry.Etale.pullbackCohomology_longExact_ladder`:
   exactly `propext`, `Classical.choice`, `Quot.sound`. Verdict: a complete proof.
3. No statements or modules were split off or added. Read the δSucc definition,
   its exactness lemmas, cohomologyMap_apply and cohomologyMap_map in the existing
   source library. The construction includes degree zero and arbitrary natural
   degrees, with no nonemptiness, characteristic or scheme restrictions added.
   Verdict: no new statement needing an edge-case or duplication check.
4. Read the proof from its existential witnesses down through all nine conjuncts.
   The exactness lemmas give both ladders and the monomorphisms give both initial
   injections; associativity and preservation of extension classes give the last
   square. Searched the source library with `rg` for δSucc, map_of_exact,
   postcomp_mk₀_injective_of_mono and mapExactFunctor_extClass. Gabber already has
   the boundary square, but importing that larger module solely to replace this
   three-line calculation would add unnecessary dependencies. Both original
   imports provide names used by the statement. The 18 original dependencies
   listed above are all those omitted from the new proof_deps. Read
   dag/units/sk-thm-p1.json: this item is below its realized statements and steps;
   the unit's route and realized records are unchanged. Verdict: passes.
5. Found that the sandbox node was byte-identical to the repository, despite the
   first report's claim that it had been updated. Replaced only its proof,
   proof_deps and proof_origin with the actual direct Ext route, retaining the
   pullback-definition and extension-class compatibility dependencies. All other
   node fields, including its statement and Lean signature, remain unchanged.
   Verdict: repaired; no new nodes are required.

Second reading changed only the DAG proof metadata and this report; the Lean
proof was correct as delivered. The existing derived-global-sections comparison
obligation mentioned above is neither claimed proved nor changed by this item.

## New nodes

- lem-weil-pbc-sheaf-ext-cohomology-long-exact: source-library leaf recording the generic sheaf Ext long exactness and degree-zero injectivity declarations used in the first proof step.

## Second reading by Q1

1. Compared the delivered Lean module with the repository by `diff -u`: only the
   existing theorem proof body changes. All declaration signatures, definitions,
   docstrings and imports are byte for byte unchanged. Verdict: passes; no change
   record is required.
2. Compiled the sole delivered module using `lcompile.py --all`; no errors or
   warnings. Compiled the scratch copy with `#print axioms` for the theorem:
   exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry or forbidden
   declaration remains in the module. Verdict: a complete proof of the original
   statement, with no hidden sorry dependencies.
3. No Lean statement was split off or added. The new node records already proved
   generic source-library and Mathlib declarations. Read their proofs and section
   hypotheses: they apply at every natural degree, including zero, and to zero
   sheaves, without requiring a terminal object or extra scheme hypotheses.
   Independent local searches found no DAG node already carrying these generic
   sheaf declarations. Ran new searches via msearch: LeanSearch was unavailable
   (recorded without a verdict); Loogle and grep found generic Ext exactness.
   Verdict: no duplicate Lean theorem and no unproved split-off obligation.
4. Read the proof from the existential witnesses through all nine conjuncts.
   Exact inverse image gives hY; the defined boundaries are postcomposition with
   extClass. The existing exactness lemmas give each ladder; mono_f gives the
   initial injections. cohomologyMap_map gives the first two squares, and
   mapExactFunctor_extClass plus associativity gives the boundary square.
   Searched the source and Mathlib with different terms (covariant_sequence_exact,
   postcomp_mk₀_injective, map_δSucc). Gabber has the boundary calculation but
   importing it would add substantial dependencies for the same three lines.
   The original imports supply the statement cohomology/pullback and extClass
   vocabulary; no proof-only public import was introduced. Compared all original
   proof_deps: precisely the 18 nodes listed in No longer needed were pruned.
   Read sk-thm-p1.realized: this lemma is below its realized statement and steps,
   so the unit route stays unchanged. Verdict: passes.
5. Compared the existing node against the repository: only proof, proof_deps and
   proof_origin differ. Their dependency union agrees and the three proof steps
   follow the actual Lean argument. Checked the new source-library leaf and
   repaired its record: correct source path, full declaration names (one primary
   declaration plus a declarations list), verbatim primary signature, explicit
   site/topology hypotheses, full proof in words and actual logged searches.
   Verdict: repaired. This records existing proved results, not a new sorry.

Second reading changed only the new source-library node metadata and this report.
The Lean proof is correct as delivered and is unchanged. The derived-global-sections
comparison remains a separate obligation, as stated above; it is not claimed proved.
