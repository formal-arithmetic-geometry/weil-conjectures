## What changed

Proved `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_counit_cocycle_calculation` with its exact original signature, arbitrary injective target R, arbitrary augmented lift L and all degrees. The proof replaces the forgotten source by a genuine abelian injective resolution, uses the existing source comparison evaluation, compares the two target lifts by homotopy, and applies the proved injective cocycle calculation.

`AbelianExtSectionsCocycleNormalization.lean` proves the missing normalization of the actual fixed Ext-to-sections constructor. It computes the chosen-resolution Hom cocycle, extends the result to every injective resolution by comparison and cancellation, then transports it through the sections natural isomorphism. `TerminalSourceSectionsEvaluation.lean` proves evaluation of the actual terminal-source map at the integer generator. `AbelianInjectiveCounitCocycle.lean` combines these with the already-proved exact-functor cocycle theorem and the actual Zariski adjunction/restriction calculation.

Moved the unchanged counit definitions and the existing proved source evaluation theorem into `AbelianCounitCocycleDefinitions.lean`. The old evaluation module now re-exports that theorem. Normalized `abelianInjectiveResolutionIso` to the usual injective constructor, with a complete equality proof against its former acyclic constructor. This preserves the fixed comparison rather than selecting a different equivalence. Change record: `coord/changes/abelian-counit-cocycle-comparison-normalization.md`.

All six delivered Lean modules compile individually through lcompile in import order. The complete pre-cleanup build took 18.4 s, 2.7 s, 36.6 s, 54.8 s, 1.5 s and 30.4 s respectively. The unchanged direct consumers `AbelianCounitResolutionCalculation` and `AbelianReplacementSectionHomotopiesCoreParts` also compile against the sandbox overlay, in 31.6 s and 18.9 s. Their source files are not delivered. The required dry run printed OK: the commit compiles and passes preflight except for the second reading, which the second reader writes; nothing was pushed. Its probe checked every delivered declaration. Explicit `#print axioms` for the leaf, the fixed site-sections cocycle normalization, the injective/acyclic comparison and the representative-transfer lemma shows exactly `propext`, `Classical.choice`, and `Quot.sound`. No new unresolved node or theorem is added. The unit’s statement and realized steps are preserved.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_counit_cocycle_calculation` (`new-abelian-counit-cocycle-calculation`). One of one original sorries is proved; zero holes are split off or added. No delivered Lean declaration contains `sorry`.

The new public proofs are `CategoryTheory.acyclic_comparison_of_injective`, `CategoryTheory.homology_transfer_of_cycle_representatives`, `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.canonical_site_sections_cocycle`, `terminal_source_sections_evaluation`, `abelianInjectiveResolutionIso_eq_acyclic`, and `abelian_injective_counit_cocycle_calculation`. All are complete. The existing `abelian_resolution_comparison_evaluation` remains proved and retains its signature and visibility. Every helper theorem is proved. The named local additive instances contain concrete proofs of additivity.

## No longer needed

Removed the item’s direct proof imports `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic` and `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`. Replaced its direct `AcyclicComparisonNatural` import by the lower module containing the existing proved source evaluation. A transient direct `ExactFunctorResolutionCocycle` import is also removed from the item; only the injective calculation uses it. The redundant public `FlatCohomologyComparison` imports in the item and the injective calculation are removed because their public definitions module supplies it. The generic normalization does not need `AcyclicComparisonNatural` as a direct import.

The old evaluation module no longer imports the leaf or `AcyclicComparisonNatural`; it publicly re-exports `AbelianCounitCocycleDefinitions`. The old direct dependency `lemma-weil-pbc-leray-acyclicity` is unused by this cocycle argument. `lem-sc-injective-module-abelian-acyclic-zariski` and `lem-sc-acyclic-comparison-natural` are needed below the existing source normalization/evaluation, not as separate steps proved here. Their modules remain used elsewhere, so no whole library module is withdrawn or claimed globally pruned.

The proof does not use `objectCohomology_resolution_cocycle_equivalence`, an arbitrary existential Ext/sections comparison, `Adjunction.mapExtCounit_bijective`, a degree-zero specialization, a target module resolution, or a generic derived-category roof construction added for this item. No new node for these is needed. The supplied route prototypes are incorporated into complete calculations, not imported as experimental modules.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or target weakening. The route note was correct. Its remaining fixed-constructor representative calculation is now proved explicitly. Forgotten module injectives are used only as section-acyclic terms; they are never assumed abelian-injective. Direct image is used additively and no exactness of that right adjoint is assumed.

The proved source evaluation could not be imported from its former module because that module publicly imported the leaf. It has been moved below the leaf with its original public name and signature. The initial homology presentation mismatch was resolved by an abstract cycle-representative lemma and explicit simplification of the homology functor presentation. Large acyclic constructors are kept irreducible and accessed through a proved equality API, rather than raising the limit or splitting an unfinished proof to evade it.

## New nodes

`def-pc-abelian-counit-cocycle-comparisons`: the relocated counit constructors, with the computational injective form. Their original meanings are preserved by the equality theorem.

`new-abelian-injective-acyclic-comparison`: the proved equality of the acyclic and ordinary injective-resolution comparisons, using identity-lift naturality and cancellation.

`new-abelian-injective-resolution-comparison-normalization`: the proved equality of the normalized counit constructor with its original acyclic form.

`new-abelian-cycle-representative-transfer`: the proved elementary passage from source and target cycle formulas to every homology class, using the surjective homology projection.

`new-abelian-ext-sections-cocycle-normalization`: the completed fixed site-sections cocycle formula, including the chosen Ext/Hom constructor cancellation and arbitrary-resolution comparison.

`new-terminal-source-sections-evaluation`: the proved evaluation of the actual terminal-source isomorphism on the integer generator.

`new-abelian-injective-counit-cocycle`: the completed cross-site calculation for genuine abelian injective source and target resolutions. It uses the existing exact-functor cocycle theorem.

The two existing nodes `new-abelian-counit-cocycle-calculation` and `new-abelian-resolution-comparison-evaluation` have updated proofs/dependencies; the latter’s Lean attachment follows the moved theorem. Change record: `coord/changes/abelian-counit-cocycle-comparison-normalization.md`.

## Second reading by H3

1. **Signatures and accidental changes — pass.** I diffed the delivered calculation and
evaluation modules against `sheaf-dag`. The target theorem and the existing evaluation
theorem retain byte-for-byte signatures. The moved constructors are covered by the open
change record, whose equality theorem preserves the former injective comparison. No other
held module is adapted.

2. **Proof and axioms — pass.** I compiled all six delivered modules with
`lcompile.py --all`; the import-ordered build exits successfully. There are no `sorry`,
axiom, unsafe, opaque, extern, or implemented-by declarations in delivered Lean files.
The proof uses only the permitted standard axioms, as recorded by the delivery probe.

3. **Split statements — pass.** I checked each new node and its declaration against the
existing library and the recorded searches. The seven new statements are genuine
intermediate calculations or definitions, strictly used by the completed proof, and none
is a restatement of the item. No holes were added.

4. **Pruning and route — pass.** The leaf uses the source comparison evaluation,
injective cocycle calculation, and homotopy APIs directly. The removed imports are proof
only and are listed above; no public statement dependency was removed. The unit
`sk-thm-p1` statement and all realized steps remain unchanged.

5. **DAG agreement — pass.** I checked the delivered node `lean`, `proof`,
`proof_deps`, and `proof_origin` fields against the imports and theorem applications. The
constructor change is documented in
`coord/changes/abelian-counit-cocycle-comparison-normalization.md`; the moved evaluation
attachment and all new nodes match their Lean declarations.

I changed only this report section: the delivered Lean proofs, node metadata, and change
record required no repair.
