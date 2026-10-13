## What changed
Proved `AlgebraicGeometry.Etale.sourceCocycleExactRestriction` with its original
signature and public import unchanged. Three proved private helpers calculate
exact-functor homology projections, restriction of the evaluated cocycle before
localization, and transport of homology through exact derived functors.

The cocycle calculation cancels the monic image of the cycle inclusion, checks
degreewise evaluation with `Cochain.fromSingleEquiv_fromSingleMk`, and uses
naturality of the arbitrary transformation for cycle inclusion and projection.
The final calculation uses naturality of the localization factorization,
`mapDerivedCategoryHomologyFunctorIso_hom_app_Q`, restriction to the bounded-below
category, and naturality for the specified representative transport.

Updated the existing node's proof and proof origin to describe these calculations.
No statement, definition, visibility, or dependency interface changed. Read Stacks
Tags 03Q9 (theorem-higher-direct-images), final proof paragraph, and 03QO
(lemma-vanishing-etale-cohomology-strictly-henselian). The unit record
`sk-prop-h2` has no realized nodes for its statement or proof steps here; its route
is unchanged. Compiled the complete assigned module without warnings in 20.6 s. A separate
`#print axioms AlgebraicGeometry.Etale.sourceCocycleExactRestriction` check lists
exactly `propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`).

## Proved and sorry left
Closed the sole original hole:
`AlgebraicGeometry.Etale.sourceCocycleExactRestriction`
(node `lem-weil-pbc-source-cocycle-exact-restriction`).

Holes closed: 1. Holes added: 0. Sorries left in delivered modules: none.
The private helpers `exactHomologyProjection`, `sourceSectionsCocycleRestriction`
and `exactHomologyTransport` are fully proved. This is a proof, not a decomposition.
No holed theorem is used as a proof dependency: from SourceLocalizedCocycleHomology
we use only the actual definition `sourceCocycleHomologySection`.

## No longer needed
No imports, nodes, or modules removed. The sole original public import provides
`sourceCocycleHomologySection` and is still required by the public statement.
The theorem `sourceLocalizedCocycleHomology` is not needed for this proof, but its
module and node also supply that definition, so they cannot be pruned here.
No K-injectivity, localized-Hom bijectivity, stalk comparison, or base-change mate
is needed, as in the original statement. No new proof imports remain.

## Where the brief, the DAG or earlier work was wrong
The earlier sandbox delivery left the assigned theorem sorry and was therefore
not a valid reduction. It is now proved in full. Its private transport helper
was reusable. The earlier copied dependency module and temporary public helper
module have been removed from the delivered source set.

The shared SourceLocalizedCocycleHomology artifact is now available; no workaround
or dependency adaptation is necessary. The original DAG plan was mathematically
correct but compressed several different naturality calculations into one step;
the updated node makes the kernel cancellation and derived transport explicit.
Edge cases use the same calculation: zero cocycles and zero complexes map to zero;
there is no positivity restriction on n, nor an injectivity assumption on L.

## Second reading by K1

1. **Interface: pass.** Compared the delivered module with the repository version
   using `diff`, and separately compared the text from
   `theorem sourceCocycleExactRestriction` through its final type: byte-identical.
   The original docstring, visibility, universe, arbitrary natural transformation,
   unrestricted integer degree, arbitrary complex L, cycle hypothesis, representative
   isomorphism r, and complete displayed conclusion are preserved. No definitions or
   other modules are delivered. Only three private proved helpers are added.
2. **Proof and axioms: pass.** Independently compiled the delivered module without
   errors or warnings (24.1 seconds). Scanned the delivered Lean for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, and skipped kernel checks: none.
   Compiled a scratch copy with `#print axioms` for the theorem and all three private
   helpers; each uses only `propext`, `Classical.choice`, and `Quot.sound`.
   `sourceCocycleHomologySection` is the actual lift-to-cycles, homology projection,
   localized homology transport and free-generator evaluation; its data is not chosen
   from an unproved existence theorem. The open theorem
   `sourceLocalizedCocycleHomology` is not invoked.
3. **Split statements: pass, none.** No new public statement, node or hole is added.
   Read all three private helper statements and proofs: `exactHomologyProjection`
   compares the mapped quotient projection; `sourceSectionsCocycleRestriction`
   computes the cycle before localization; `exactHomologyTransport` concerns an
   arbitrary exact additive functor and arbitrary transport morphism. All are proved.
   The cycle calculation cancels the preserved monomorphism G(U(iCycles)), evaluates
   `fromSingleMk`, then applies naturality at iCycles and homologyπ. It requires no
   monomorphism assumption on f, no K-injectivity and no positivity of n. Zero f,
   zero complexes, negative degrees and the zero natural transformation introduce
   no exceptional case: all maps in the calculation remain the same additive maps.
4. **Route and pruning: pass.** Read the definitions in
   `StrictLocalInjectiveSourceComparison` and `SourceLocalizedCocycleHomology`, and
   the strict-local exactness interface. Read Stacks
   [03Q9](https://stacks.math.columbia.edu/tag/03Q9), final proof paragraph
   (`theorem-higher-direct-images`), and
   [03QO](https://stacks.math.columbia.edu/tag/03QO)
   (`lemma-vanishing-etale-cohomology-strictly-henselian`). The source supplies
   degreewise restriction and exact sections; this theorem is their formal
   compatibility calculation, without importing the source's unrelated hypotheses
   on a higher-direct-image morphism. Searched library/upstream sources for mapped
   homology projections, exact derived homology transport and cocycle restriction;
   the additional msearch grep had zero hits. Read Mathlib's `NatTrans.app_homology`:
   it assumes both functors preserve homology, whereas neighbourhood sections in τ
   need not be exact, so it does not replace this cycle-level argument. The proof
   already uses the generic projection and exact derived comparison lemmas.
   The only import supplies definitions appearing in the unchanged statement and
   must remain public. All three old proof dependencies still supply constructions
   used by the proof; no old dependency is omitted from `## No longer needed`.
   Checked `dag/units/sk-prop-h2.json`: realized statement and step arrays are empty;
   this delivery changes no unit route.
5. **DAG: pass.** Only `proof` and `proof_origin` differ from the existing node.
   Its statement, statement dependencies and Lean record are unchanged. The union
   of step `uses` equals `proof_deps`. Step 1 matches the quotient projection and
   monic cycle-inclusion calculation, step 2 matches localization naturality and
   `mapDerivedCategoryHomologyFunctorIso_hom_app_Q`, and step 3 matches bounded-below
   restriction and naturality at the explicit morphism b. The localized-cocycle
   dependency is used for its constructed section, as the updated proof says,
   rather than for its still-open comparison theorem.

**Changes after reading:** appended this independent review and added scratch-only
axiom checks. No repair to the Lean proof, imports, signatures or node was needed.
Verified holes closed: `AlgebraicGeometry.Etale.sourceCocycleExactRestriction` (1).
Holes added: none (0). This delivery is a complete proof, not a decomposition.
