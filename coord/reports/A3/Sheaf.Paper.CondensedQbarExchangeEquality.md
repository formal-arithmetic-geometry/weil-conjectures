## What changed

Repaired the returned duplicate-definition refusal by retaining the four shared helpers
only in the right adjunct module. The finite-to-Qbar counit identity
`constructibleToQbar_push_counit` is now public, and the left adjunct imports and uses it.
The general `lifted_push_counit` is strengthened in place to take the coefficient
adjunctions and restriction/direct-image isomorphism, proving the mate identification
internally. Its proof and those of `push_eq_mate_pull_inv` and `restrict_counit_hom`
appear only once. Both adjunct modules retain their small generic naturality-lifting
lemmas, which prevent the restricted naturality calculation from unfolding resolution
constructions during kernel checking. No proof or module is split to evade the limit.

The shared source now proves the required base-change counit identity as
`boundedConstructibleBaseChange_adjunct`. The left proof uses that existing API.
Removed the duplicate proposed `Sheaf.Paper.CondensedBaseChangeCounit` module and
reattached its node to the existing source declaration. It never landed, so the fetched
delivery base has no file to withdraw and no `deleted.txt` entry is needed.

Replaced the stale MorphismDefs snapshot with the current shared source, preserving
its squareExchange presentation, component lemma, all signatures, proofs and imports.
The only source change is `@[no_expose]` on the unchanged
`boundedConstructiblePullbackSquareComparison` construction: the left proof exceeds
the artifact-generation limit when that derived construction is exposed.
The existing component and adjunct APIs remain public. Added only a proof-only
`import all` to the unclaimed BoundedExchangeAmbient module, whose original proof
requires the hidden defining body; details and the original error are below.

The combining proof of `constructibleToQbar_exchange_equality` retains its original
signature. The two adjuncts normalize to the same expression, and injectivity of the
inverse adjunction hom equivalence proves the equality.

H10 repair: diagnosed the timeout after ordinary elaboration and kernel checks.
Lean's `symbolFrequency` and `sineQuaNon` export extensions each traverse public
signature expressions with `foldRelevantConstants`. The concrete right-adjunct type
contains large inferred derived-category instance expressions; repeated `getFunInfo`
dependency scans spend most of the export time on that type. Opacity changes alone
did not resolve the timeout.

Added Lean's documented `LibrarySuggestions.nameDenyListExt` entry for the single
name component `constructibleToQbar_exchange_right_adjunct`. This avoids those
premise-suggestion scans for this concrete identity. Its full statement and proof,
every existing declaration signature, and public visibility remain byte-for-byte
unchanged from the returned right module. All six delivered modules remain intact;
no proof or file is split, no compiler limit is raised, and kernel checks still run.
The only functional limitation is that automatic premise suggestions omit this one
identity; the equality proof continues to apply it explicitly. The other public
counit identity and generic mate theorem remain indexed. The repair and its consumer
effect are recorded in `coord/changes/condensed-qbar-right-artifact-index.md`.

The right module exported in 28.5 seconds with an explicit 60-second timeout.
The subsequent six-module artifact run passed without warnings: right adjunct 25.9s,
pullback cube 26.1s, MorphismDefs 4.5s, BoundedExchangeAmbient 12.5s, left adjunct
43.6s, and combining equality 30.9s. The run used lcompile.py's unchanged 60-second
per-file limit. The required dry run passed its compilation and axiom probes; documentation-only
preflight findings were repaired before rerunning it. Its final log is
`scratchpad/h10-dry-run.log`.

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_exchange_equality`.
Both saved normalization statements are proved:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_exchange_left_adjunct` and
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_exchange_right_adjunct`.
The shared `lifted_push_counit` and the right module's public
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_push_counit` are proved.

The sole remaining delivery hole is the previously split
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube`
(`lem-weil-pbc-qbar-condensed-pullback-cube`). The integral specialization
`integralConstructiblePullIso_comp` is now proved in the current shared source. Its module
also contains the proved generic private `derived_pull_comp`, applicable to E-to-Qbar
coefficients. The remaining cube needs the bounded restriction of that generic identity,
its application to the two paths of the square, and equality-substitution coherence.
The second reader tested that route in scratch files; the full bounded conversion has
not yet compiled within the 60-second file limit. Its docstring and node give the intended
argument through underived restriction/direct-image composition, derivation,
conjugation, and fully faithful restriction. It mentions no exchange or push
comparison and is a strictly smaller pullback-coherence assertion.
This is a decomposition: one original hole closed, one cube hole left, net zero.
The assigned item and repaired right module each already have zero holes in the
returned sandbox. H10 closes zero of zero holes and adds zero split statements.
Across all six retained modules, the one existing cube hole remains.

## No longer needed

Removed all four duplicate helper declarations from the left adjunct module. It imports
and applies the right module's public finite-to-Qbar counit identity.

Removed the plain import of `Sheaf.Paper.CondensedBaseChangeCounit`; that module is
omitted because `boundedConstructibleBaseChange_adjunct` supplies its exact identity.
Its node now attaches to the existing source theorem. The new source counit API and
its private mate-expansion helpers are no longer added by this delivery.

The original proof imports `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`,
`Sheaf.Paper.CondensedFlatCoefficientCalculus`, and
`Sheaf.Paper.ProfinitePointPullback` are removed. The public import
`Sheaf.Paper.CondensedQbarComparisons` remains. The former direct proof dependencies
`lem-weil-pbc-condensed-flat-coefficient-calculus` and
`lem-weil-pbc-profinite-point-pullback` are replaced by the normalizations and cube.
No claim is made that those modules are unused elsewhere. The adjunction-mate,
Qbar coefficient-comparison and condensed-category definitions remain used transitively.
All five old direct proof_deps edges are replaced by the two normalization nodes:
`def-weil-pbc-adjunction-mate`, `def-weil-pbc-qbar-condensed-comparisons`,
`lem-weil-pbc-condensed-flat-coefficient-calculus`, `lem-weil-pbc-profinite-point-pullback`,
and `def-weil-pbc-condensed-e-module-category`. The three definition nodes remain used
transitively; the two former proof lemmas are not used by the new proof. No unit statement
or realized unit step is bypassed.

A source import-graph comparison against the current shared repository confirms that
`Sheaf.Paper.CondensedFlatCoefficientCalculus` and
`Sheaf.Paper.CondensedCoefficientComparisons` leave the TargetsCheck import closure.
Their nodes are `lem-weil-pbc-condensed-flat-coefficient-calculus` and
`def-weil-pbc-condensed-coefficient-comparisons`. Neither module contains a hole.
ContinuousCoefficientUniverse and ProfinitePointPullback remain reached elsewhere.
The pruning is from the targets' closure; no source file is deleted.

## Where the brief, the DAG or earlier work was wrong

The returned attempt proved four helper statements twice. They are now retained once
or generalized once and reused through a normal import, as the return requests.
No theorem is renamed to hide a duplicate.

The prior delivery carried an old MorphismDefs snapshot which would overwrite
concurrent source improvements. The repaired snapshot preserves every current source
declaration and makes only the body-exposure adjustment. The old counit module is
redundant with the source's new adjunct API and is omitted from the repaired delivery.

The retained second-reading report described the returned revision and has been removed.
A fresh independent reader must assess the H10 repair. No target statement or mathematical construction changes;
no compiler limit is raised and no kernel check is disabled.

## New nodes

`lem-weil-pbc-qbar-condensed-exchange-left-adjunct` and
`lem-weil-pbc-qbar-condensed-exchange-right-adjunct` record the proved normalizations.
Their dependencies record the shared edge identity rather than duplicate proofs.

`lem-weil-pbc-qbar-condensed-push-counit` records the proved generalized
`lifted_push_counit` theorem in the right module. It combines iterated mate cancellation,
the mate counit equation and fully faithful restriction for arbitrary categories and
four full subcategories. Both finite-to-Qbar edge calculations specialize it. Identity
functors reduce to the adjunction triangle equations, and zero objects satisfy the same
naturality equations. No new hole is introduced by this node.

`lem-weil-pbc-qbar-condensed-pullback-cube` is the existing remaining hole. It applies
to any commutative square and input in C_E(Y), requires neither properness nor
Cartesianity, and inverts only pullback comparisons. Identity squares reduce to unit
coherence and zero objects to uniqueness of zero morphisms.

`lem-weil-pbc-condensed-basechange-counit` is reattached to the existing
`boundedConstructibleBaseChange_adjunct` theorem in MorphismDefs. Its duplicate module
is omitted. The source body-exposure adjustment and its users are recorded in
`coord/changes/condensed-pullback-square-interface.md`.

## Forced adaptations

`Sheaf.Paper.BoundedExchangeAmbient` is unclaimed in the shared checkout. Its original
fails against the adjusted MorphismDefs at original line 163:

```text
Type mismatch: (transportedCompositeIso_eq ... hB).symm
has type
  (boundedConstructibleUpperStarComp ...).symm ≪≫ eqToIso hB ≪≫
    boundedConstructibleUpperStarComp ... = transportedCompositeIso ...
but is expected to have type
  boundedConstructiblePullbackSquareComparison ... = transportedCompositeIso ...
The following definitions were not unfolded because their definition is not exposed:
  boundedConstructiblePullbackSquareComparison
```

The only changed line is the added proof-only import at new line 11:

```lean
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
```

It gives the existing proof access to the hidden comparison body. The original public
import, every signature, every proof and all visibility are preserved. No other
consumer is adapted.

## Second reading by A3

Independent reading of the six retained modules and their DAG records, including the
H10 repair, against the current shared source on 2026-10-16.

1. **Statements and definitions: pass.** Diffed every delivered module against the
   shared repository. The equality theorem's signature and docstring are unchanged.
   MorphismDefs differs only by `@[no_expose]` on the unchanged square-comparison
   definition; BoundedExchangeAmbient differs only by its plain `import all`.
   The declaration-table comparison reports no existing signature changes, additions,
   or removals. Compared the right module with the saved returned H10 revision:
   the appended premise-index command preserves every theorem and proof. The change
   records describe both exposure and index effects. No target meaning changes,
   hollow definitions, arbitrary witness choices, or mathematical data changes occur.

2. **Proofs and compilation: pass, with the declared cube hole.** Independently ran
   `lcompile.py --all` with its unchanged 60-second per-file limit. All six modules
   exported without warnings: right adjunct 23.2s, cube 25.2s, MorphismDefs 4.9s,
   BoundedExchangeAmbient 11.6s, left adjunct 41.8s, equality 27.6s. Read the generic
   mate cancellation, restricted counit formula, both naturality lifts, the path
   calculation, both normalizations, and injectivity argument. The only direct
   `sorry` is `constructibleToQbar_pullback_cube`. There are no forbidden declarations
   or kernel-check bypasses. Scratch `#print axioms` probes show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from open dependencies; the generic
   `lifted_push_counit` uses only the three allowed axioms. Recompiled the original
   BoundedExchangeAmbient against the delivered overlay and reproduced its line-163
   hidden-body error; its one-line proof import repairs exactly that failure.
   Lean 4.33.1's LibrarySuggestions/Basic.lean documents `nameDenyListExt.addEntry`;
   SymbolFrequency and SineQuaNon consult this filter before indexing theorem types.
   The H10 command excludes precisely the named component from suggestions and does
   not alter type checking, theorem visibility, or explicit applications.

3. **Split statements and duplication: pass.** The remaining cube has the actual
   coefficient and geometric comparison maps, allows every commutative square, and
   requires no exchange or push comparison. Its two paths have the same endpoints.
   Identity squares reduce to unit coherence and zero objects to the unique map.
   Its source and complete word proof accompany the named theorem and matching node.
   Independently searched with new LeanFinder, Loogle, and Mathlib grep queries,
   and searched both library roots for pullback-composition and cube identities.
   The hits give generic mate identities and underived sheaf coherence, rather than
   this bounded derived Qbar cube. The existing integral composition module proves
   a generic private `derived_pull_comp`; its integral specialization is already
   proved and is reused as the model, not duplicated. Inspected the saved bounded
   specialization experiments and their timeout/typeclass failures: completing this
   conversion is not a short missing rewrite. The cube is a strict pullback-coherence
   part of the argument, not a renamed exchange equality. All other new statements
   are proved; the shared counit calculation occurs once.

4. **Route and pruning: pass.** The equality applies inverse-adjunction injectivity
   to the two actual adjunct normalizations. The right normalization uses naturality
   and the mate counit equation; the left additionally uses the smaller cube and the
   source's existing `boundedConstructibleBaseChange_adjunct`. Public imports supply
   signatures; all extra proof imports are plain. Every old direct proof dependency
   is accounted for under No longer needed. An independent source-import closure
   comparison confirms exactly CondensedFlatCoefficientCalculus and
   CondensedCoefficientComparisons are pruned from TargetsCheck. Read the unit's
   `realized` record: none of these removed nodes realizes a unit statement or step,
   and the unit route is retained. This delivery closes one original hole and adds
   one cube hole: a decomposition, with net zero holes closed. The H10 repair itself
   adds and closes no holes.

5. **DAG and records: pass after documentation refresh.** The equality's two edges,
   the left normalization's cube/counit edges, the right normalization's shared
   counit edge, and the generic counit proof agree with the Lean. The cube's node
   records its intended composition-coherence proof and verbatim Lean signature.
   The five new nodes carry the required source, searches, origin, creation, unit,
   chapter, blueprint and Lean fields. The base-change counit node attaches to the
   existing source theorem, with no duplicate module. Re-ran downstream.py and
   inspected all five existing textual consumers of the hidden definition.

Second-reading changes: refreshed the exposure change record's downstream table to
124 current/sandbox users, including 21 newly landed users, and refreshed claim
holders. Gave the H10 record its declaration heading and an explicit consumer table.
Added this reader's three independent searches to the cube node. Added this review
and its verification evidence. No Lean proof, statement, definition body, or import
was changed by this reading. The six-module export run verifies the assigned H10
repair. Required dry run and delivery follow this review.
