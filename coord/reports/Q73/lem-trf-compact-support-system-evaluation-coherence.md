## Worker report

This repairs the independent review of immutable head `eb4f71c3af40`. The saved packet's initial `deliver2.py --no-push` passed mechanically as `5b74e4f33d`; rereading the source and Lean confirmed that its arbitrary transition families and geometric functors still failed the mathematical review. They have been replaced, not merely re-pushed.

The theorem module now states existence of a canonical presentation together with its evaluation witness. The theorem assumes only the prime, finite coefficient extension, three invertibility Facts, an open immersion `j`, and an unrestricted morphism `p`. There is no assumed `D` with arbitrary operations or assumed transition compatibility. The presentation, its normalization equations, and the witness are supplied in the conclusion. The presentation contains only comparison maps; all four unit/counit equations are separate witness conclusions, not fields of an assumed adjunction-evaluation datum. All definitions have concrete data; only the main theorem has `sorry`.

### Repair of each returned point

1. **Actual source and target transitions (H6/H3).** There are no `sourceTransition` or `targetTransition` fields. `compactSupportConstantTowerTransition` descends the actual natural transformation obtained by evaluating `(homOfLE h).op` in the ordinary `ℕᵒᵖ` tower. `compactSupportSystemSourceTransition` evaluates it on the actual `U_Y S_p J_j M`. `compactSupportSystemExtensionTransition` defines precisely `Rp_n(t^N) ∘ b`, with `N = IntegralOpenReduction.J ... M` and `t^N` the scalar-adjunction adjunct of `coefficientSequenceDerivedTransition` on this real system. `compactSupportSystemTargetTransition` is `Res_m` of its transpose, followed by the canonical composition of restrictions and the recorded open-evaluation identifications. The conjunct labelled `transition_compatibility` equates these two fixed maps through `theta` for every system, every pair of indices, and every derived object.

   The previous report's claim that identity/cocycle axioms excluded artificially zero transitions was false. Those axioms did not identify the transitions at all. The repaired definitions have no independently selectable transition maps. Actual systems with zero transitions remain valid inputs and use their real transitions.

2. **Canonical geometric operations (H3/H4).** The system direct image is literally `(integralComparisonSequenceDirectImage l E p).rightDerivedFunctor`, not a field and not the derived functor of an arbitrary functor. The finite direct image is the right derived functor of `Scheme.coefficientProEtaleModuleDirectImage p` at the actual quotient coefficient ring. The system pullback is `integralComparisonDerivedSequencePullback p`; the finite pullback is the corresponding `coefficientProEtaleModulePullback p`. The system and finite open functors are the concrete `IntegralOpenReduction.J`, `.P`, `.finiteExtension`, and `.finiteRestriction`. The derived adjunctions descend the actual ordinary adjunctions. No functor can be substituted while keeping the presentation's type.

   The coefficient comparison is normalized by its identity on every ordinary section and by `CompactSupportDerivedSquareNormalization` on every K-injective resolution. `compactSupportSystemCoefficientMate` is a named construction using `mateEquiv`, rather than an independently supplied map. The finite scalar adjunctions use the existing quotient-extension and restriction functors. The target transpose uses the same adjunctions as this mate and as `t^N`.

3. **Unit and counit conclusions (H3).** `CompactSupportSystemEvaluationWitness` explicitly concludes the four conjuncts labelled `j_unit`, `j_counit`, `p_unit`, and `p_counit` in the file. These equations use the actual system and finite adjunctions, and the component evaluation maps whose composite is `theta`. The conjunct labelled `theta_canonical` fixes that composite to `compactSupportSystemEvaluationIso`. The existence theorem supplies the entire presentation and witness, including these equations; they are not assumptions on a universally quantified datum.

### Hypothesis and clause correspondence

- A prime ℓ and finite extension E/ℚ_ℓ are `l`, `[Fact l.Prime]`, `[Field E]`, `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]`. Quotient rings and their actual coefficient sheaves come from the recorded coefficient definitions. The standard index `n : ℕ` denotes exponent `n+1`, so all positive levels are present.
- The site/size convention is `Scheme.{t}` with independent coefficient universe `u`, the small `Scheme.ProEt` site, and module size `max u (t+1)`. No equality of universes is imposed.
- The three invertibility hypotheses are exactly the three stalkwise `Fact` binders. The geometric hypotheses are `[IsOpenImmersion j]` and the unrestricted `p : Z ⟶ Y`.
- Ordinary strict systems and their unbounded derived category are `coefficientSequenceModules` and `coefficientSequenceDerived`. Evaluation and actual derived transitions are `coefficientSequenceDerivedEvaluation` and `coefficientSequenceDerivedTransition`.
- Exact open extension and whole-system direct image are the canonical functors named above. K-injective and additive presentation fields are supplied existentially in the conclusion; there is no added resolution hypothesis on an input object or on its evaluated components.
- `U_Y` is `coefficientSequenceDerivedRestriction`; its evaluation is `coefficientConstantTowerEvaluation`. The source functor is `compactSupportSystemSourceLevel`.
- `T_n` is `compactSupportSystemTargetLevel`, the recorded finite open extension followed by the actual finite derived direct image and `coefficientFiniteDerivedRestriction`.
- The displayed extension-form composite, scalar transpose, completed restriction, and composition `Res_m Res_(m,n) = Res_n` are the named definitions `compactSupportSystemExtensionTransition`, `compactSupportSystemTargetTransition`, and `compactSupportSystemRestrictionComp`. The latter uses the existing `coefficientRestrictionComp` equality.
- The canonical `Theta` is `compactSupportSystemEvaluationIso`: `coefficientRestrictedEvaluationIso`, then the normalized direct-image evaluation, then the localized `IntegralOpenReduction.extensionEvaluation`. The witness supplies natural isomorphisms equal to this composite.
- The `transition_compatibility` conjunct is the whole-tower equation at every pair of levels. The source maps are actual maps of a strict tower, so this equation gives a whole-tower isomorphism. Naturality in every derived morphism is built into the natural isomorphisms, not restricted to maps of complexes.
- The four unit/counit equations are explicit witness conclusions. No limit or completed-limit functor appears in the construction. For compiler performance, the identical unit and counit equations are named `CompactSupportUnitEvaluation` and `CompactSupportCounitEvaluation`, applied separately to the actual open and direct-image adjunctions. Each predicate quantifies over every object and is written out in the theorem module. The two specialized square-normalization predicates likewise supply the named exactness instances explicitly and assert the same arbitrary-resolution equation.

### Dependencies used

- `Sheaf.Paper.CoefficientRingedSequenceSite`: actual sequence categories, evaluations, `coefficientSequenceDerivedTransition`, completed restriction, `coefficientRestrictedEvaluationIso`, and finite scalar restriction.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearSections.AdjunctionEvaluation` and the ordinary-system evaluation/mate calculus.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`: `integralComparisonSequenceDirectImage`, `integralComparisonDerivedSequencePullback`, and the canonical ordinary adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`: actual finite `coefficientProEtaleModuleDirectImage`, `coefficientProEtaleModulePullback`, and their adjunction, retaining independent universes.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`: `IntegralOpenReduction.Operations`, `J`, `P`, `finiteExtension`, `finiteRestriction`, `systemAdjunction`, and `extensionEvaluation`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`: actual finite quotient extension and `coefficientRestrictionComp`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`: `Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
- Mathlib: `IsOpenImmersion`, `mateEquiv`, `Localization.liftNatTrans`, natural isomorphisms, ordinary cochain complexes, and standard unbounded derived localizations.

The new evaluation-diagram definition node cites these already-recorded dependencies and reuses their interfaces. The theorem cites that new node. No dependency module or mathematical statement correction is required.

### Edge cases

The equal-index map is the actual identity tower arrow, not an arbitrary field. Every pair `n ≤ m` is included. The zero input and actual zero-transition systems are allowed; no cartesianness or invertibility of transition adjoints is assumed. Identity `j` and `p` use the same ordinary canonical adjunctions, and the empty open and empty schemes are allowed. No properness, quasi-compactness, quotient-flatness, boundedness, or assumption that evaluation preserves K-injectives is introduced. The normalization equations allow arbitrary K-injective resolutions of evaluated complexes. Every construction is made before any inverse limit.

### Searches

The original packet's three kinds of searches are retained in the node. Repair searches additionally used:

- LeanFinder, query “canonical evaluation of derived direct image on coefficient systems compatible with actual inverse tower transitions and coefficient adjunction mates”: eight unrelated Kaehler/cotangent-map hits; no statement match.
- Loogle, query `CategoryTheory.mateEquiv, CategoryTheory.Localization.liftNatTrans, CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`: no hits; the last project identifier is unknown to the Mathlib search service. The exact project declaration was read directly.
- Mathlib grep, query `compactSupportSystemEvaluation|derived.*[Ee]valuation.*[Cc]oherence` under `CategoryTheory`: no hits.
- `rg` on the source `WeilConjectures` for the item id: no existing declaration. Targeted `rg` on repository `lean/Sheaf` found the canonical direct-image, quotient-transition, and open-operation interfaces listed above; these are reused rather than privately reconstructed.

No `STATEMENT-DISPUTED` issue was found. The informal node's statement is unchanged; this delivery repairs its Lean rendering.

## Second reading by Q73

I reread the informal node, all six proof steps, the current blueprint clause (3), the dependency signatures, and both repaired modules and the new definition node. The review checks the three returned faults separately: transition maps are definitions on the actual tower and actual coefficient adjunct; geometric functors are fixed by `j` and `p`; and unit/counit equations are conclusions. The saved packet's zero-transition argument was rejected and removed. I also checked the mate direction: the ordinary/derived restriction square has domain `Res_Z ⋙ Rp_m` and codomain `Rp_n ⋙ Res_Y`; its inverse `mateEquiv` image has domain `Rp_m ⋙ tensor_Y` and codomain `tensor_Z ⋙ Rp_n`, exactly the displayed `b`. The source transition has direction `m → n` because evaluation uses `(homOfLE h).op`. Naturality is for all derived morphisms because `theta` is a family of natural isomorphisms. The positive-level convention, independent universes, empty open, identities, unbounded inputs, and arbitrary input transitions are preserved. This is a self-check in the single-worker repair session; no second agent was started.

## New nodes

`def-trf-compact-support-system-evaluation-diagram`, in the same chapter, owns
`Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram`. It defines the actual
level and whole-system functors, their inherited adjunctions, a presentation of
their evaluation maps, the K-injective square-normalization predicate, the
canonical comparison composite, and the two specified transition maps. This is
the missing definition of the diagram on which the item's coherence statement
is made. Separating definitions from the theorem also keeps each file within
the prescribed compile limit. It introduces no replacement of existing
coefficient, system, sheaf, geometric, or derived-category definitions.

Its primary declaration is `CompactSupportSystemEvaluationData`; every named
helper is listed in its `lean.declarations`. The class's four comparison fields
are `jLeftEvaluation`, `jRightEvaluation`, `pLeftEvaluation`, and
`pRightEvaluation`. They have the actual functors as endpoints. The node states
these fields, the source and target definitions, the mate direction, the
restriction composition, and the full resolution-normalization equation.
There is no theorem or postponed proof in this definition module.

New-node searches used LeanSearch and LeanFinder for the compact-support
evaluation diagram with actual tower transitions and adjunction mates, and
Mathlib grep under CategoryTheory for
`compactSupportSystem|[Ee]valuation[Dd]iagram|[Cc]ompact[Ss]upport.*[Tt]ransition`.
LeanSearch returned generic scalar adjunctions, evaluation adjunctions and adic
completion evaluation; LeanFinder returned generic double complexes and adic
evaluation; grep had no hit. The exact returned search records are retained in
the new node. DAG search and `blueprint_refs.py search 'compact support'` found
no matching definition. Project grep found `compactSupportRestrictedTransition`
and `sfCompactSupportTransition`; their full signatures start from a
completed-coefficient input and a compactification, unlike the arbitrary strict
quotient systems and unrestricted p here. They are not substituted.
`blueprint_refs.py ancestor` returned `thm-trf-l-function-euler-product`.
All new statement/proof dependency paths were checked for a path back to the
item; there is none. The definition-node citations exactly match its
`stmt_deps`, and only its id is added to the item's `stmt_deps`.

The final witness is a subtype of the family of natural isomorphisms: its value is theta and its property is the conjunction of the displayed normalization, transition, and four adjunction equations. This replaces Lean-generated structure projections, whose repeated dependent checking timed out, with exactly the same data and clauses; it adds no premise and removes no conclusion. The comment labels in the subtype identify each clause for review.

## Resumed-packet self-check (2026-10-18)

The required initial dry run of the saved packet failed: the diagram compiled,
but the theorem module exceeded 60 seconds locally and on the server. A temporary
profiler run localized this to a deterministic kernel timeout while checking
`CompactSupportSystemEvaluationWitness`; the two normalization definitions were
quick. Profiling was removed after diagnosis.

The two section-normalization clauses, the transition clause, and each of the
four adjunction compatibility clauses are now named predicates in the same
theorem module, listed in `lean.declarations`. The witness's corresponding
conjuncts invoke these predicates. Each predicate contains the original full
equation, with every functor endpoint explicit in the adjunction clauses. This
factors the large dependent check without introducing another module, another
geometric operation, an assumption on the input, or a postponed proof. The
ordinary coefficient-square identity uses `HEq`, as does the adjacent ordinary
direct-image identity: the section carriers are definitionally the same, so
this is still the identity on the same sections. The finite functor definitions
retain the saved packet's abbreviations and exact bodies.

The resumed self-check compared the retained returned source with this packet:
the old arbitrary transition fields and geometric functors are absent. Actual
tower evaluation and the specified mate/transpose define the two transitions;
all four adjunction equations remain conclusions. The informal item is unchanged,
and its only added statement dependency is the new evaluation-diagram definition.

Factoring isolated the kernel timeout to the ordinary coefficient-square
section normalization. That predicate is now heterogeneous equality of the
whole underlying section function with the identity function on the actual
section carrier of `N`. Function equality is precisely identity on every
section. The input type of the comparison function is inferred from its actual
module-sheaf map, so the kernel does not repeatedly unfold the direct image and
restriction merely to check an explicitly typed argument `x`. No transition or
adjunction clause is altered.

Validation: `scompile.py Q73 lem-trf-compact-support-system-evaluation-coherence`
with both delivered modules exited 0, with no errors or warnings. The diagram's
checks were 14.3--49.7 seconds and the theorem module's sandbox/library checks
were 26.4 and 8.7 seconds, all under the unchanged 60-second per-file limit.
The final self-check confirms both primary `lean.statement` signatures verbatim,
no overlong Lean lines, no unbound universes/variables, concrete data in every
definition, and exactly the requested main theorem as the sole `sorry`.

The subsequent delivery dry run compiled both modules, then reported that the
current DAG ancestry contains one additional `blueprint.from.via` entry,
`lem-trf-rational-global-frobenius-powers`. The new definition node's ancestry
was updated exactly to the current preflight diagnostic. No statement changed.
