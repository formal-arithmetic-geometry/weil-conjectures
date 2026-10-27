## What changed

`Sheaf.Paper.ConstructibleResidueTree` now contains a complete Lean proof of
`WeilConjectures.constructible_residue_tree` from the existing refinement, completeness
and finite-model declarations, and one new finite-reduction comparison. Its statement
and public imports are unchanged. All helpers are private and proved.

The proof appends the constructibility stratifications of the finitely many residue
homology sheaves to the input partitions. It reindexes this finite family, applies
`exists_finite_open_closed_refinement`, and retains its scheme-theoretic leaf
factorizations. A common interval is the minimum of the two lower bounds and the
maximum of the two upper bounds. Local constancy with finite geometric stalks supplies
finite constant module models on every stratum. Pullback composition carries these
models to any weakly etale object of a nonempty leaf. Exact pullback transports the
vanishing outside the interval and gives finite zero models there.

For completeness, the projection-normalized coefficient maps identify the two
ordinary pullback presentations by uniqueness of adjoints and derived functors.
`ordinaryCompositeCompletionUnit_isIso` applies directly to a weakly etale map followed
by the leaf immersion. The completion-unit criterion therefore gives completeness
without a separate induction down the tree. An auxiliary prime greater than l supplies
only the finite-field parameter of the legacy-completeness presentation; no hypothesis
on W is added.

The new module `Sheaf.Paper.OrdinaryIntegralReductionHomology` isolates the ordinary
integral pullback/finite-reduction homology comparison. It has no tree, finite support,
constructibility or completeness claim. It is used to identify the desired residue
homology with exact finite-coefficient pullback of the original residue homology.

The item compiled successfully in 18.2 seconds during the final proof check; the
new comparison module compiled successfully in 41.7 seconds. Profiling options were
removed for delivery. Static checks confirm the original theorem signature and public
imports are unchanged, the new node's Lean statement matches verbatim, all dependencies
have nodes, and neither the import graph nor the proof-dependency graph has a cycle
through this item. The delivery tool performs the final packet checks.

## Proved and sorry left

Closed the original hole `WeilConjectures.constructible_residue_tree`
(`lem-fix-constructible-residue-tree`). The item module has zero literal sorries.
Added one hole: `WeilConjectures.ordinaryIntegralReductionHomology`
(`lem-fix-ordinary-integral-reduction-homology`), in its own new module.
This is a decomposition: one upper hole closed and one strictly smaller hole added,
not a claim of a net hole reduction. The combination proving the original tree,
completeness, interval and finite-model assertions is complete Lean.

The remaining comparison is true for arbitrary scheme maps and positive finite
quotient exponents: choose a flat-term K-flat representative, use the coefficient
projection square and tensor associativity, compute both derived scalar extensions
with their counits, then use exactness of constant-coefficient inverse image.
The docstring and node give this argument. Its zero object, empty scheme and exponent
one cases follow from the same tensor formulas, with no nonemptiness assumption.

## No longer needed

The planned direct dependency `lem-fix-qcqs-completion-unit-locality`
(`Sheaf.Paper.QcqsCompletionUnitLocality`) is replaced by the sharper
`lem-fix-qcqs-completion-unit-restriction` and the completion-unit criterion.
The wrapper and its tree induction are not used or imported, even transitively, by
this proof. No unit statement or
unit proof step is bypassed: the item's unit record has no realized declarations.
No existing Lean module is withdrawn.

The finite-model argument uses the existing constant-scalar constructibility
comparison and fixed-module finite local models directly. It lifts their isomorphisms
through fully faithful restriction to constant scalars, retaining the finite model.
This avoids a detour through `Sheaf.Paper.ProEtaleFiniteUnderlyingModels` and
`Sheaf.Paper.ProEtaleFiniteActionLocalModels`; neither is imported, even transitively, by this proof.
All original public imports are retained. The supplied local-constancy hypothesis is
unnecessary for this route because the finite constructibility stratifications are
appended explicitly; its binder is preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

The original step 3 says finite scalar reduction commutes with ordinary restrictions,
but none of its cited declarations states that comparison for the specified
`ordinaryIntegralDerivedPull` and `scalarReductionDerivedExtension`. The existing
`NormalizedIntegralPullbackTower` supplies an underived strict-tower comparison;
`ProEtaleConstantModulePullbackHomology` supplies exact finite-coefficient homology.
The descent connecting those two constructions is the new, smaller remaining step.
The original completeness plan's induction can be replaced by the already stated
comparison on the composite weakly etale/immersion map. No statement repair is needed.

## New nodes

`lem-fix-ordinary-integral-reduction-homology`, attached to
`WeilConjectures.ordinaryIntegralReductionHomology` in
`lean/Sheaf/Paper/OrdinaryIntegralReductionHomology.lean`, is the finite-reduction part
of the original node's third step. Its proof plan uses the existing ordinary derived
pullback construction, K-flat resolutions, scalar-extension counits, normalized
pullback tower comparison and exact constant-coefficient homology. The original node's
proof and proof dependencies now describe the Lean argument. No change record is
required: no other existing module, statement, definition or interface changes.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
