## What changed

Replaced the hole in `SheafOfModules.StrictQuotientExchange.strictQuotientExchangeUnitEquation`
by an assembly through normalized strict coefficient projection, pullback-square,
evaluation and coaugmentation lemmas. The existing theorem and definition signatures
are unchanged. All additions are under `Sheaf.Paper`; no source-library files change.

The proved evaluation bridge additionally identifies the arbitrary normalized
tower adjunction with the library's canonical normalized one by localization
extensionality. Its counit comparison follows from normalization on K-injectives.
The pullback cube follows from the exact-functor cube theorem and the uniqueness
characterization of the ambient square, then mate transport gives the displayed
comparison. Thus evaluation is proved independently of all three remaining holes.

The categorical calculations are explicit: the exchange mate cube identifies the
projection conjugate with the tower mate; its second application proves the quotient
comparison from the given scalar square and counit equations. Cancellation removes
the two artificial inverses in gamma. The adjunct projection is natural, so gamma
is a composite natural transformation. Naturality of kappa and the single-edge
projection/coaugmentation equation give the final unit equation.

## Proved and sorry left

The original module had one hole, at
`SheafOfModules.StrictQuotientExchange.strictQuotientExchangeUnitEquation`.
Its body is complete relative to three remaining intermediate declarations. This
is a **decomposition**, not a net proof: one old hole closed and three holes added
(net -2). The fourth new result,
`SheafOfModules.StrictQuotientExchange.strictTowerMateEvaluation`, is proved in
this delivery, including adjunction uniqueness, counit normalization, the exact
pullback/evaluation cube, and the final comparison diagram. It has zero holes.
No hole is inside a definition or a private helper.

The cleaned main theorem compiled without warnings in 50.5 seconds. The second
delivery check compiled all five modules cleanly. The item retains a local
elaboration heartbeat budget for naturality; the 60-second wall-clock compile
limit remains unchanged. Preflight requested a change record for the local
elaboration attributes; this packet includes that record. The axiom checks
are performed by the delivery tool.

The added holes are:

- `SheafOfModules.StrictQuotientExchange.strictPerfectTowerProjection`,
  node `lem-sbc-strict-perfect-tower-projection`.
- `SheafOfModules.StrictQuotientExchange.strictReductionPullbackSquare`,
  node `lem-sbc-strict-reduction-pullback-square`.
- `SheafOfModules.StrictQuotientExchange.strictProjectionCoaugmentation`,
  node `lem-sbc-strict-projection-coaugmentation`.

The new statements were checked on identity edges, zero coefficient complexes,
zero input objects and arbitrary augmentations. Evaluation and the coaugmentation
bridge impose no perfectness or invertibility of exchange. The perfect projection
bridge permits different local bounds and ranks at every level. None detects
equality of strict derived tower maps merely by their evaluated components.

## No longer needed

The quotient comparison no longer uses
`lem-pur-diagram-ring-restriction-pushforward` or
`lem-sfb-ringed-comparison-tensor-adjunction`: the supplied `QuotientComparisons`
already contains the exact counit and inverse-image square equations needed by
the mate cube. Removed those obsolete top-level tool approvals from the item's
node; no new approval was added.

Removed the following unused private proof imports from the item:

- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.RingedComparisonTensorAdjunction`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Mathlib.CategoryTheory.Adjunction.Mates` (available through the mate-cube import)
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedStrictTowerProjectionMorphism`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The first of these remains a private proof import of the proved evaluation bridge,
where its proved Grothendieck instance is used. Other geometric dependencies remain
in the proposed proofs of the remaining bridges or in unchanged public imports.
The private import of `RingedTowerPushforwardLimitComparison` is retained to
preserve the blueprint unit route. No upstream declaration or library module is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The numbered plan is mathematically sound, but its intermediate declarations do
not directly state the normalized formulas for `Reduction`, `PullReduction` and
`TowerAdjunction`. Those records were introduced as part of the recent strict
coefficient interface. The four bridge lemmas make these steps explicit. The
existing augmented-diagram projection theorem only covers algebra sheaves in
degree zero, whereas this item permits arbitrary augmented complexes.

The quotient clause is simpler than its original plan: no construction or
uniqueness theorem for scalar comparisons is necessary when proving a statement
universally quantified over already normalized comparison data.

The unit `sk-rem-rest` route remains unchanged. The generic tools
`lem-weil-pbc-exchange-mate-cube`,
`lem-fix-site-open-exchange-localization`, and
`lem-weil-pbc-ringed-square-tensor-compatibility` serve the explicit adjunction,
evaluation-cube and tensor representative calculations. The unit has no substitute
for these general categorical tools; they do not replace its geometric route.
Their use is for independent review, with no worker-added `tool_uses` approvals.

## New nodes

`lem-sbc-strict-perfect-tower-projection` is the single-edge levelwise perfect
projection result. It includes preservation of local perfectness needed to apply
the projection result at h after pulling coefficients along f.

`lem-sbc-strict-reduction-pullback-square` states the inverse-image coefficient
square before taking any mate, evaluation or inverse limit.

`lem-sbc-strict-tower-mate-evaluation` is the compatibility of the actual square
mate with normalized evaluation. It is proved in this delivery and requires
neither perfect coefficients nor isomorphic structural ring maps.

`lem-sbc-strict-projection-coaugmentation` is the single-edge projection/unit
identity after derived inverse limit. It requires no perfectness and inverts no
projection or augmentation.

Each has its own Lean module, source, complete proof in words and DAG attachment.
Change record: `coord/changes/strict-quotient-exchange-elaboration.md`. It records
the local elaboration attributes flagged by preflight; no existing statement or
definition body changed.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
