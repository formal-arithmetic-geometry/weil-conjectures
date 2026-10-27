## What changed

Replaced the hole in `WeilConjectures.IntegralOnSlice.qcqsOrdinaryQuotientRestriction`
by a strict tower assembly from normalized comparisons for a single quotient of a
module sheaf. The original public signature and public import remain verbatim.
All helpers in the item are private and proved.

`quotientLevelIso` applies the module comparison degreewise. Its naturality proves
that it respects differentials and chain maps. `quotientLevelIso_transition`
transposes the adjacent-level square through `ordinaryAdjunction` and applies the
pure-tensor extensionality supplied by the fixed scalar-extension model. Naturality of the adjunction unit, the
existing transition generator formula, and finite constant-map naturality then
prove the square. `quotientTowerIso` assembles these squares with
`NatTrans.ofOpSequence` and proves invertibility componentwise.
`quotientLevelIso_augmentation` proves the required augmentation equation by
transposing through the same adjunction and evaluating on generators. The only
remaining coefficient calculation is preservation of one by the finite ring map.

Added `Sheaf.Paper.OrdinaryQuotientModuleComparison`, containing the real composite
`ordinaryQuotientModule` and one remaining theorem about a single finite quotient
of module sheaves. It assumes invertibility of the specified completed coefficient
map, which the item obtains from the existing `qcqsOrdinaryRestrictionExact`.
It has no complex, transition or tower conclusion. Its normalization determines
the comparison uniquely; no definition chooses arbitrary data from a bare
existence theorem. The remaining theorem has a source and complete proof in words.

Proof imports are private. `import all IntegralReductionTowerUnrestricted` exposes
the scalar-extension generator extensionality used by `quotientModule_hom_ext`.
Finite constant-map naturality is proved locally from the sheafification adjunction.
Local irreducibility attributes keep `ordinaryPull` and `reductionWitness` folded;
transparency protection remains enabled. No other existing module or node was changed. The new node inherits the item's chapter, unit and
blueprint ancestry. The unit's realized statement and step lists are empty, and
the unit route is unchanged.

Validation: both modules compiled remotely: the finite-module comparison in
47.1 seconds, and the final assembly in 43.1 seconds with profiling enabled.
Profiling and temporary warning options were removed for delivery. Axiom inspection
of `ordinaryQuotientModule` and the augmentation helper showed only `propext`,
`Classical.choice` and `Quot.sound`. The public theorem signature was compared
verbatim with the repository version, and both node dependency unions were checked.
The delivery tool runs the final compile and preflight checks.

## Proved and sorry left

Original holes: one. The direct hole of
`WeilConjectures.IntegralOnSlice.qcqsOrdinaryQuotientRestriction`
(node `lem-fix-qcqs-ordinary-quotient-restriction`) is closed in the item.

Added holes: one, the entire public theorem
`WeilConjectures.IntegralOnSlice.ordinaryQuotientModuleComparison`
(node `lem-fix-ordinary-quotient-module-comparison`). There are no other new holes.
This is a decomposition: one upper hole closed, one strictly smaller finite-module
hole added. It is not a net sorry reduction. The existing exactness theorem is
an unchanged dependency, not a newly added hole.

The finite-module statement includes n=0 (exponent one), zero modules and the empty
scheme. It adds no boundedness, completeness, nonemptiness or flatness hypothesis
to the item. The proofs of every strict transition, of naturality in complexes,
and of the augmentation equation are in the item rather than assumed in the new
statement.

## No longer needed

No original import was removed and no module is withdrawn.
`lem-weil-pbc-reduction-pullback-derived-tower`
(`Sheaf.Paper.ReductionPullbackDerivedTower`) is removed from this node's direct
proof dependencies: the statement concerns ordinary complexes, and the derived
reduction theorem does not identify the fixed ordinary models. The argument uses
the single-module tensor comparison and proves the strict assembly itself.

`prop-weil-pbc-proetale-constant-ring-map` is no longer a direct proof dependency of
the item; its finite coefficient identification belongs to the new finite-module
node, which retains it. `lem-fix-qcqs-ordinary-restriction-exact` and
`def-pur-integral-derived-operations` remain direct dependencies. The finite ring-map square is proved locally by applying the defining
sheafification adjunction to the constant-section maps and evaluating their
naturality at the finite quotient transition. No claim is made that a removed direct dependency leaves every target's
existing import closure.

## Where the brief, the DAG or earlier work was wrong

The listed derived reduction/pullback theorem is a theorem about derived tensor
models and does not itself provide the ordinary comparison with the fixed
completed-module action and adjunction-unit normalization. The existing
`NormalizedIntegralPullbackTower` identifies reduction after ordinary pullback
with finite-coefficient pullback after reduction; it does not assert pullback
after restriction of a finite module to completed coefficients. The remaining
single-module theorem isolates this coefficient-action step.

The original generator/transition argument is followed. Its strict-tower and
augmentation parts are now Lean proofs. No statement was disputed or weakened,
no existing definition was changed, and no source-library declaration was removed.

## New nodes

`lem-fix-ordinary-quotient-module-comparison`, in
`dag/nodes/sec-six-functors/lem-fix-ordinary-quotient-module-comparison.json`, realizes
the finite module tensor comparison of the original first proof step, before
complexes and strict towers. Its module is
`Sheaf.Paper.OrdinaryQuotientModuleComparison`. LeanSearch, LeanFinder, Loogle and
source grep found scalar-extension adjunction and pullback-composition APIs but
no direct match for the specified normalized comparison. A blueprint search found
no duplicate. The statement and proof explain the finite coefficient comparison,
the action square, the pure-tensor formula, inverse identities and uniqueness.
No change record is required because all new declarations are in a new module
and no existing interface changes.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
