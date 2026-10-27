## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.enlarged_chart_ringed_morphism` in
`lean/Sheaf/AlgebraicGeometry/EnlargedChartRingedMorphism.lean`, without changing its
statement, the four existing definitions, or any public import. All added helpers are
private and proved. No other existing Lean module is changed.

The normalization isomorphisms lift through fully faithful ring restriction. Conjugating
by these lifts reduces the arbitrary-normalization predicate to the existing canonical
structural-map predicate; full faithfulness of forgetting commutativity then supplies the
unique commutative-ring map. Finite-limit preservation is proved using the inclusion in
the ambient sheaf slice and its comparison with `Over.pullback`. Covering preservation
is proved by lifting field-valued sections across the actual sheaf pullback square.
Continuity reuses the existing `enlargedBaseChange_continuous` theorem.

For the ringed morphism, the actual sheaf pullback is left exact by representable
flatness and exact filtered colimits of sets. The existing sectionwise coefficient
ULift and the proved `siteContinuousRingedTopos` construction give the ringed-topos
record, with its ring map pinned to the prescribed adjoint transpose. The final geometric
morphism is the explicit transport through the scheme-restriction equivalences.
The construction is accessed by a proof-only `import all`; its existing private
implementation is reused unchanged, with independently sized site universes.

Added proof-only imports for scheme density, this generic construction, ambient slice
pullback, flatness, exact filtered colimits of sets, and finite limits from terminal
objects and pullbacks. Updated the item node's proof, proof dependencies, proof origin,
and obsolete top-level tool approvals to describe this route. Added three DAG attachments
to declarations that already exist; no new Lean module or declaration is introduced.

Validation: the complete Lean file compiled cleanly in 16.0 seconds, with no warnings.
The final delivery checks also compile the packet. The argument includes empty covering
families without assuming a witness exists, uses no surjectivity hypothesis on f, and
uses only categorical isomorphism cancellation, so zero rings and identity morphisms
need no additional hypotheses. No shared interface is changed; no forced adaptations
or change records are needed. The unit's statement and realized route are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AlgebraicSpace.enlarged_chart_ringed_morphism`
(node `lem-trf-space-enlarged-chart-ringed-morphism`).

Original item holes: 1. Closed: 1. Added: 0. Split off: 0. Left in the item: 0.
Every added private theorem is proved; no definition contains `sorry`.

This is a proof from existing declared dependencies, not an assertion that the entire
transitive import closure is now axiom-free. In particular,
`AlgebraicGeometry.AlgebraicSpace.enlargedStructuralMap_existsUnique`,
`AlgebraicGeometry.AlgebraicSpace.enlargedBaseChange_continuous`,
`AlgebraicGeometry.AlgebraicSpace.enlargedSite_scheme_density`, and
`AlgebraicGeometry.AlgebraicSpace.chartwise_etale_permanence` retain their existing
holes in unchanged modules. The first two receive individual DAG attachments in this
packet. Their holes predate this delivery; none is added or moved by it.

## No longer needed

Removed the proof-only imports `Sheaf.CategoryTheory.SiteInverseImageTensor` and
`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`. The direct flat-functor argument
supplies left exactness, and the existing explicit ringed-topos construction supplies
transposition. Accordingly removed the item's two obsolete top-level `tool_uses`:
`lem-weil-pbc-left-exact-site-inverse-image-tensor` and
`lem-weil-pbc-adjunction-lifts-group-ring-objects`.

These two nodes are no longer direct proof dependencies. The updated direct proof list
also omits `lem-trf-space-fibre-products-etale-covers`,
`lem-trf-space-enlarged-atlas-algebraic-extension`, `def-trf-geometric-morphism`,
`def-pc-scheme`, and `def-weil-pbc-ringed-topos-morphism`: existing canonical
constructions supply the atlas argument, and the imported categorical API supplies
finite limits, adjunction transport, and the ringed record. Scheme, geometric-morphism,
and ringed-topos definitions remain in the unchanged statement dependencies where needed.
Atlas and fibre-product results remain necessary to existing dependencies; this packet
does not claim that any of these modules is globally unused or withdraw any module.
Public imports are preserved. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The plan repeated the atlas construction even though
`enlargedStructuralMap_existsUnique` already states its canonical case. Normalization
transport gives a shorter proof for arbitrary RX and RY.

The ancestor node `lem-trf-space-enlarged-etale-ringed-site-model` bundles the canonical
structural-map theorem and continuity theorem while depending on this item. Citing that
ancestor as a proof dependency would create an artificial cycle. The new individual
attachments expose precisely those existing subresults with their own proofs and lower
dependencies. They do not duplicate any Lean declaration or replace the assigned theorem
by a renamed version. The canonical case omits the arbitrary-normalization, finite-limit,
covering, ringed-topos, transpose, and small-topos conclusions; continuity is only the
site-theoretic clause. The combining proof is complete Lean in the assigned module.

## New nodes

`lem-trf-space-canonical-enlarged-structural-map` attaches the existing, unchanged
`AlgebraicGeometry.AlgebraicSpace.enlargedStructuralMap_existsUnique` in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`. Its source is Stacks 03G8/03H7;
its proof uses atlas equalizers, common refinements, and fully faithful ring restriction.
This is a metadata attachment with `existing: true`, not a new split-off hole.

`lem-trf-space-enlarged-base-change-continuous` attaches the existing, unchanged
`AlgebraicGeometry.AlgebraicSpace.enlargedBaseChange_continuous` in that same module.
Its source is Stacks 03G2(1); covering-pullback preservation proves sheaf continuity.
This likewise introduces no Lean declaration or hole.

`def-trf-continuous-ringed-topos-construction` attaches the existing proved private
`SheafOfModules.RingedPresentationOnSites.siteContinuousRingedTopos` in
`Sheaf.CategoryTheory.RingedPullbackPresentationOnSites`. It records the concrete
continuous ringed-topos construction with a specified adjoint transpose and module
direct image, from Stacks 00YV/03D7. The enclosing section's independent site sizes and
adjunction parameters remain unchanged. This is an existing construction, not an axiom
or a new existence theorem. No change record is needed.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
