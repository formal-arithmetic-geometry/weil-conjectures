## What changed

Restored the assigned archived module and proved
`AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionNormalization` without changing
its signature. Its own DAG node follows the direct proof. Repaired the representation
of `DirectImageRestrictionNormalized` in the unclaimed shared data module: its original
four conjuncts are now the four proof fields of a proposition structure, and its
representative field pins four local preadditive instances to the explicit projections
of `Mod.instAbelian`. The four conditions, canonical maps, binders and mathematical
meaning are preserved. The change record is
`coord/changes/V4-open-restriction-preadditive-projections.md`.
Added private proof imports of `ModuleDirectImageOpenPasting` and
`DerivedExchangeModuleTermwise`.

The canonical module-pasting witness gives the underived isomorphism and the sectionwise
formula after identifying its mate with the specified map. The general derived mate unit
identity, specialized to the actual module adjunctions, gives the representative equation by
cancelling evaluation and exact restriction isomorphisms. That equation proves invertibility
on K-injective representatives; naturality transports it to every derived object.

Validation: `lcompile.py` accepted the final data module and the complete item proof.
All five direct importers compiled against the repaired data: the item, associativity,
successive restriction, mixed restriction, and the derived coherence assembly. No
consumer adaptation was needed. The four unchanged test copies were removed before
delivery. The final delivered Lean sources contain no `sorry` or profiling settings.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionNormalization`
(node `lem-sfb-derived-open-restriction-normalization`). Added 0 holes; split off 0 statements.
There are no remaining `sorry` declarations in either delivered Lean module. The shared
data module has zero original holes and zero added holes.

## No longer needed

The declared proof dependency `lem-sfb-kinjective-direct-image-open-word-model`, module
`Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel`, is unnecessary for this proof.
Invertibility follows directly from the representative equation and the existing theorem
`DerivedCategory.exists_iso_Q_obj_of_isKInjective`; no finite-word cells, simultaneous
evaluation families or word-diagram descent are needed. Removed that dependency from this
node's proof plan. This does not withdraw the word-model module or assert that other parents
no longer need it.

The original module contained only its public data import, which is preserved. No existing
import was removed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item initially existed only in quarantine, as recorded in `coord/rework.tsv`; its archived
statement and attachment were preserved. During the session the shared source was restored
independently. Its original single proof step proposed finite-word descent to prove
invertibility, but the same result follows directly from its representative equation.

The section coprojections and fibre-product arrows in the data module and module-pasting
module have different helper names but the same constructions. The mate equations differ
only by taking the inverse of the composite square comparison and equality transport.
No mathematical statement correction was necessary. The native module preadditive
instance and its projection from the abelian structure caused a kernel conversion timeout.
Explicitly pinning the module instances inside the representative field and lemma,
and doing the invertibility argument with abstract categories, avoids that conversion.
The predicate is stored in a proposition structure to keep proof assembly from unfolding
the entire conjunction. Its constructor and four projections give logical equivalence
with the original conjunction. This definition repair reopens the affected target-meaning
review, as recorded in the change record.
No global instance priorities or source-library bodies are changed. Empty opens, identity
maps, arbitrary commutative condensed coefficients and unbounded K-injective complexes remain included.
The unit record `sk-cor-affine-space-rational` has no realized statement or proof step attached
to this auxiliary node, and its route is preserved.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
