## What changed

Proved `AlgebraicGeometry.ProEtale.ModuleRingedComparison.internal_oplax_resolving_components`
without changing its statement or any of the existing definitions. Private proved helpers
identify the acyclic tensor test with homotopy K-flatness, preserve the resolving class under
the actual internal pullback, compute both derived comparison counits, and invert naturality
squares. The tensor component identity is the source library's existing
`Functor.leftDerivedTensorComparison_app_app_comp_counit`, since `internalDelta` is defined
as that comparison. Its mate monoidal instance is first identified with the canonical
one by the existing proved `internalPullOplax_eq_canonical` normalization. The regular-unit clause uses the stated K-flat section comparison.
The specified unit equation is obtained by expanding the two existing constructions.

The DAG proof now follows this direct internal argument. Local irreducibility settings
prevent expansion of the large monoidal, localization, homotopy-functor and derived-functor
bundles. The new generic proofs use transparency-respecting matching, and the naturality
square applications check their map hypotheses separately. Profiling options were removed
before delivery. The complete proof compiled in 48.7 seconds during profiling; delivery
rechecks the final file. Added the private proof import
`WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence` and
`import all Sheaf.Paper.ProEtaleSectionModuleFunctors` for its proved private normalization
lemma. No public signature or public import changes, no source-library edits, no new data choices, and no change record is required.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.internal_oplax_resolving_components`
(node `lem-pd-internal-oplax-resolving-components`).

No holes remain in the item. Zero holes added; zero split-off statements. The proof still
uses the regular-unit clause of the existing theorem
`KFlatSectionComparison.section_kflat_tensor_comparison`, whose hole belongs to its own item.

## No longer needed

The following former proof imports and corresponding proof dependencies are unnecessary
for this proof:

- `Sheaf.Paper.SectionDerivedPushpullNormalization`
  (`lem-pd-section-derived-pushpull-normalization`): compute the internal counit directly
  using the source library's generic K-flat counit theorem.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
  (`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`): use the actual internal inverse image
  and scalar-extension equivalence to preserve K-flatness.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
  (`lem-sfb-internal-module-operations-transport`): no internal/section transport is needed.
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
  (`lem-pur-kflat-total-tensor-model`): homotopy K-flat objects are already closed under tensor;
  flat terms of the tensor are not needed for the generic counit theorem.
- `Sheaf.Paper.DerivedPullbackRepresentativeComputation`
  (`lem-weil-pbc-kflat-tensor-pullback-computation-universes`): no section computation needed.
- `Sheaf.Paper.SectionOplaxTotalComparison`
  (`lem-pd-section-oplax-total-comparison`): the specified `internalDelta` already has its
  proved generic component equation, and the ordinary unit is explicit.
- `lem-weil-pbc-localization-universal-property`: no new lift or uniqueness argument is
  needed; use the existing derived comparison equation and the fact that Qh inverts
  quasi-isomorphisms.

Removed the four obsolete `tool_uses` entries for the ringed tensor pullback, internal
operations transport, K-flat total tensor model and universe-sensitive pullback computation
nodes listed above. All original public imports remain, since they provide the existing
statement interface.
These dependencies are pruned from this proof only; other consumers are unaffected.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The six-step DAG plan was longer than necessary: the imported
source library already proves the comparison equation for exactly the definition used by
`internalDelta`, and already provides K-flat counit invertibility. The replacement keeps
all clauses and the unit route. The inverse-square proof uses the actual functor images
and their `asIso` inverses. It imposes no nonzero-ring, nonempty-scheme, boundedness, or
coefficient-flatness assumptions. Every new helper is proved, including in the zero and
empty cases covered by its unchanged categorical hypotheses.

Searches used msearch LeanFinder, Loogle and grep, then direct searches of both library
roots and Mathlib. Read the existing declarations and the Stacks source at
`lemma-pullback-K-flat`, `lemma-tensor-product-K-flat` and
`lemma-pullback-tensor-product`. No new nodes.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
