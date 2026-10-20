## What changed

The item now proves
`SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique`,
`SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit`,
`CategoryTheory.CochainPullback.ringedPullbackPresentation_exists`, and
`CategoryTheory.CochainPullback.compositePresentation_exists`, with
unchanged signatures and independent site/coefficient universes.

The first constructs scalar insertion and a normalized tensorator, and independently
proves uniqueness on sectionwise scalar-extension generators. Its two new supporting
modules `CochainInverseComparison` and `CochainTensoratorExistence` are fully proved:
the algebraic inverse-image comparison uses the set adjunction restricted to linear
and balanced bilinear maps, and scalar extension uses sectionwise tensor adjunctions
and module sheafification. No auxiliary theorem is left unproved.

The new supporting module `CochainModuleAdjunction` proves the inverse-image module
adjunction by restricting the natural underlying Hom equivalence to linear maps.
Composing with the scalar-extension adjunction supplies the item’s presentation;
left-adjoint preservation of coproducts and zero proves its additivity.

`moduleUnit` keeps its original `Classical.choose` body verbatim. Local
transparency settings allow the explicit coefficient unit and unique-existence
predicate to elaborate. The earlier `.exists` projection has been removed, so
consumers using the original `Classical.choose_spec` formula retain that exact
choice. The local elaboration change is recorded in
`coord/changes/B9-cochain-module-unit-projection.md`.

The unit is constructed from the regular module, inverse-image scalar action and
scalar-extension adjunction. The regular-module linear equivalence uses the
specified underlying inverse directly. Its forward hom formula is definitional;
no inverse selected from a bijectivity proof needs to reduce. Its normalization is checked on generalized pure
tensors, and its uniqueness follows from the right-unitor equation.

The composite proof constructs the transported ring and module structures, then
bundles the composite coefficient map from the addition, multiplication and one
graph laws. A second supporting theorem compares the scalar extensions through
their Hom equivalences. The comparison sends each insertion generator to the
twice-inserted generator. Adjunction conjugation supplies the module right-adjoint
comparison; the set right-adjoint comparison is the identity. Both new supporting
modules are fully proved.

Reusing the existing generic geometric module construction and linear-map
transport removes approximately 950 lines of duplicated helpers. The resumed
check removed development profiler settings and diagnostic heartbeat caps from
`CochainCompositeAlgebraic` and `CochainCompositeHom`. Both compile cleanly
with the normal heartbeat budget (19.9 and 18.5 seconds respectively).
The main module reuses the scalar-construction pure tensor and insertion wrappers,
and its extensionality lemma, instead of duplicating their sheafification proof.
The unit calculation evaluates its Hom-equivalence equality at a section; explicit
scalar-action data keep elaboration from expanding the chosen unit isomorphism.
The complete item module builds its compiled artifact cleanly in 51.8 seconds
within the unchanged 60-second limit. Its direct consumer
`CochainCoefficientArrows` compiles unchanged in 24.1 seconds. After the next
green build published its dependency, the unchanged higher consumers
`CochainComparisonMonoidalEquations` and `CochainPullbackTensorCoherence` also
compile against the new artifact, in 31.0 and 29.2 seconds respectively.
No consumer source is changed. The composite assembly packages
its normalized left comparison through a proved private conjugation lemma,
avoiding repeated reduction of the constructed presentation. All four original theorem proofs and all five supporting
modules are complete.

## Proved and sorry left

Original item holes: 4. Original holes closed: 4. Holes added: 0. Net: 4.

Closed:

- `SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique`.
- `CategoryTheory.CochainPullback.ringedPullbackPresentation_exists`.
- `SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit`.
- `CategoryTheory.CochainPullback.compositePresentation_exists`.

All four realize node `def-pur-cochain-tensor-coherence-data`.

The supporting theorems `normalizedTensorator_exists`,
`exists_inverseImageTensorComparison` and `inverseImageModuleAdjunction_exists`
are proved, including all private helpers and construction laws.

No `sorry` remains in any delivered Lean file. There are no holes in definitions
or private declarations and no split-off holes. The two additional supporting
theorems `compositeAlgebraicImage_exists` and
`normalizedScalarComposition_exists` are proved in full.

## No longer needed

No existing public imports, modules or target-reachable dependencies are pruned.
The private `oneSection`, `unitMap` and `unitMap_apply` bridge is unnecessary:
the regular-module linear equivalence is constructed directly from the given
underlying isomorphism and the rank-one action formula.
The original definition node had no proof dependencies; its updated proof records
the tensorator, independent uniqueness, module/scalar adjunction assembly and
normalized composition.
The shared-universe landed comparison remains imported for `ofLanded`.

The new proofs do not import the shared-universe geometric tensor comparison,
which cannot instantiate the independent site sizes here. The new supporting
modules reuse the generic private APIs in `GeometricModuleConstruction` and
`GeometricModuleTransport`, plus the algebraic inverse-image and sheaf-tensor APIs.
Exploratory imports of `RingedSiteModules`, Mathlib’s `Sheaf.ChangeOfRings`,
`Adjunction.Mates`, `Sites.Equivalence`, `Adjunction.Basic` and
`Limits.Preserves.Finite` were removed from the new modules when unused.
The unused direct private import of `CochainInverseComparison` was removed from
the item; `CochainTensoratorExistence` still needs its proved tensor comparison.
No target-reachable pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original definition node had an empty proof plan. The updated steps record
the actual construction, and all new supporting nodes are proved. The retained
report’s claim that an inverse-image comparison remained unproved was stale:
that full Hom/Bilin argument has now been implemented.

The retained local irreducibility setting blocked the explicit unit projection.
Local transparency repairs elaboration while preserving the original definition
body. A newly landed consumer, `CochainComparisonMonoidalEquations`, reads the
original choice predicate directly, so the temporary `.exists` projection was
withdrawn before delivery.

Zero rings, zero modules and degenerate sites are included. No flatness, nonzero,
point or faithfulness hypothesis has been added. The unit’s route is retained.

The retained composite helper files contained development profiler settings and
10,000-heartbeat diagnostic caps. The latter produced a deterministic heartbeat
failure in the final algebraic-composition declaration; removing the diagnostic
settings restored clean compiles. No launcher code, limits or gates were changed.
The final composite assembly also required named `RingedPullback` fields: its
implicit additivity field makes the retained positional constructor incorrect.

## New nodes

`lem-pur-independent-ringed-tensorator-existence` records the proved normalized
ordinary tensorator, combining the proved inverse-image and scalar comparisons.

`lem-pur-independent-inverse-image-tensor-comparison` records the proved tensor
preservation of the specified algebraic inverse-image lift. Its proof transposes
linear and bilinear operation graphs through the underlying adjunction, then
applies the sheaf tensor universal property.

`lem-pur-independent-module-adjunction` records the proved inverse-image module
adjunction. It is the linear-map part of the source adjunction argument used for
the ringed module presentation, with independent site universes.

Change record: `coord/changes/B9-cochain-module-unit-projection.md`.

`lem-pur-independent-composite-algebraic-image` records the proved construction of
the algebraic inverse image and coefficient map for the composed set functor.
Finite-product transport checks the ring/module operations; the two coefficient
graph laws compose and give the required ring-sheaf morphism.

`lem-pur-independent-normalized-scalar-composition` records the proved natural
isomorphism of composite scalar extensions, with its value on all insertion
generators. Its Hom equivalence identifies linear maps through the composed
underlying adjunction; bijectivity proves the inverse identities and naturality.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
