## What changed

Completed `Sheaf.Paper.ProEtaleSectionModuleFunctors` and restored the previously
attached `Sheaf.Algebra.Category.ModuleCat.Sheaf.FinalRingedUnitMate` companion
source removed by the shared rollback. No new mathematical statement or hole is
introduced.
The tensor mate proof compares the normalized internal and section direct-image
pairings on pure tensors, transports adjuncts using the specified unit equation,
and cancels the existing tensor and pullback comparison isomorphisms. Essential
surjectivity and naturality give invertibility for arbitrary section modules.
No flatness, boundedness or finiteness assumption is added.

Retained the valid normalization and unit-mate proofs from the C4 source present
when this session started. The shared source was rolled back during this session;
this packet also preserves the original private `upperStar_tensorπ_delta` and
`tensorπ_natural` interfaces used by `SectionOrdinaryOplaxNormalization`. Their
proofs reuse the abstract tensor projection calculations in TraceBaseChangeFirst.
The restored companion preserves its existing public signature and node
`lem-pd-final-ringed-unit-mate-isiso`; its complete proof compares the specified
adjunct with Mathlib’s final-site regular-unit map via uniqueness of left adjoints.

The normalized pairing predicate `PushNormalized` now names the existing ringed
pure-tensor predicate, definitionally the same formula. Its owning module is imported
publicly because the definition refers to it. A change record documents this
representation change and its consumers. All actual chosen ordinary and total
comparison isomorphisms, coefficient maps, functors and adjunctions are unchanged.
The total-comparison uniqueness proposition binds the same equivalence functor
and its induced complex functor by local lets, and supplies the existing totalization
proofs explicitly. Zeta reduction and proof irrelevance give the original proposition; its
normalization and the chosen comparison map are unchanged. All other public
declaration names and signature text match the current shared source. Private
abstract calculations, compact coproduct proofs and local transparency settings
avoid unfolding large concrete monoidal structures. The totalization
proofs use existing coproducts and their preservation, supplied explicitly to avoid
matching concrete coefficient, site and equivalence-image expressions. The assembly
and tensor-mate DAG proofs now record the route used in Lean.

The restored companion compiled in 5.4 seconds. The unchanged
`SectionOrdinaryOplaxNormalization` was
checked against the sandbox artifact without any Lean errors; its 68.5-second
run exceeded the single-file limit, so no accepted consumer compile is claimed.
No consumer source is delivered or adapted.

## Proved and sorry left

Closed, against the current shared source:

- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.pushNormalized_existsUnique`
  (`lem-pd-section-push-normalized-exists-unique`): existing ringed pairing theorem.
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.pull_delta_isIso`
  (`lem-pd-section-pull-delta-isiso`): normalized pairing and mate transport.
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.pull_eta_isIso`
  (`lem-pd-section-pull-eta-isiso`): existing final-site normalized unit theorem.

Three current holes closed; zero remain; zero added; zero split off. The restored
`SheafOfModules.normalized_unit_mate_isIso` companion is also fully proved. At session
start only the tensor hole remained; the other two proofs were already in C4's
source and were removed by the subsequent shared rollback. They are credited here
explicitly as restored existing proofs rather than new mathematical work by K9.

## No longer needed

For `lem-pd-section-pull-delta-isiso`, these planned direct dependencies are unused:

- `det-pe-topos-functoriality-inverse-image`
- `lem-sp-proetale-algebraic-inverse-image`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `lem-weil-pbc-scalar-extension-hom`
- `def-weil-presheaf-modules-sheafification`
- `lem-weil-pbc-geometric-module-transport`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-pd-ringed-tensor-adjunction-mate`

The existing strong internal pullback and the fixed equivalences replace a new
presheaf scalar-extension construction and its adjunction comparison. Removed
obsolete top-level tool approvals for geometric inverse image, algebraic inverse
image, module adjunction, scalar Hom, geometric module transport, and the
conjugate-iso unit equation; retained the mate-formula approval. No claim is made
that these modules can be removed from the whole target closure. No source-library
declaration or module is withdrawn. The old private `mapMod_tensorπ_delta`,
`counit_underlying`, and `sectionPureTensor_hom_ext` are no longer used; repository
search found no external consumer of those declarations. The two externally used
private tensor lemmas are retained.

## Where the brief, the DAG or earlier work was wrong

The original tensor-mate plan was valid but unnecessarily reconstructs a scalar
extension presentation. The existing internal strong pullback already supplies
the invertible mate; the missing argument was compatibility of the normalized
pairings with the specified adjunction transport. The proof retains the unit's
Verdier-exchange route and all target statements.

The C4 rollback restored three holes, removed the proved unit-mate companion’s
source while retaining its DAG attachment, and exposed downstream uses of two
private lemmas omitted by that landing. This packet preserves those interfaces rather
than changing their consumer. The representation-only predicate change is
recorded in `coord/changes/K9-section-push-normalization.md`; the equal private
canonical pairing is documented in `coord/changes/K9-internal-normalized-pairing.md`. The definitionally equal
total-comparison proposition is documented in
`coord/changes/K9-total-comparison-functor-alias.md`.
Target semantic review is reopened for PushNormalized, with no mathematical meaning changed.

## Reviewer corrections (2026-10-26)

- The delivery imported `Sheaf.Paper.TraceBaseChangeFirst` into the item (`import all`).
  Through `import all` of the item, its global instance
  `CondensedRing.condensedUpperStarMonoidal` reaches `Sheaf.Paper.InternalOplaxResolvingComponents`.
  There it competes with `CondensedRing.monoidal_upperStar`, and that importer fails
  (lines 365, 369 and 377). The reviewer restored the published internal part of the module:
  `canonicalInternalPush`, `canonical_projection`, `upperStar_tensorπ_delta`,
  `tensorπ_natural`, `internalPull_*` and `internalPull_preservesFlat`, together with their
  imports (`Sheaf.Paper.InverseImageModuleFlat` again, no TraceBaseChangeFirst).
  The section-module part, the three closed holes, `PushNormalized` and
  `totalComparison_existsUnique` are kept as delivered.
  The change record `K9-internal-normalized-pairing.md` is withdrawn.
  Step 6 and `proof_deps` of node `def-pd-proetale-section-module-functors` are restored
  to the published flatness route.
- `total_preserves` was a `private instance (priority := 4000)`, which is still a global
  instance in every importer. It is now a `private theorem` with
  `attribute [local instance 4000]`.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
