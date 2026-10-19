## What changed

Proved `AlgebraicGeometry.exists_proetale_hypercover_single_affine` from the existing
finite-basis hypercover and qcqs geometry declarations, with its original signature.
The finite-product and singleton-cover clauses are proved separately. The geometric
clause now has a complete Lean proof: construct a formal w-contractible hypercover,
realize each finite family using the scheme and representable-sheaf coproduct mapping
properties, compare proper-face limits through sheaf realization, turn represented
matching epimorphisms into singleton covers, and replace the terms by literal spectra.
The final parent derives representable weak contractibility degreewise from
`Scheme.proetale_weakContractible_equivalences`.

The delivery contains eight Lean modules: the item, `FiniteProductWContractible`,
`SingleWContractibleCover`, `SingleAffineHypercover`, `FormalWContractibleHypercover`,
`FiniteCoproductWContractibleSpectrum`, `RepresentableEpiCover`, and
`HypercoverSpectrumReplacement`. Each new module has a matching DAG node. No existing
signature, definition, visibility, or consumer was changed; no change record is required.
The retained earlier report described an unfinished decomposition; this report replaces it.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_proetale_hypercover_single_affine`
(`det-pe-hypercover-existence`). Added zero holes; zero local sorries remain.
The previously retained geometric split is also proved in this delivery, so this is
not a delivery of an unresolved decomposition.

The seven additional proved public declarations are:

- `isWContractibleRing_pi_of_finite` (`det-pe-hypercover-product-wcontractible`).
- `exists_single_wContractible_affine_cover` (`det-pe-hypercover-single-cover`).
- `exists_single_affine_wContractible_hypercover` (`det-pe-hypercover-single-affine`).
- `exists_formal_wContractible_hypercover` (`det-pe-hypercover-formal-wcontractible`).
- `finite_coproduct_wContractible_spectrum`
  (`det-pe-hypercover-finite-coproduct-spectrum`).
- `AlgebraicGeometry.Scheme.ProEt.singleton_cover_of_representable_epi`
  (`det-pe-hypercover-representable-epi-cover`).
- `hypercover_spectrum_replacement` (`det-pe-hypercover-spectrum-replacement`).

These proofs use existing library declarations as permitted by stage 3; this does not
assert that their entire transitive dependency closure is already sorry-free.
Compilation and delivery validation are recorded by the delivery tool.

## No longer needed

Removed these direct proof imports from the original item:
`Sheaf.AlgebraicGeometry.WContractibleAffineCover`,
`Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`,
`Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`, and
`Sheaf.CategoryTheory.CoskeletonMatchingTuples`.
The qcqs geometry and finite-basis hypercover modules remain needed transitively.
`Sheaf.AlgebraicGeometry.WContractibleAffineCover` is absent from the delivered item's
transitive import closure: the proof applies the source ring-extension theorem directly
after obtaining an affine cover. `det-pe-wcb-cover` is not used by the new proof.
`lem-weil-pbc-coskeleton-matching-tuples` and its module are unnecessary on this route:
the conclusion records proper-face limiting cones directly. Removed its obsolete
approval from the parent node's `tool_uses` list.
Its proof dependency `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
(`lem-weil-pbc-truncated-coskeleton-finite-limits`) also leaves this item's import closure.
The three modules removed from that closure are exactly `WContractibleAffineCover`,
`CoskeletonMatchingTuples`, and `TruncatedCoskeletonFiniteLimits`; other library consumers
may still need them.

The finite-product proof uses Mathlib's prime-spectrum homeomorphism and evaluation
localization isomorphisms; it needs no scheme coproduct theorem or finite-affine
coproduct-spectrum node. The realization proof uses Mathlib `sigmaSpec` directly and
reuses the proved sheaf-realization helpers of
`Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry` through a proof-only
`import all`. The auxiliary formal-family terminal/pullback distribution lemmas,
finite-limits-from-terminal-pullbacks node, and affine-open-basis refinement argument
are not directly used by the new geometric proof. Their existing indirect use by
imported library modules is not claimed globally pruned.

Removed unused direct proof imports of `SiteFiniteBasisHypercoverExistence`,
`FiniteProductWContractible`, and `SingleWContractibleCover` from the geometric module;
they are used by its supporting modules. No entire original dependency module is
claimed globally pruned without checking other library consumers.

## Where the brief, the DAG or earlier work was wrong

The old geometric proof plan did not expose a convenient scheme realization functor.
The existing affine-hypercover geometry module already contains proved sheaf realization,
finite-limit preservation, proper-face matching comparison, finite proper-face categories,
and lowering of represented epimorphisms. The delivery reuses those proofs instead of
reproving that theory. Its node is used as a generic tool on the same finite-family
realization route, without replacing the unit's route. The represented local-lifting
node is likewise a generic tool to recognize actual singleton covers.

The final covering criterion explicitly uses a quasi-compact source and a
quasi-separated target. Matching targets are constructed in the qcqs slice before
inclusion in the full slice, ensuring that hypothesis; it is not inferred for arbitrary
finite limits over an arbitrary base. The singleton-cover clause retains only
quasi-compactness of its target. Finite-family indices are reindexed by
`ULift (Fin (Nat.card I))` to keep the product ring in the scheme universe.

Edge cases checked in the construction: empty finite product, empty families and base,
zero coordinate rings, arbitrary base scheme X, degree-zero empty proper-face diagram,
and degree-one product over U. No strengthened or weakened existing statement is used.

## New nodes

- `det-pe-hypercover-product-wcontractible`: finite products of w-contractible rings;
  proved by the spectrum sigma decomposition, evaluation localizations and extremal
  disconnectedness of the closed-point/component spaces.
- `det-pe-hypercover-single-cover`: single w-contractible spectrum covers; proved by
  composing the existing affine singleton cover with a faithfully flat ind-etale
  w-contractible coordinate-ring extension.
- `det-pe-hypercover-single-affine`: geometric simplicial hypercover clause; proved by
  the four strictly smaller constructions below and existing realization lemmas.
- `det-pe-hypercover-formal-wcontractible`: specialization of the existing finite-basis
  hypercover theorem to literal w-contractible spectra in the qcqs subsite.
- `det-pe-hypercover-finite-coproduct-spectrum`: finite coproduct spectrum representative;
  proved with universe reindexing, Mathlib `sigmaSpec`, and finite-product stability.
- `det-pe-hypercover-representable-epi-cover`: quasi-compact represented epimorphisms to
  quasi-separated objects are actual singleton pro-etale covers; proved using the
  existing represented local-lifting theorem and joint surjectivity on scheme points.
- `det-pe-hypercover-spectrum-replacement`: conjugates all simplicial operators by
  chosen spectrum isomorphisms and transports proper-face cones and singleton covers.

On resumption, checked the retained eight-module proof against the current source library.
Corrected the represented-epimorphism helper's source path for Tag 00WN to `sites.tex`,
removed unrelated statement dependencies from new nodes, and recorded the existing
finite-affine-coproduct spectrum Mathlib leaf used by the spectrum realization.
The singleton-cover node now cites `lem-weil-pbc-source-wcontractible-extension`,
which is attached to the actual source theorem `exists_isWContractibleRing`,
in place of the covering-family node `det-pe-wcb-cover`.

All seven nodes have complete proof terms, source/proof descriptions and statements.
No new node is left for a subsequent worker to prove.

The resumed dry run identified missing LeanSearch records on four new nodes. Ran the
four searches and recorded their actual results: they supply partial Mathlib tools
already used here, rather than a replacement for any of the four complete statements.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
