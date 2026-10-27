## What changed

Proved `restriction_tensor_chain_square` from the normalized coefficient transport,
the ordinary pullback mate, and the canonical ordinary tensor comparisons. No
existing public declaration signature or definition body changes.

`Sheaf.Paper.ProEtaleCoefficientOrdinaryTensorSquare` proves the ordinary square.
Its private helpers compute the mate on unit sections, compare both routes on
pure tensors, invert the resulting square, and express the comparisons in the
complex and bifunctor presentations used by the totalization theorem. It privately imports the existing
mate and pure-section proof APIs.

`Sheaf.Algebra.Homology.TensorTotalComparisonSquare` proves the passage from an
ordinary bifunctor square to signed direct-sum total complexes. Its hypotheses
are the ordinary square and the three summand formulas. The item supplies these
formulas and specializes the theorem to module sheaves.

After profiling and local transparency improvements, the combined file still
exceeded 60 seconds. `Sheaf.Paper.ProEtaleCoefficientTensorIsoNaturality` holds the existing
`tensorIso_naturality` theorem, and `Sheaf.Paper.ProEtaleCoefficientTensorIso`
holds the existing `tensorIso` definition. Both keep their original signatures;
the definition body is unchanged. Naturality uses
the generic total-bifunctor map formula. Its proved `tensorIso_summand` API
avoids unfolding the large definition in the final specialization. The item
publicly imports this supporting module, preserving all previous exports.
All transparency attributes are local. No shared definition is made irreducible.
The change record is `coord/changes/c1-coefficient-tensor-iso-packaging.md`.
The direct importer needs a proof elaboration improvement, described below.
The item node now records the proof and the relocated declarations have their
own definition node. The additional supporting module
`Sheaf.Paper.ProEtaleTensorRepresentativeNormalization` exposes proved equations
for the existing selected canonical comparison and tensor representative. The
consumer uses these APIs with local irreducibility of the selected comparisons;
its node records that dependency.

Validation: `lcompile.py --all` accepted all seven files without warnings,
including the required direct-importer check against the complete packet.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.CoefficientTensorChain.restriction_tensor_chain_square`
(node `lem-pbc-coefficient-restriction-tensor-chain-square`). The existing
`restriction_tensor_localized_square` proof now uses that proved chain square.

The supporting modules also completely prove:

- `AlgebraicGeometry.Scheme.CoefficientTensorChain.ordinary_square`
  (`lem-pbc-coefficient-restriction-ordinary-tensor-square`);
- `HomologicalComplex.mapTotalBifunctor` and
  `HomologicalComplex.tensorTotalComparisonSquare`
  (`lem-pbc-tensor-total-comparison-square`);
- `AlgebraicGeometry.Scheme.CoefficientTensorChain.tensorIso_summand`
  (`def-pbc-coefficient-restriction-tensor-iso`).

Also proved
`AlgebraicGeometry.Scheme.CoefficientTensorTransport.canonical_tensor_representative`
and `AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensor_representative_naturality`
(`lem-pbc-canonical-tensor-representative-normalization`).

One original hole closed, zero holes added, zero remaining across all seven
modules, including the adapted consumer. No unproved split-off statements. The proof uses existing library
results whose proofs are outside this item, as permitted by the dependency
contract.

## No longer needed

Removed the planned direct proof dependency
`lem-weil-pbc-independent-sheaf-tensor-colimits`: restriction along the coefficient
isomorphism is an equivalence and therefore preserves the total-degree coproducts.
Its module remains a transitive dependency of existing tensor constructions.
No module is withdrawn.

The item also no longer directly cites `def-pur-sheaf-tensor-product` or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` as proof steps: the pure-section
API and signed-total definition supply the formulas used here. Both remain
transitive dependencies. The ring-sheaf-change adjunction remains needed in the
ordinary supporting module.

Removed the item's private
`import all Sheaf.Paper.RingedTopoiCanonicalTensorPullback`: the proved generic
`mapTotalBifunctor` API supplies the total-map formula needed for naturality.
The source module remains a transitive dependency of existing constructions.
No derived representative-descent, K-flatness or flatness result is needed for
the chain square.

## Where the brief, the DAG or earlier work was wrong

The planned independent tensor-colimit lemma is unnecessary: the functor at the
coproduct-extensionality step is scalar restriction, an equivalence. The statement
and the unit route are unchanged. The proof uses universal properties and
normalization identities, covering zero rings, zero complexes, empty sites and
the identity coefficient isomorphism.

## Forced adaptations

`Sheaf.Paper.ProEtaleCoefficientTensorRepresentativeSquare` is unclaimed.
Its original source failed the required direct-importer check with:
`NOT ACCEPTED: this compile took 64 s > 60 s, the limit for one file`.
The body of its private `paste_tensor_square` helper is inlined at its sole call,
and the unused helper is removed. The two compared expressions are morphisms
instead of whole natural transformations, and the representative arrows have
explicit source and target types. The canonical representative normalization
and representative naturality calculations are factored into the new proved API
module, allowing local irreducibility of `proEtaleCanonicalTensorComparison` and
`proEtaleTensorPullbackTotalIso`. All transparency changes remain local. This avoids its expensive specialization to
the large geometric tensor comparisons. The same naturality and square equations
are composed in the same order. No signature, visibility, public import or global
attribute changes. No mathematics or proof route is changed in this consumer.

## New nodes

`lem-pbc-coefficient-restriction-ordinary-tensor-square` records the proved
module-level square. It is strictly below the item: there are no complexes,
differentials, signed totals or coproducts. The item uses it termwise.

`lem-pbc-tensor-total-comparison-square` records the proved coproduct passage
for additive functors and specified zero-preserving bifunctors. It assumes the
ordinary square and the three summand formulas, and proves compatibility on
total complexes. It contains no geometry, adjunction or pure-tensor calculation.

`def-pbc-coefficient-restriction-tensor-iso` records the existing normalized
isomorphism relocated to its supporting module and its proved summand API.
It chooses no new data; the definition body and normalization are unchanged.
The relocation is documented in
`coord/changes/c1-coefficient-tensor-iso-packaging.md`.

`lem-pbc-coefficient-restriction-tensor-iso-naturality` records the already proved
naturality declaration moved to its own supporting module. It translates the
uncurried total-functor map into the tensor of chain maps and applies the supplied
normalization data. It introduces no new obligation or data.

`lem-pbc-canonical-tensor-representative-normalization` records the fully proved
specification of the existing selected canonical comparison and naturality of
the supplied tensor representative. It constructs no isomorphism or arbitrary
witness. It is used by the required consumer adaptation to avoid unfolding large
comparison definitions repeatedly.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
