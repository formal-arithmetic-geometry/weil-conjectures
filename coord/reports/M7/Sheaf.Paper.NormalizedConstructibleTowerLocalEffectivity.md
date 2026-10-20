## What changed

Repair of reviewer C-2e50e, head 2e50e3069, H9: removed the unused proof
imports `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` and
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit` from
`Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation`. Its proof and node
dependencies are unchanged. `LisseNormalizedTowerLocalModels` retains its import
and the unit route. This repair adds and closes zero holes; the retained packet
still has the two named obligations listed below.

Repair verification on 2026-10-20: `lcompile.py --all` compiled all five retained
modules successfully (each within 23 seconds). `deliver3.py --no-push` passed
the server preflight with review class CODEX. Both removed imports remain in
`LisseNormalizedTowerLocalModels`, preserving the unit route.

Decomposed `AlgebraicGeometry.Scheme.normalizedConstructibleTower_local_effectivity`
without changing its signature or any definition. Its complete Lean proof applies
finite coefficient presentation at each quotient, obtains common lisse strata from
level zero, reconstructs each stratum, and packs the local models. The private
`inverse_normalization_square` proves inversion of the semilinear compatibility
square by cancellation of mapped isomorphisms.

Four new modules isolate the single-sheaf finite coefficient comparison, finite
coefficient derived presentation (step 1), common strata and nilpotent propagation
(steps 2--3), and local reconstruction (steps 4--7). The derived presentation is
proved from the single-sheaf comparison and existing fixed-module descent. Each
of the two remaining obligations has one public theorem proved by `sorry`, a
source, a detailed proof in words, and a matching node. These statements are strictly separate parts of the
argument; none repeats the full item or supplies its conclusion as a hypothesis.
The unit's route and all existing public signatures remain unchanged.

The following substeps were proved while continuing the split obligations:

- `finite_presentation_representative` extracts a cochain representative and its
  comparison with the given derived object. Its helpers `restrictCancelIso`,
  `coefficientEquivalence`, and `coefficientEquivalence_isEquivalence` construct
  scalar restriction along a coefficient-ring isomorphism explicitly.
- `common_constructible_stratification` gives a simultaneous finite refinement for
  any finite family of constructible fixed-ring etale sheaves. Its elementary
  helpers construct the identity stratification, refinement transitivity, and a
  finite common refinement. The empty indexing family is included.
- `exists_boundedFinite_model` truncates a pseudo-coherent finite-free model above
  b and below a. The top kernel is finite over the Noetherian ring; the bottom
  cokernel is finite. Neither boundary term is asserted projective.
- `map_roos`, `module_roos_epi`, and `module_derivedLimit_interval` prove the common
  cohomological bound directly in the module derived category. Countable products
  commute with homology; finite Mittag--Leffler makes the preceding Roos operator
  surjective; the long exact sequence embeds outside cohomology into a zero product.
- `exists_boundedFinite_normalizedTower` constructs the derived limit by a product
  triangle, applies the declared pseudo-coherent reconstruction theorem, proves its
  bound, and obtains a bounded finite representative and compatible reduction
  isomorphisms for every supplied family of reduction adjunctions.

The five delivery modules compile together through `lcompile.py --all`. No arbitrary
data are defined by choosing a witness of an unproved existence theorem. All helper
definitions are explicit constructions, and all private theorems are proved.

## Proved and sorry left

This is a decomposition. One upper hole is closed in Lean:
`AlgebraicGeometry.Scheme.normalizedConstructibleTower_local_effectivity`.
Zero of the original one hole is counted as fully proved; two holes are added:

- `AlgebraicGeometry.Scheme.normalizedTower_common_lisse_strata`
  (node `lem-weil-pbc-normalized-tower-common-lisse-strata`). The proved `native_common_strata` helper transports intrinsic
  constructibility to fixed scalars, applies the finite common refinement and
  lifts the local models to native coefficient modules on covering sieves.
  `relative_lisse_iff_native` proves the equivalence with the relative
  inverse-image coefficient predicate. What remains is the normalized
  small-site coefficient transport needed to apply nilpotent-reduction-lissity
  at all levels.
- `AlgebraicGeometry.Scheme.lisseNormalizedTower_local_models`
  (node `lem-weil-pbc-lisse-normalized-tower-local-models`). It still needs the
  coefficient and stalk adapters, compatible finite derived trivializations,
  transport of normalized derived objects along the proved completion quotient
  equivalences, and relative completed-constant realization. The normalized algebraic reconstruction,
  product-triangle construction, cohomological bound, and good truncation are
  proved in `exists_boundedFinite_normalizedTower` and its helpers. The caller
  proves inversion of the final normalization square.

The new theorem
`AlgebraicGeometry.Scheme.finiteCoefficient_constructibleDerived_origin_presentation`
is proved from `finiteCoefficient_intrinsic_constructible`, existing fixed-module
constructible descent, bounded cohomology descent, and explicit scalar transport.
Its helpers `intrinsic_constructible_of_iso` and `finite_etale_origin_realization`
are also proved. This closes one provisional split obligation without adding an
additional remaining hole.

`AlgebraicGeometry.Scheme.finiteCoefficient_intrinsic_constructible` is also proved.
The proof retains the underlying set sheaf under arbitrary coefficient presentation,
pulls back its finite constant models, and proves that a finite locally constant set
sheaf with a finite-ring module structure is locally a constant finite module. It
constructs these modules as the finite submodule generated by the restricted constant
sections after a common covering refinement makes addition, zero and scalar action
constant. Thus it does not need a locally constant ring-automorphism argument.

No sorry remains in the item, intrinsic-comparison or derived-presentation modules.
The two remaining obligation modules each contain exactly one named public
`:= by sorry`; the delivery has exactly two remaining holes and no holes inside
definitions or private helpers. The delivered net hole change is +1, so no positive
net proof progress is claimed.

## No longer needed

Removed from `Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation` for H9:

- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`

Neither import supplies a declaration used by this proved module. Their nodes
were already absent from its proof dependencies. The unit route remains through
`LisseNormalizedTowerLocalModels`, which retains the required import.

The following direct proof imports were removed from the item; the required theory is
retained in the corresponding intermediate modules and their proof dependencies:

- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `WeilConjectures.Topology.Stratification`
- `Sheaf.Paper.NilpotentReductionLissity`
- `Mathlib.RingTheory.Ideal.Quotient.Defs`
- `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`
- `Sheaf.Paper.CompatibleFiniteDerivedTrivializations`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.RingTheory.AdicCompletionNoetherianOfQuotient`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower`
- `Mathlib.RingTheory.Finiteness.Defs`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Sheaf.Paper.FiniteMittagLeffler`
- `Sheaf.CategoryTheory.Triangulated.MilnorSequence`
- `Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel`
- `Sheaf.Paper.CompletedConstantFiniteComplexRealization`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

Also removed the redundant direct proof import
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin` from
`Sheaf.Paper.LisseNormalizedTowerLocalModels`; its finite-origin input now comes
through `Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation`.

Also removed the unused exploratory imports
`Mathlib.CategoryTheory.Sites.Point.Skyscraper` and
`Mathlib.Algebra.Homology.ShortComplex.ShortExact` from the reconstruction module.
Its direct use of `lem-pc-derived-limit-milnor-sequence` was replaced by
`lem-weil-derived-limit-products-core`, `lem-pc-derived-limit-roos-abelian-groups`,
and the derived homology long exact sequence. The finite Mittag--Leffler theorem
still uses the generic derived-limit theory transitively.

Removed `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` from the
common-strata module: its required scalar-extension comparison follows from
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` by uniqueness of
left adjoints. The reconstruction module retains its tensor-theory dependency.

No dependency node or module is claimed globally pruned: this decomposition relocates
the proof-dependency imports below the four intermediate results. The original
tool-use approvals on the parent are withdrawn because its proof no longer directly
uses those generic tools; the local reconstruction node records their actual uses.

## Where the brief, the DAG or earlier work was wrong

The finite-ring origin theorem has B in Type u and the small intrinsic predicate;
the assigned tower has quotient rings in Type (u+1) and the relative coefficient
predicate. Applying that theorem is not a one-line specialization. The proved
finite-ring presentation instead uses the existing fixed-module derived origin
theorem directly in Type (u+1). Its single-sheaf intrinsic-constructibility
adapter is proved in this packet; no small-ring replacement is required. No statement was
weakened and no definition was changed. The local reconstruction API returns forward
isomorphisms and a forward square; their inverses satisfy the required local-model
square by the explicit Lean cancellation proof.

Edge cases checked mathematically: zero coefficient ring, zero complex and empty scheme
are allowed by the finite-ring equivalences; the common-strata theorem permits an
empty partition; an empty stratum has the empty covering sieve. The local first term
is a finite cokernel and is not assumed projective. The coefficients remain inverse
images of the completion on X throughout. The new claims add no finite Tor bound.

## New nodes

`lem-weil-pbc-finite-coefficient-derived-origin-presentation` isolates one finite ring
and one complex, with no normalized tower or common local model. It serves step 1.

`lem-weil-pbc-normalized-tower-common-lisse-strata` uses constructibility only at the
first positive quotient and produces only simultaneous lissity, with no local complex.
It serves steps 2--3.

`lem-weil-pbc-lisse-normalized-tower-local-models` starts on a single immersed lisse
stratum and produces forward realization isomorphisms. It neither constructs a global
stratification nor gives the finite-level origin conclusion. It serves steps 4--7.

The searches logged in searches.jsonl found no matching Mathlib result; blueprint
searches for normalized constructible and finite derived local found no duplicate.
`lem-weil-pbc-finite-coefficient-intrinsic-constructibility` isolates a single sheaf
and its finite constant local models, with no derived object, bound or tower. The
proved derived-presentation node now uses it and the existing fixed-module
constructible and bounded-derived origin nodes.

No change record is needed because all existing statements and definitions are unchanged.

Continuation verification: `lcompile.py --all` compiled all five delivery modules
successfully after the interrupted attempts. The initial continuation dry run reported
two split-off holes after 3 of its 120-minute reference clock. The original report
predated completion of the intrinsic-comparison proof and has been corrected above.
The retained `.budget` was not changed.

The completion-Noetherian dependency has moved in the current sources from
`Sheaf.RingTheory.AdicCompletionNoetherianOfQuotient` to
`WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient`; the reconstruction
module now imports its current source location. The theorem and its use are unchanged.
Additional proved helpers in the obligation modules identify the nilpotent image
of I in A/I^(n+1), its quotient-factor kernel and residue-ring equivalence, and
specialize the nilpotent-reduction theorem. Reconstruction helpers identify the
completion evaluation kernel, construct the canonical completion quotient ring
equivalences, and prove their compatibility with every quotient transition.
The common-strata module now contains proved canonical constant-ring and module
pullback comparisons for coefficients in Type (u+1), their slice comparisons,
and the conversion from finite scheme covers to covering-sieve models.
`native_constructible_fixed` and `native_common_strata` use these comparisons;
the older `fixedDerived_strata` helper and its duplicate coefficient-equivalence
helpers were removed. `pullbackScalarExtensionIso` derives the needed scalar
extension comparison by uniqueness of left adjoints from the existing canonical
derived direct-image comparison, so this module no longer needs the generic
ringed-topos tensor-comparison import. The reconstruction module also now contains
proved transport of universal normalization arrows under fully faithful functors
and coefficient equivalences. Additional scratch proofs of small-site encodings, scalar restriction compatibility,
the scalar-extension adjunction on an arbitrary small site, and scalar extension
transport through equivalences remain excluded from delivery and do not count as
closed obligations. Combining the generic encoding with this file exceeded the
60-second limit; the retained packet uses the concrete coefficient encoding and
keeps the full named nilpotent-propagation obligation. No file was split to evade
the compile limit.

Reference-clock reset observed on continuation: retained `scratchpad/final-dry-run.log`
reports 64 minutes, while the continuation dry run at 2026-10-19 17:22 UTC reports
15 minutes. The retained start timestamp 1792425946.2025676 has become
1792429583.517295 in `.budget`, without any worker edit. This records the reset for
the launcher owner; no tool or budget file was patched, and proof work continued.

The scratch canonical constant-ring comparison is identified with a natural
isomorphism by uniqueness of the adjunction to sections, and its naturality in
coefficient ring maps is proved there. The delivery retains the simpler pointwise
comparison. The small-site finitely-presented model comparison import used only
during experiments was removed. Explicit comparison isomorphisms are locally
irreducible after construction, so downstream elaboration uses their interfaces
without unfolding their component formulas. All five modules compiled together
after this optimization; the common-strata module took 18.4 seconds.
The common-strata node now records the intrinsic-to-fixed, weakly-etale localization,
and coefficient inverse-image comparison dependencies used by its proved helpers.

The server preflight requested a leansearch entry for the intrinsic-comparison node.
The additional search returned local-generator, constant-sheaf and sheaf-constructor
results, with no constructibility comparison; the node now records this search.

Current-source import repair: `Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel`
was retired in favor of the WeilConjectures twin. Importing the twin against the
available build produced a duplicate `DerivedCategory.IsPseudoCoherent` declaration.
The reconstruction proof now avoids this dependency entirely: its private bounded
model helper uses both good truncations directly over the Noetherian completion.
It strengthens only the private helper's hypotheses with Noetherianity, already
present at its caller. The public statements remain identical. The dependency
`lem-pc-pseudo-coherent-bounded-finite-free-model` is no longer needed by this local
argument; no global pruning claim is made.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
