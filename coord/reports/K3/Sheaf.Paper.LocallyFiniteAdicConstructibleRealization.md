## What changed

The final theorem `WeilConjectures.LocallyFiniteAdicRealization.locally_finite_adic_constructible_realization`
now has a complete assembly proof. It derives Noetherianity, finite dimension and stalkwise
invertibility from the original finite-type hypotheses, obtains a normalized functor,
applies separate Hom/image descent, and assembles the unchanged Realization structure.
Source essential smallness is proved by lifting J fully faithfully into the small target.

The existing realization data move verbatim to LocallyFiniteAdicRealizationData and are
publicly reexported. All original public imports remain, including the lower-shriek import
needed by compact-support consumers. No source-library file or consumer is changed.
The new NormalizedFunctor is only the functor/coefficient/transition part of Realization:
it does not assume Hom bijectivity, image characterization, or either smallness conclusion.
The normalization equation is part of this construction, not claimed for arbitrary
RealizationCore data with independently chosen integral comparisons.

The already proved source theorem DerivedCategory.essentiallySmall_bounded_inf supplies
the complete bounded-derived counting argument. Consequently
nativeConstructible_essentiallySmall is proved from smallness of constructible sheaves.
The three remaining mathematical steps each have their own module, exact statement,
source, full proof in words, edge-case discussion and DAG node. The unit route is unchanged.

Definition ownership and the exhaustive consumer inventory are recorded in
coord/changes/K3-native-realization-proof-separation.md.

Validation: all seven delivered Lean modules compile in import order. Timings were
16.8 s (unchanged data), 11.5 s (new functor data), and 2.3--2.8 s for each remaining
module, including 2.8 s for the original theorem. No profiling options remain.
All seven direct importers compile unchanged against the packet: CompactSupportData
42.8 s; NativeAdicRealizationData 11.0 s; NativeCoefficientInverseImage 16.0 s;
NativeWeilLocalizingBrownAdjoints 22.8 s; SfAdicCommonStageDescentEquivalence 40.5 s;
CompactSupportRealization 8.8 s; NativeGeometricBrownConstructibleComparison 22.4 s.
Their temporary source copies were removed after verification.

## Proved and sorry left

Original item: one hole; delivered item: zero holes.

Closed (by decomposition):
- WeilConjectures.LocallyFiniteAdicRealization.locally_finite_adic_constructible_realization
  (lem-sf-locally-finite-adic-constructible-realization).

Additional complete proof:
- WeilConjectures.LocallyFiniteAdicRealization.nativeConstructible_essentiallySmall
  (lem-sf-locally-finite-adic-constructible-small), using the existing generic bounded
  derived smallness theorem and the native heart counting statement.

Two holes added, each exactly `:= by sorry`, and no others left in the packet
(a third, nativeConstructibleSheaf_essentiallySmall, was closed by the reviewer; see below):
- WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_exists
  (lem-sf-locally-finite-adic-normalized-functor): native coefficient presentations,
  normalized triangulated functor and its common-field equation; no descent or smallness.
- WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent
  (lem-sf-locally-finite-adic-functor-descent): full faithfulness and image for the given
  normalized functor; no functor construction, coefficient construction or small models.

Closed by the reviewer of K3 12433ab5 (FIX):
- WeilConjectures.LocallyFiniteAdicRealization.nativeConstructibleSheaf_essentiallySmall
  (lem-sf-locally-finite-adic-constructible-sheaf-small): the library already has the
  native encoding `ProEtale.NativeEncoding.encoding` (full and faithful,
  lem-sf-native-adic-encoding-ordinary-operations) and `ProEtale.encoding_constructible_iff`
  (lem-sf-native-adic-encoding-constructibility) on Noetherian X; lifting the encoding to
  the constructible full subcategories and applying constructibleModuleObjects_essentiallySmall
  with essentiallySmall_of_fully_faithful proves it (the same proof as the G6 38c53fae review).
  Axioms: propext, Classical.choice, Quot.sound. Its node's proof, proof_deps and
  proof_origin follow this proof.

This is a decomposition of one upper hole into two genuine smaller obligations. No hollow definition or data chosen in a definition
from an unproved existence theorem is introduced.

## No longer needed

The dedicated BoundedPostnikovTower proof import and its node
lem-sfb-bounded-postnikov-extension-generation are unnecessary for this realization
route: the existing source bounded-inf theorem proves the finite truncation induction
and extension counting directly. (The reviewer restored the parent's tool_uses list: it records tools used, not proof
edges; the proof edges are proof_deps.)
The module is absent from the item's new Lean import closure. This does not withdraw
that module or any upstream declaration.

The following old proof imports leave the item and remain needed in the new step modules:
RationalCoefficientCategoryComparison; ContinuousRationalDerivedRealization;
RationalRealizationScalarCoherence; ConstructibleModuleObjectsEssentiallySmall;
RingedDerivedMonoidalComparisons; ExtensionProductEssentiallySmall (through the proved
generic bounded-derived theorem); CondensedFlatCoefficientCalculus;
CondensedFieldLfpLocalTriviality; CondensedQbarFunctionCoefficients;
CondensedQbarLfpLocalTriviality; ContinuousCoefficientRealizations;
IntegralStratifiedPerfectCharacterization; ScalarExtensionRingIso; and TwoColimit.
SfIntegralConstructible remains a statement prerequisite through the retained public
imports, so its redundant private import is dropped. FiniteType remains proof-only in
the item. None of these relocations prunes their mathematics. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The current server queue assigns proof work with one hole, not zero-hole rework.
The recorded red build lists three bad imports, but the unchanged current item compiles
against published artifacts in 30.7 seconds. The earlier R1 return specifically reported
that dropping the public lower-shriek import hid adicOpenImmersionLowerShriek from a
compact-support consumer. This packet preserves that public import and all other public
imports; consumers are checked against the changed overlay.

The returned R1 proposal also asserted commonField for every arbitrary RealizationCore.
An arbitrary choice of its integral natural isomorphisms has no stated scalar coherence,
so that universal normalization claim is not justified by the structure. It is not used.
The present construction requires coherent comparisons together and proves descent
separately, avoiding that issue.

The DAG's final smallness step need not rebuild Postnikov counting: a proved generic
source theorem already supplies it. This packet attaches a node to that existing theorem.
The remaining native heart counting and native-to-condensed comparisons are genuine
mathematical obligations, explicitly retained, not consequences claimed from general
category theory alone. Empty schemes, zero complexes, empty intervals and rank-zero
local models are included in the statements and proof descriptions.

## New nodes

- def-sf-locally-finite-adic-normalized-functor: FunctorData, its transition predicate,
  and NormalizedFunctor, with no descent or smallness fields.
- lem-sf-locally-finite-adic-normalized-functor: construct that data under the geometric
  hypotheses; parent proof steps 2--5, Bhatt--Scholze 6.8.2, 6.8.14 and 6.8.15.
- lem-sf-locally-finite-adic-functor-descent: parent steps 3 and 6--7, using the existing
  finite-field realization and condensed two-colimit declarations.
- lem-sf-locally-finite-adic-constructible-sheaf-small: the first counting step of parent
  step 8, from constructible module presentation counting and native internal modules.
- lem-sf-locally-finite-adic-constructible-small: proved bounded-derived consequence of
  the preceding heart statement.
- lem-sfb-small-bounded-cohomology: attaches the already proved source declaration
  DerivedCategory.essentiallySmall_bounded_inf; no copied module or new hole.

Every new node records actual LeanSearch, LeanFinder, and grep queries from searches.jsonl.
Blueprint searches found no duplicate native statement. The existing data-definition node
is updated only in lean ownership for its verbatim relocation. The reviewer added
def-sf-locally-finite-adic-realization-data to the item node's stmt_deps (its statement
names Realization) and restored the item's proof_origin (Bhatt--Scholze §6.8). The parent's proof edges
now follow the actual assembly. Change record:
coord/changes/K3-native-realization-proof-separation.md.

## Related modules compiled before delivery

7 related module(s) compiled against this delivery by deliver3.py: 7 OK.

```json
{"capped": false, "direct": 7, "left_out": 0, "own": {"Sheaf.Paper.LocallyFiniteAdicConstructibleRealization": "916ef6335a84737c7a527093bbdbd2477d597084", "Sheaf.Paper.LocallyFiniteAdicConstructibleSheafSmall": "4555935b54dc323f5a986ccf0a1f39a469b0ef7f", "Sheaf.Paper.LocallyFiniteAdicConstructibleSmall": "cfea33eb7c939da3398dca837facf1fced65de93", "Sheaf.Paper.LocallyFiniteAdicFunctorDescent": "b76cf1c90ffa7c9964c78e73a9d29349b96b8aff", "Sheaf.Paper.LocallyFiniteAdicNormalizedFunctor": "6111c569860225f1c891d72ddc6fa7d3f4dcf9c9", "Sheaf.Paper.LocallyFiniteAdicNormalizedFunctorData": "f514d6bb073aba1a65624b028889f95525eafc41", "Sheaf.Paper.LocallyFiniteAdicRealizationData": "77c8529eeff8eaa0b76b4f0bffd400a6c5c905b9"}, "results": {"Sheaf.Paper.LocallyFiniteAdicCompactSupportData": {"hash": "228607968cbf697875a27c3beb2d872c5ea196c3", "status": "OK"}, "Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization": {"hash": "b1222b33661731a5f010777a9242825042cdc6f7", "status": "OK"}, "Sheaf.Paper.NativeAdicRealizationData": {"hash": "1c5841337f21707909a7b99a78611e0d05711743", "status": "OK"}, "Sheaf.Paper.NativeCoefficientInverseImage": {"hash": "01bdc6764a3636f469e3c9e7eaf9d66b9e5327ac", "status": "OK"}, "Sheaf.Paper.NativeGeometricBrownConstructibleComparison": {"hash": "90eb752eec7082b347f81fcc85fa44a9ccc197e7", "status": "OK"}, "Sheaf.Paper.NativeWeilLocalizingBrownAdjoints": {"hash": "1c4987d09f9c6a74550dd8ae52e1615d212aaaac", "status": "OK"}, "Sheaf.Paper.SfAdicCommonStageDescentEquivalence": {"hash": "3cef5ea1f2ac78bc6ac6380937ca9dc32b367198", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T05:22:52+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
