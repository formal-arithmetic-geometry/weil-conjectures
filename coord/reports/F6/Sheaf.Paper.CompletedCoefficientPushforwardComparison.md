## What changed

The existing model declarations were extracted verbatim to
Sheaf.Paper.CompletedCoefficientPushforwardModels and publicly re-exported by the item.
Their signatures and data constructions, and the comparison theorem signature, are unchanged.
This extraction makes the smaller proof modules acyclic. No source-library file changes.
The site proof keeps concrete quotient sheafification out of sequence unification: generic
restriction-composition and successor-section lemmas supply its transition equations.
See
coord/changes/F6-completed-coefficient-pushforward-model-extraction.md.

Sheaf.Paper.CompletedCoefficientPushforwardSites constructs all site-side data: exact scalar
restrictions and their normalized identity/composition comparisons, the generator-normalized
finite coefficient isomorphisms, exact restriction of semilinear systems to strict completed
module towers, and total derived inverse limit with its normalized projections.

Sheaf.Paper.CompletedCoefficientStructureMap now proves
WeilConjectures.CompletedCoefficientPushforward.completedStructure_existsUnique from
Mathlib's sheafification adjunction and preserved-limit universal property. The finite
constant-section maps are proved natural in the actual quotient homomorphisms; ring-sheaf
direct image preserves the tower limit, whose lift supplies the map, and limit extensionality
proves uniqueness. It also proves compatibility with the constant integral scalar map:
limit extensionality reduces this square to naturality of the same quotient maps.
The main assembly constructs this map and both compatibility proofs before invoking the remaining
diagram extension. That result now extends the supplied map with these proven compatibilities and records equality to it.
Thus this first direct-image construction is proved in Lean, not part of its remaining hole.

The item proves strict realization degreewise. It also constructs the reduction augmentation
as an ordinary limit lift of the compatible tensor units and proves uniqueness by equality
after each projection. The final assembly applies the three independent direct-image and
completeness results. Reconstruction is obtained by applying the derived image to the
invertible source augmentation and composing with limitComparison. It never chooses an
arbitrary triangle lift or an arbitrary witness of a mere-existence data theorem.

## Proved and sorry left

Validation: all six original delivery modules compiled through lcompile.py --all, as did
unchanged original consumers Sheaf.Paper.FiniteEtaleAdicCohomology and
Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility. The copies used to test the consumers
were removed after checking that they were byte-identical to the repository originals.
The unchanged indirect consumer Sheaf.Paper.FourierArtinSchreierProperties also
compiled successfully (13.6 s); its byte-identical temporary copy was removed.
The two reported style warnings were corrected. The first delivery preflight found only
metadata errors: it required LeanSearch as a distinct search kind, the parser's structure
signature excluding its fields, and the conservative push-name hit in
FourierArtinSchreierProperties in the change-record consumer table. These were corrected. The standalone cleanup recheck returned
server-busy exit 124 without compiler diagnostics; deliver3.py performs the final packet
compile and preflight on the corrected files. The first retry received no answer
from the busy compile server within 510 s for the model module, so it pushed nothing
and is being retried without source changes.

Delivery infrastructure outcome: subsequent attempts first received the documented
compile-server busy response, then twice exhausted the delivery-slot queue.
The final two deliver3.py attempts were terminated with exit code 143 (SIGTERM),
without a diagnostic or DELIVERED line. No successful push is claimed. The
six-file packet and all metadata remain in this sandbox for retry.

Resumed attempt F6/2026-10-21T18:32:35Z received a fresh reference clock
(start 1792607554.9502115, reference 7200 s, session 86400 s), despite the retained
packet and earlier compile/preflight work. No budget metadata was changed. The required
first delivery retry (started 18:33 UTC, process session 9675) exhausted its 3000-second
slot wait and exited 75 at approximately 19:23 UTC: DELIVERY BUSY, nothing pushed.
During this wait, the packet was audited against current source: model extraction and
the original theorem signature remain unchanged; all six DAG dependency lists match
their proof-step uses. A scratch proof of normalization and invertibility independence
for arbitrary RightImage models compiled without holes; the canonical completed
structural-map construction is being checked separately. Scratch files are not delivery
modules and add no reported holes. The fresh --all compile completed successfully at
19:26 UTC: Models 30.6 s, DirectImageDiagrams 2.3 s, Sites 11.9 s,
PreservesCompleteness 2.4 s, AugmentationIso 3.1 s, Comparison 11.5 s; exit 0
and no diagnostics. The second delivery retry (session 20116) exited 1 at 19:29 UTC with the split-off
reference-clock gate: 3 added sorry after 56 of 120 minutes, threshold 72 minutes.
No push occurred. Its output is preserved in scratchpad/delivery-resume-2.log.
This is the documented fresh-clock refusal, not a tool failure; proof work continues.

Original holes: one, WeilConjectures.CompletedCoefficientPushforward.comparison.
This hole is closed by a complete assembly, with three strictly smaller statements split off.
This is a decomposition, not a proof of the original mathematical package: holes closed 1,
holes added 3, net -2. No sorry occurs in any definition or private helper.

The revised seven-module packet compiled cleanly with exit 0 (packet-structure.log):
the new structural-map module took 4.4 s, the adapted diagram statement 2.6 s, and
comparison 12.2 s; unchanged modules were reused. All remaining holes stay at three;
no new hole was added by this resumed proof work. The final seven-module --all check including the
constant integral square also passed with no diagnostics: Models 39.1 s, Diagrams 3.6 s,
Sites 18.0 s, StructureMap 6.0 s, PreservesCompleteness 3.9 s, AugmentationIso 4.1 s,
Comparison 15.8 s (packet-constant.log).

Fresh consumer checks: FourierArtinSchreierProperties compiled unchanged in 18.7 s.
FiniteEtaleAdicCohomology and OrdinaryAdjunctionScalarCompatibility each reached the
60-second compile limit, with no Lean error or goal output. Profiling copies and
counterfactual copies using only the published library were submitted to distinguish
a regression from existing elaboration/import cost. These temporary sources are not
intended delivery changes. The earlier complete consumer checks remain recorded above;
the fresh results are kept separately in scratchpad/consumer*.log and adjunction*.log. OrdinaryAdjunctionScalarCompatibility then compiled with profiling in 19.7 s
against the delivery, and its published-library counterfactual compiled in 18.7 s.
The comparable profiles showed no regression; the only warnings concerned the temporary
profiler options. Its profiling source and the byte-identical Fourier consumer copy
were verified against the repository originals and removed. No consumer adaptation is
part of the packet.
The first finite-etale profiling and published-baseline requests both ended with the
documented busy-server response (no answer within 645 s, exit 124), without Lean
diagnostics. After an interval, the finite-etale profiling retry compiled successfully against
the delivery in 38.8 s. Only the expected temporary profiler-option style warnings
were emitted. Its source was verified byte-identical to the repository after removing
the profiling options and was removed. All three consumer checks are now resolved;
no consumer changes or profiler options are delivered.

Proved without new holes:
WeilConjectures.CompletedCoefficientPushforward.completedStructure_existsUnique;
WeilConjectures.CompletedCoefficientPushforward.siteData_exists,
including its exact-restriction, finite-ring, strict-system and normalized-limit private
helpers; the item's strictComplexTower_exists and reductionAugmentation_existsUnique.
The item comparison itself has a complete Lean proof from the three listed results.

Every remaining sorry is exactly the body of one of these public theorems:

- WeilConjectures.CompletedCoefficientPushforward.directImageDiagrams_exists,
  node lem-pur-completed-coefficient-direct-image-diagrams;
- WeilConjectures.CompletedCoefficientPushforward.reductionAugmentation_isIso,
  node lem-pur-completed-reduction-augmentation-iso;
- WeilConjectures.CompletedCoefficientPushforward.directImage_preservesComplete,
  node lem-pur-completed-direct-image-preserves-completeness.

Each is in a separate module with its complete source argument and edge-case discussion
in the docstring. The first concerns coherent direct-image diagrams only, the second the
specified source augmentation only, and the third preservation of completeness only.
None restates ComparisonData or assumes a repackaged version of the final conclusion.

## No longer needed

The interface extraction removes the following private proof imports from the old item.
They are not required by the model declarations. The site-construction module imports
RingedStrictTowerHomotopyLimitIndependentCoefficients where its private universal-derived
construction is actually used. Mathematical dependencies of the remaining separate results
remain in their DAG nodes; no source declaration is withdrawn and no whole-library module
is claimed pruned.

- Mathlib.Algebra.Homology.DerivedCategory.Basic
- Sheaf.Paper.CompletedIntegralCoefficientGerm
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
- Sheaf.Paper.IntegralReductionTower
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
- Sheaf.Paper.AdicCoefficientDatum
- Sheaf.Paper.PbcActualStrictPullback
- Mathlib.CategoryTheory.Sites.ConstantSheaf
- Sheaf.Paper.IntrinsicCompletionCompleted
- Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
- Sheaf.CategoryTheory.RingedSiteModules
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.CategoryTheory.DiagramSiteRealization
- Mathlib.Algebra.Category.Grp.FilteredColimits
- Mathlib.CategoryTheory.Sites.Limits
- Sheaf.CategoryTheory.KInjectiveTotalDerived
- Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
- Sheaf.Paper.WeilCompletedTensorReflector
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
- Sheaf.Paper.CompletedDirectImageLimits
- Sheaf.Paper.KoszulReconstruction
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.Paper.DerivedCompleteOnSlices
- Sheaf.Paper.IntegralReductionTowerCanonical
- Sheaf.Paper.PbcQbarCompletedPullback

The structural-map proof uses the ordinary Mathlib limit API directly; it needs no
profinite inverse-image or derived-composition lemma to construct the ring map itself.
Those dependencies remain needed for the separate diagram extension.

The proved site-side route uses exactness and the localization universal property directly.
It does not use K-flat pullback to construct scalar restriction, nor does strict realization
require the coefficient direct-image or adic completeness theorems. No target route or
blueprint unit realization is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The third delivery reached server preflight and was refused because the model-extraction
change record listed only direct consumers and one indirect name match. The corrected
record now lists all 77 transitive consumers from the current source import closure,
including every conservative short-name match. Their declarations are unchanged through
the original module's public re-export; no consumer adaptation is required. The preflight
also reported a busy-server axiom probe, which its merge step will repeat. Nothing was
pushed by this refused attempt.

The named ringed-topos composition, coefficient-square and tower direct-image theorems
state their main interfaces with a common small-site/coefficient universe. The item retains
site object universe t+1, site hom universe t and coefficient universe max u (t+1).
They therefore need transport to a sufficiently large equivalent small site before direct
application. This is explicit in the remaining direct-image-diagram argument.

The Roos/intrinsic equivalence states invertibility of specific Koszul and intrinsic units.
The item asks about a chain-level tensor augmentation followed by an arbitrary normalized
strict derived-limit unit. Identifying that particular map, rather than only its endpoints,
is a separate comparison argument, recorded by the augmentation-isomorphism node.

No statement was found false, no target statement changed, and no upstream declaration or
proof was removed. The site's scalar, finite-coefficient and strict-system constructions
were proved directly from the actual declarations rather than left as additional holes.
Blueprint searches for completed coefficients, strict reduction and derived direct image
returned the existing coefficient/completion and parent-adjunction nodes, with no blueprint
node stating these extracted normalized interface results. The nearest blueprint ancestor
is fix-prop-adjunctions, Step 1, as recorded by blueprint_refs.py ancestor.

## New nodes

- def-pur-completed-pushforward-models attaches the unchanged extracted interface records.
- lem-pur-completed-coefficient-site-data attaches the proved siteData_exists construction.
- lem-pur-completed-coefficient-structure-map attaches the fully proved, unique structural
  ring map from the finite coefficient projection equations. Its own source proof step
  is now performed by the main assembly before the remaining diagram theorem.
- lem-pur-completed-coefficient-direct-image-diagrams separates normalized coherent
  direct-image diagrams, including limit and evaluation compatibility.
- lem-pur-completed-reduction-augmentation-iso separates invertibility of the specified
  source reduction augmentation under completeness.
- lem-pur-completed-direct-image-preserves-completeness separates the adic direct-image
  preservation assertion for any normalized derived model.

The original node's proof and proof dependencies follow the final assembly. Its statement,
statement dependencies, source and blueprint route are retained. The extraction change
record is coord/changes/F6-completed-coefficient-pushforward-model-extraction.md.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
