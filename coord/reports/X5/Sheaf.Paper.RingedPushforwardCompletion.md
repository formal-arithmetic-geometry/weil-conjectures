## What changed

`CategoryTheory.ringedPushforward_completion` now has a complete Lean proof from an
augmented Cech tensor-pullback lemma and the existing Cech reflector theorem. Its
statement, public imports, independent derived-category universes, unit equation,
and uniqueness among all arrows are unchanged.

Global augmented Cech models and the closed tensor-Hom adjunctions are obtained
from existing library theorems. The remaining geometric lemma accepts these models
and structures as inputs; it does not postpone their construction.

The categorical proof constructs natural inverse transposes of the Cech units,
takes right adjoints of the augmented tensor square, proves the unit normalization using the composite Hom equivalences, and transports across
unit-preserving reflector isomorphisms. It also proves preservation of completeness:
a complete source object has invertible source unit; the comparison equation forces
an invertible target unit, identifying the direct image with a complete object.

A separate proved theorem constructs a left adjoint to the supplied derived direct
image in independent localization universes. It uses the existing K-flat module
pullback theorem, a resolving class of flat-term K-flat complexes, absolute Kan
extension properties, K-injective computation, and Mathlib's derived adjunction.
It imposes no ideal or completion hypotheses. It also records the ordinary additive
module left adjoint, the homotopy left-derived comparison, and its invertibility on
flat-term K-flat representatives, so the geometric step can access the construction
without repeating its existence proof.

Validation: `lcompile.py --all` compiled all three sandbox modules cleanly under
the unchanged 60-second limit. The final all-module run compiled the main theorem in 14.3 seconds after
removing the two generic sheaf-composition instances locally for this
declaration (an earlier uncached run took 33.6 seconds). The strengthened proved derived-adjunction module compiled in 9.7
seconds; the geometric statement compiled in 26.8 seconds on an uncached run. Explicit sheaf-composition instances in the auxiliary
statements and cached instances in the main proof avoid repeated inference
through the large image-ideal interface. The first server preflight reported
that its separate axiom probes for the derived-adjunction and main modules
timed out; it states that the merge reruns these probes. This is not a claim
that those independent probes passed.

## Proved and sorry left

- Original holes closed: `CategoryTheory.ringedPushforward_completion` (1 of 1).
- New proved theorem: `CategoryTheory.RingedToposMorphism.exists_derivedLeftAdjoint`
  (`lem-weil-pbc-ringed-derived-adjunction-independent-universes`), zero holes.
- New hole: `CategoryTheory.ringed_augmentedCech_tensor_pullback`
  (`lem-weil-pbc-augmented-cech-tensor-pullback`), exactly `by sorry`.
- No other delivered declaration contains `sorry`. The original theorem is reduced
  to a geometric augmented tensor comparison; this is a decomposition, not a net
  hole reduction (1 closed, 1 added). The new lemma does not assert any conclusion
  about completion reflectors. It records finite generation of the image ideal
  and the tensor/pullback square for supplied augmented Cech models. It has no
  conclusion about reflection, direct-image preservation, or uniqueness.

## No longer needed

Removed direct proof imports from the item module:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`
- `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`
- `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`
- `Sheaf.CategoryTheory.RingedPresentationTransport` (retained in the geometric lemma's proof plan; no unused proof import)
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` (used by the proved derived-adjunction lemma)
- `Sheaf.CategoryTheory.RingedToposSitePresentation`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `Sheaf.Paper.CoefficientRingedTensorHomModel` (now a public statement import of the new geometric lemma)
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`
- `Sheaf.Paper.ProjectionFormulaTotalization`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedDerivedSliceLocalization`
- `Sheaf.Paper.RingedStrictTowerProjectionMorphism`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` (retained in the geometric lemma's proof plan; no unused proof import)
- `Sheaf.Paper.RingedTopoiDerivedPullback` (retained in the geometric lemma's proof plan; no unused proof import)
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`

The shorter argument needs none of the following original direct proof dependencies:

- `def-weil-pbc-projection-formula-arrows`
- `def-weil-pbc-sites-and-cohomology`
- `lem-sfb-derived-internal-hom-sections-model`
- `lem-sfb-unbounded-sections-localization`
- `lem-weil-pbc-extended-cech-completion-model`
- `lem-weil-pbc-ringed-cech-koszul-dual-limit`
- `lem-weil-pbc-ringed-derived-slice-localization`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-koszul-completion-reflector`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-pbc-ringed-strict-tower-projection-morphism`
- `lem-weil-pbc-ringed-topos-site-presentation`
- `lem-weil-ringed-tower-pushforward-limit-comparison`
- `lem-weil-tower-category-levelwise-abelian`
- `lemma-weil-pbc-projection-formula-totalization`

The strict Koszul tensor towers, their projection morphism, perfect projection
formula, derived tower limits, and direct-image/limit comparison are not used by
this argument. No declaration is removed from the adopted source library, and no
module is withdrawn. Dependencies needed transitively by the geometric bridge or
the derived-adjunction construction remain needed. Pruning here describes this
proof route, not a claim that these modules have no other consumers.

The four old top-level tool approvals withdrawn from the item are
`lem-sfb-derived-internal-hom-sections-model`,
`lem-weil-ringed-tower-pushforward-limit-comparison`,
`prop-pur-kinjective-resolutions-exist`, and
`lem-sfb-unbounded-sections-localization`: the new direct proof does not use these
tools. K-injective resolution existence remains an explicit dependency of the
proved derived-adjunction node. The generic resolving-class,
essential-constancy, and closed tensor-model results used by the new nodes are
recorded explicitly in those nodes for review.

## Where the brief, the DAG or earlier work was wrong

The original plan's site-presentation theorem requires precoverage presentation
data not present in this arbitrary-topology statement; its presentation transport
also uses standard derived universes rather than the two supplied universes.
The new argument avoids reducing the main theorem to that site-presentation API.
The geometric bridge still needs compatibility with arbitrary sheaf slices, which
its proof in words records explicitly. Its localization step uses the already
proved `existsUnique_localizationInverseImage` and `ringedSliceLocalizationModel`
(the latter at the identity site functor for extension of scalars), preserving
the actual localization units. The canonical tensor-pullback API allows independent
site universes but still shares one derived universe. The geometric lemma therefore
records transport to standard localization models, comparison of restriction and
internal Hom by uniqueness of localization lifts, and transport back. It does not
apply the common-universe theorem directly to `wX` and `wY`.

The completion comparison can be obtained by taking right adjoints of a Cech tensor
square. Consequently a separate vanishing proof of preservation, a strict tower
construction, and a tower/projection-formula argument are unnecessary here. The
empty ideal has Cech model R and completion the identity; the unit ideal has an
acyclic Cech model and zero completion. These cases, the identity morphism, and
noninvertible structural ring maps satisfy the new geometric statement. For the
nonflat map `Z → F_p` and the ideal `(p)`, its image ideal is zero and the target
Cech factor `[Z → Z[1/p]]` pulls back to `[F_p → 0]`. Thus it becomes the source
ring complex, as required; the proof must use K-flat Cech representatives rather
than assume exact scalar extension.

## New nodes

`lem-weil-pbc-ringed-derived-adjunction-independent-universes` records the proved
existence of a derived inverse-image adjunction in independent universes. Its
module is `Sheaf.CategoryTheory.RingedToposDerivedAdjunctionOfUniverses`.

`lem-weil-pbc-augmented-cech-tensor-pullback` records the remaining geometric result,
from the localization/tensor calculation underlying Stacks 0A0G. Its module is
`Sheaf.Paper.AugmentedCechTensorPullback`. Its docstring and node give a full
construction in words and the exact augmentation equation required downstream.

No existing definition or statement is changed. The conservative command-level
interface check requires the elaboration change record
`coord/changes/X5-ringed-completion-local-elaboration.md`. It records the scoped
instance exclusions, the unchanged signature, and the unaffected direct consumer.
No consumer adaptation is required or delivered.
The original theorem signature and all six public imports have been checked
verbatim against the current source. The owning unit is `sk-thm-properbasechange`;
its realized statement and three proof steps are preserved. This item is below
those unit nodes, so no unit route is bypassed.

The backward-definitional-equality option used by the new proofs is scoped to
individual declarations. The existing global instance attribute remains unchanged. The two additional
instance exclusions are local to this declaration; the imported instance
environment is restored afterward, as documented in the change record. Search records include LeanSearch,
Loogle/LeanFinder, and a Mathlib-source grep for each new node.

Blueprint searches for `Cech`, `derived adjunction`, and `ringed` found no exact
blueprint statement for either new auxiliary lemma. Both are attached through
this item to `prop-weil-pbc-scalar-extension`, final comparison sentence. The
other derived-adjunction blueprint results concern scheme/condensed coefficient
settings, rather than this supplied arbitrary ringed-topos direct image.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
