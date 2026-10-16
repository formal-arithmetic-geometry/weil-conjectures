## What changed

Retained the complete proof of
`AlgebraicGeometry.ProEtale.glue_nonempty_support_open_closed_models`, with its original
signature and docstring unchanged. It uses the proved constructibility, prescribed-outer
localization, and finite-extension interfaces retained in this sandbox.

Repaired all six duplicate-helper findings in the returned delivery. Extracted the
existing private factorization, Serre-to-triangulated, single-complex, and exact-left-derived
shift proofs into `Sheaf.Paper.CondensedFiniteModelProofAPI`. Removed their definitions from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` and
`Sheaf.Paper.CondensedFlatCoefficientCalculus`; all three consumers now reuse them through
nonpublic `import all`. The shared finite-field triangulated theorem is exposed as its
node's public declaration; the remaining helpers remain private.

Both adapted modules are unclaimed. Source searches and downstream checks found no
external user of the removed private declarations and no `import all` of either original
parent. No existing public signature, definition, comparison morphism or target changes.
The new API is needed because both original parent modules reach this gluing item: direct
imports would cycle. This extraction deduplicates proof code; it is not a timeout workaround.

Change record: `coord/changes/shared-finite-coefficient-model-proof-api.md`.
The supporting shift-factorization property and generic composition/transport definitions
move with their lemmas, so they too have one definition and proof. The second reading
also replaces the new constructibility module's private stratification argument with the
existing `constructible_of_restrictions` helper, and deletes its copied `single_factors`
wrapper in favor of a direct application of the shared factorization theorem.
All existing and new node proof routes name the shared API where used. Unit records remain
unchanged. The earlier second readings are retained in scratchpad/report-before-extraction.md
for history; this repaired delivery requires a fresh independent reading.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.glue_nonempty_support_open_closed_models`.

Also proved the three retained public interfaces:

- `AlgebraicGeometry.ProEtale.CondensedRing.constructible_open_closed_images`, node
  `lem-weil-pbc-condensed-constructible-open-closed-images`.
- `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_localization_triangle`, node
  `lem-weil-pbc-condensed-finite-coefficient-localization`.
- `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_model_of_triangle`, node
  `lem-weil-pbc-condensed-finite-model-extensions`.

The extracted `AlgebraicGeometry.ProEtale.finiteBoundedTriangulated` is proved, node
`lem-weil-pbc-condensed-finite-model-proof-api`; its proof already existed privately in
TwoColimit. Its extraction does not count as another hole closed.

Sorries left in the item: none. Holes added anywhere in this delivery: zero. All new
interfaces and private helpers are proved; all data is explicitly constructed. Existing
unchanged lower-library holes remain inherited by the algebraic descent and gluing proofs.
This closes one of one original holes, with zero unfinished statements split off.

The independent reading compiled all seven modules without warnings or errors through
lcompile.py (4.4–56.2 seconds per file). After removing three redundant imports, the
extension module also compiled alone in 29.9 seconds. The subsequent wrapper removal
compiled in a scratch copy in 34.1 seconds; the shorter constructibility module compiled
in 4.1 seconds. The original item signature and
docstring are byte-identical to the repository version. Existing public signatures and
docstrings in both adapted parents are unchanged. All delivered DAG records name the
right declarations and have consistent proof-dependency unions; the six explicitly
stored Lean signatures match their declarations.

## No longer needed

The item's ten original proof imports are removed and replaced by the three interfaces
above:

- `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.ExtOneExtensionClassification`
- `Sheaf.Paper.CondensedSheafExtContinuity`
- `Sheaf.Paper.ProfinitePointPullback`

The algebraic module no longer directly imports
`WeilConjectures.ConstructibleSheaf.OpenClosed`: its zero-constructibility argument
now uses the existing helper. The localization module omits its earlier unused public import of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`: its statement needs no
constructibility predicate. The item's three original public imports are retained.

The following original planned nodes are unnecessary for this proof route:

- `lem-weil-pbc-ext-one-extension-classification`, module
  `Sheaf.CategoryTheory.ExtOneExtensionClassification`: complete the descended boundary
  by `Pretriangulated.distinguished_cocone_triangle₂` and compare triangles with
  `isoTriangleOfIso₁₃`.
- `lem-weil-pbc-closed-subset-closed-subscheme`: the closed scheme and immersion are
  already supplied.
- `lem-sc-derived-adjunction-from-underived`: use the existing exact derived-functor
  comparison API.
- `lem-weil-pbc-finite-dimensional-linear-homeomorphism`: use the existing coefficient
  comparison API.
- `lem-weil-pbc-proetale-ringed-open-closed`, module
  `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`: use the existing condensed
  recollement theorem directly.

The general derived proper-pushforward comparison in source
`Colimit/Compatibility.lean` is not used: the closed-support special case is proved
underived. The original broad direct proof-dependency list is replaced by the three
actual interfaces. Ingredients still used transitively, including coefficient
continuity, Serre closure, stratification, exact scalar extension, closed support, and
recollement, are not claimed globally pruned. The other thirteen original proof dependencies cease to be direct dependencies and
remain in the new DAG dependency closure (including statement dependencies):

- `def-constructible-stratification`
- `def-weil-closed-immersion`
- `def-weil-finite-subextension-directed-set`
- `def-weil-pbc-condensed-e-module-category`
- `def-weil-pbc-proetale-covering`
- `def-weil-proetale-inverse-image`
- `lem-sc-noetherian-finite-irreducible-components`
- `lem-weil-pbc-condensed-constructible-serre`
- `lem-weil-pbc-condensed-sheaf-ext-continuity`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-profinite-point-pullback`

The component-selection lemma is retained below other dependencies. The current source
import graph, with all seven delivered modules overlaid, removes 55 project modules
from the `TargetsCheck` closure. These are source-graph figures, not the pinned sorry ledger.
No module is deleted. The extracted helpers no longer have duplicate declarations in
`CondensedFiniteModelExtensions`, `TwoColimit`, or `CondensedFlatCoefficientCalculus`.
The latter two use the shared API; their public imports and public signatures are unchanged.
The new extension module now applies the shared Hom-colimit factorization theorem directly
instead of copying the parent's one-line `single_factors` wrapper.

- `Sheaf.AlgebraicGeometry.AffineClosedSpecializationLocalization`
- `Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover`
- `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`
- `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedAbelianFilteredColimits`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedFilteredColimits`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationAffineCoordinates`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationCounit`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison`
- `Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection`
- `Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.ExtOneExtensionClassification`
- `Sheaf.CategoryTheory.ModuleInverseImageUnitComparison`
- `Sheaf.CategoryTheory.Sites.CoveringRepresentableCoequalizer`
- `Sheaf.CategoryTheory.Sites.LowerShriekCorepresentability`
- `Sheaf.CategoryTheory.Sites.LowerShriekCoveringGenerators`
- `Sheaf.RingTheory.BoundedWContractibleExtension`
- `Sheaf.RingTheory.EtaleContraction`
- `Sheaf.RingTheory.EtaleContractionProperties`
- `Sheaf.RingTheory.EtaleContractionSize`
- `Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso`
- `Sheaf.RingTheory.PrincipalWLocalization`
- `Sheaf.RingTheory.PrincipalWLocalizationEvaluation`
- `Sheaf.RingTheory.PrincipalWLocalizationPoints`
- `Sheaf.RingTheory.PrincipalWLocalizationPrimeCharts`
- `Sheaf.RingTheory.PrincipalWLocalizationSize`
- `Sheaf.RingTheory.ProfiniteComponentRingPullback`
- `Sheaf.RingTheory.RetainedLocalization`
- `Sheaf.RingTheory.RetainedLocalizationProperties`
- `Sheaf.RingTheory.RetainedLocalizationSize`
- `Sheaf.RingTheory.StrictWCover`
- `Sheaf.RingTheory.StrictWCoverProperties`
- `Sheaf.RingTheory.StrictWCoverSize`
- `Sheaf.RingTheory.WContractibleClosedLocalization`
- `Sheaf.RingTheory.WContractibleGeometricCriterion`
- `Sheaf.Topology.BoundedExtremallyDisconnectedCover`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`
- `WeilConjectures.AlgebraicGeometry.ProEtale.SequentialLimit`
- `WeilConjectures.AlgebraicGeometry.ProEtale.SigmaCover`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `WeilConjectures.RingTheory.Spectrum.Prime.Colimit`

The second reading also removes these redundant proof-only imports from the new
`CondensedFiniteModelExtensions` module after extracting its helpers:

- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`
- `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero`

The constructibility module also removes its proof-only import
`WeilConjectures.ConstructibleSheaf.OpenClosed` and directly reuses the existing
`constructible_of_restrictions` helper. Its node no longer directly cites
`prop-constructible-open-closed`; that remains a dependency of the existing helper.

The extension node no longer directly depends on
`lem-weil-pbc-module-constructible-extension-zero`,
`lem-weil-pbc-condensed-constructible-serre`, or
`prop-weil-pbc-module-bounded-constructible-triangulated`: the shared API supplies its
single-complex and triangulated-closure proofs. Likewise the two-colimit node no longer
directly cites `lem-sf-derived-homology-long-exact`; the shared conditional triangulated
instance reaches it. These dependencies remain transitive and are not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The retained delivery copied six helpers already proved in parent modules. The landing
check correctly refused this duplication. Importing either original parent from the
support-induction argument would cycle, as verified by import_direction.py. The repair
extracts one shared dependency and adapts both unclaimed parents in the same delivery.

The earlier report claimed no adapted modules were necessary; that claim is superseded.
No mathematical statement was changed or found false. The route still descends one boundary,
completes a distinguished triangle, compares its boundary including shift compatibility,
and takes zeroth cohomology. Empty open/closed pieces, zero modules, coincident finite fields,
and a zero boundary impose no extra assumptions.

Fresh LeanSearch, LeanFinder, Loogle and direct library searches confirm the existing
components. LeanSearch is available in this repair and returned eight generic triangulated
and Serre-class components; its earlier unavailability remains only in the inherited records.

## New nodes

`lem-weil-pbc-condensed-constructible-open-closed-images`: proved preservation of
constructibility for complementary open extension and closed direct image.

`lem-weil-pbc-condensed-finite-coefficient-localization`: proved localization with exactly
the specified finite-coefficient outer models, without middle descent hidden in its statement.

`lem-weil-pbc-condensed-finite-model-extensions`: proved finite-coefficient descent for
zeroth cohomology of a distinguished extension of two finite models.

`lem-weil-pbc-condensed-finite-model-proof-api`: extracts the existing proved finite-field
triangulated-closure theorem and its private support API into a cycle-free dependency.
No new hole is created. Change record:
`coord/changes/shared-finite-coefficient-model-proof-api.md`.

## Second reading by G1

1. **Interfaces: pass.** Diffed all seven modules against the shared repository.
   Four are new. In the gluing item the complete theorem header, hypotheses, conclusion,
   universes, visibility and docstring are byte-identical; only its proof, private helpers
   and proof imports change. Both parent modules retain all public signatures, definitions,
   docstrings and public imports. Their removed private factorization, derived transport,
   single-complex and Serre helpers have one home in `CondensedFiniteModelProofAPI`.
   The finite-field triangulated lemma is newly public there, as the change record states.
   No target or definition used by a target is changed. Neither adapted parent has a claim.

2. **Proof and data: pass.** Read the localization, finite extension and main gluing
   arguments, and compared the extracted helpers with both originals. The algebraic proof
   descends the boundary by `singleHomDescent`, completes `g'` with
   `distinguished_cocone_triangle₂`, checks its shift-compatible transported boundary in
   `boundary_identification`, and uses `isoTriangleOfIso₁₃` before taking zeroth homology.
   The localization proof derives the closed scalar comparison from vanishing on the open
   complement and the invertible closed unit; it does not assume middle-object descent.
   All seven files compiled cleanly. No delivered file contains a sorry or forbidden
   declaration. All new definitions have explicit bodies; no definition chooses data from
   an unproved mere-existence assertion. A scratch module prints axioms of the five new/item
   public interfaces, all four flat-calculus theorems, the two-colimit theorem and all
   extracted helpers. Only `propext`, `Classical.choice`, `Quot.sound` and inherited
   `sorryAx` occur. The constructible-image and localization interfaces and every extracted
   private helper use only the three permitted axioms. Finite-field triangulated closure,
   finite-model extension and gluing still depend on lower open library statements;
   this is one local hole closed, not a claim of an entirely sorry-free target closure.

3. **New statements and search: pass.** Zero unfinished statements are split off.
   The proved constructibility theorem allows arbitrary commutative condensed coefficients;
   its open half uses the existing extension-by-zero theorem and its closed half concatenates
   stratifications with zero on the open complement. Localization fixes exactly `j!PU` and
   `k_*PZ` as the outer finite objects and adds no constructibility requirement. The extension
   theorem concerns a triangle with finite models only for its outer objects and proves a
   model of its middle zeroth homology; this is a strict algebraic part of gluing. Checked
   empty open/closed pieces, zero endpoint modules, zero boundary, and coincident coefficient
   fields: no step needs nonemptiness of a piece, nonzero modules or a strict field inclusion.
   The filtered undercategory has a common upper field even when the fields coincide.
   Fresh LeanFinder and Loogle searches for triangle uniqueness found the already used
   Mathlib `isoTriangleOfIso₁₃`; a differently worded msearch grep and direct library searches
   found no shorter finite-model theorem. A broader direct search also found the existing
   private `constructible_of_restrictions` criterion, so the new geometry module now applies
   it instead of rebuilding stratification concatenation. Direct searches confirmed the
   extracted helper occurrences are removed from both delivered parents; the remaining
   copied `single_factors` wrapper is removed from the extension module.

4. **Top-down route and pruning: pass, with cleanup.** The item proves its original goal
   from the three proved interfaces. The boundary-completion route replaces Ext-one
   classification with Mathlib triangle completion and comparison. All new public imports
   provide signature vocabulary; proof-only imports are nonpublic. Removed three redundant
   imports from `CondensedFiniteModelExtensions` and its copied `single_factors` wrapper.
   Replaced the constructibility module's five private normalization/concatenation helpers
   with the existing restriction criterion and removed its `ConstructibleSheaf.OpenClosed`
   import. Compiled both simplifications independently. Independently recomputed
   the `TargetsCheck` import closure with all seven modules overlaid: the 55 removed modules
   are exactly the list above. This is a source-graph count; pinned-ledger progress remains
   the maintainer's calculation. Compared all 18 original item proof dependencies against
   the report: five are unnecessary for this route and thirteen remain transitively used.
   Read `dag/units/sk-thm-properbasechange.json` and its source section: their realized
   statement and three proof steps are unchanged, and this lower support lemma bypasses
   none of them.

5. **DAG: pass, after correction.** Read all seven delivered node records and their proof
   routes. The six records that store Lean signatures agree with their declarations; the
   existing two-colimit record still names its unchanged theorem. Every `proof_deps` list
   is the union of its proof steps' `uses`. New records have their source, searches, creation,
   blueprint ancestry, chapter, unit and Lean data. Corrected the constructibility node to
   record reuse of the existing restriction criterion and coefficient-isomorphism transport.
   Corrected the extension node to cite the
   shared single-complex and triangulated helpers directly instead of their old dependencies.
   Corrected stale two-colimit prose claiming the generic bounded-constructible instance was
   avoided: the extracted helper now uses its corrected conditional form. Clarified that the
   flat-calculus module reuses the four derived-composition helpers, and recomputed the
   affected direct dependency unions. All edits are within stage-3-owned node fields.

Second-reading changes: reused the existing complementary-restriction criterion, removing
five duplicated private geometric helpers; replaced the copied single-complex factorization
wrapper by a direct shared-helper application; removed four redundant proof imports;
corrected four DAG descriptions/dependency lists; updated the validation report.
No public statement, definition, target, or unit record changed.
