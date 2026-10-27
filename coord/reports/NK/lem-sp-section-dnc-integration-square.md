## Worker report

The module `Sheaf.Paper.SectionDncIntegrationSquare` states the integrated DNC
base-change square and the diagonal identification. Both theorem proofs are
`sorry`. All helper definitions have actual data. The item statement is unchanged;
its statement dependencies cite the definition owners of the helpers actually
used. The H2 repair adds three existing:true definition ownership records; no new
Lean module, dependency module, mathematical definition or theorem is needed.

Hypotheses and clauses, matched to the Lean:

* The fixed algebraic closure of F_q and coefficient prime different from the
  characteristic are `P.field` and `P.coefficients` in `PurityFiniteSetting.{u}`.
  `_hE : P.extension = ⊥` specializes the finite extension to Q_ell; `P.level`
  and `P.level_pos` give every r >= 1. `P.Coefficient` is the published size lift
  of its valuation quotient, the canonical Z/ell^r realization. It uses ordinary
  constant-coefficient module sheaves, not completion or an adic category.
* The base schemes B and B' have explicit structure maps `aB`, `aB'`, with
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. `b` is arbitrary and
  `_hb : b ≫ aB = aB'` makes it a k-morphism. No flatness is imposed. `Pair B d`
  bundles V, g, s, smooth pure dimension d, separatedness, quasi-compactness,
  closed immersion, and the section equation. The k-structure on V is g ≫ aB;
  the stated finite-type and separated properties follow from these binders.
* `X' : Pair B' d` and `sq : BaseChange b X' X` specify any Cartesian realization
  of V times_B B', with `sq.section_eq` the pulled-back section equation. This is
  equivalent to using the chosen categorical pullback and avoids choosing extra
  coordinates. It includes the identity square as well as nonflat squares.
* `SectionRestriction.invariant` is `Dnc.sourceSection`, the published actual
  pro-etale section invariant s*omega_g, with its canonical ordinary-etale
  presentation. `baseComparison` is c_s: it is derived pullback composition,
  the actual counit-defined `dualizingComplexBaseChangeMap`, then the canonical
  comparison-unit and nu* transports. It is not an arbitrary endpoint iso.
* The family, punctured trivialization and fibres are the actual published Rees
  objects from `PurityDncFamilyIntrinsic`, `Dnc.familyEtale`, `fibreOne`,
  `fibreZero` and `SectionRestriction.familyPair`. `reesBaseMap`,
  `reesBaseGeometry`, `normalBaseMap` and `normalBaseGeometry` from the landed
  section-restriction node supply their canonical arbitrary-base-change
  identifications. This item uses their associated-graded zero fibre directly.
* `delta` selects only the unique coordinate-normalized arrow from
  `Dnc.existsUnique_dncInvariance`, between the actual section objects.
* `normalIntegration` is z*b_N, including Tate restriction: first the canonical
  normal section comparison, then the exceptional localization comparison for
  the homogeneous-normalized Rees/conormal bundle isomorphism, then
  `FiniteRingSectionDeformation.bundleOrientation`. The last is the inverse
  of the zero-section pullback of the actual integration adjunct. Its source
  is the symmetric algebra of the conormal of X.s, never an independently
  chosen trivial bundle. Projection and augmentation preservation are checked
  using `reesConeComparison_spec` and `coneBundleIso_spec`. All compactification,
  conormal-rank, and Noetherian instances in this definition are derived from
  the given hypotheses by existing theorems, not added assumptions.
* `psi` is exactly `delta ≪≫ normalIntegration`. The main theorem is the equality
  `baseComparison ≪≫ psi' = pull.mapIso psi ≪≫ OrientationRefinement.tate`.
  With Lean's left-to-right composition this is precisely
  psi_(g',s') c_s = b*psi_(g,s), under canonical Tate pullback. It is equality of
  isomorphisms in the derived category, hence also equality of the specified
  arrows, not merely degreewise cohomological identification.
* The diagonal is `diagonalPair d f`, with g = pullback.fst f f and
  s = pullback.diagonal f. `chartDiagonalAlpha` is kappa_f: its recorded
  definition pulls back the inverse of the counit-defined self-base-change
  exchange and uses p2 Delta = 1 with the coefficient-unit comparisons.
  `section_dnc_integration_diagonal` says its inverse followed by the same psi
  equals `P.diagonalDualizingObject d f aY`. The latter is the uniquely specified
  orientation with `DiagonalOrientationNormalization`; the imported
  `diagonalOrientationCharts` gives precisely its standard ordered-coordinate
  normalization. No extra coordinate chart hypothesis is imposed.
* N is universally quantified in both theorems. It is a normalized presentation
  of the same compact-support adjunctions, with actual sum/evaluation counit,
  identity and refinement equations; it is not an orientation, free exchange,
  or arbitrary isomorphism between endpoints. Universal quantification retains
  all normalized presentations rather than choosing data from bare Nonempty.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and `CoefficientDatum`.
* `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and
  `SmoothOfRelativeDimension`; the latter's `smooth` theorem is explicitly
  installed where the implementation needs it.
* `Sheaf.Paper.PuritySectionInvariantIntrinsic`: `sectionInvariantFinite` and
  its actual intrinsic finite realization; `PurityDncFiniteRealization`:
  `sectionComparison`, including the inverse comparison adjunction unit.
* `Sheaf.Paper.PurityDncComparisons`: `sourceSection`, `normalSection`,
  `normalComparison`, `sectionBaseChange`, `compactifiable`.
* `Sheaf.Paper.PurityDncInvariance`: `existsUnique_dncInvariance`, `pullComparison`.
* `Sheaf.Paper.PuritySectionEtaleRestriction`: `Pair`, `BaseChange`, `invariant`,
  `delta`, `baseComparison`; also the constructed Rees/fibre geometry noted above.
* `Sheaf.Paper.PurityNormalProjection`: `purityNormalProjection_eq`.
* `Sheaf.Paper.FiniteSmoothCanonicalInterfaces`: `reesConeComparison` and
  `reesConeComparison_spec`; its normalization fixes homogeneous generators.
* `Sheaf.Paper.FiniteRingSectionDeformation`: `geometry`, `coneBundleIso`,
  `coneBundleIso_spec`, `bundleOrientation` and its actual integration adjunct.
* `Sheaf.Paper.DiagonalDncChartNormalization`: `chartSectionEtaleRestriction`
  and `chartDiagonalAlpha`. These reuse the specified exceptional adjunctions.
* `Sheaf.Paper.DiagonalOrientationRefinement`: `OrientationRefinement.tate`.
* `Sheaf.Paper.PurityDiagonalDualizingObject`: `diagonalDualizingObject` and
  its coordinate-normalization predicate. `DiagonalOrientationCharts`:
  `diagonalOrientationCharts`. `PurityDiagonalBaseChangeCompared`:
  `diagonalComparedRestriction`, `comparedDiagonalBaseChange`.
* `Sheaf.Paper.VectorBundlePurity`: `vectorBundlePurity`, including normalized
  integration and arbitrary-base-change equation; proof import
  `VectorIntegrationSiteComparison.finiteTypeSiteComparison` identifies the
  actual site presentations of these adjuncts.
* `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`:
  `ProEtale.isIso_csAuxiliaryExchange`; proof import
  `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv_vcomp`,
  `mateEquiv_hcomp`, both conjugation/pasting lemmas and `conjugateEquiv_id`.
* Coefficient ambient interfaces read: `ProEtale.FiniteCoefficientModules`,
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`,
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`, `ProEtale.derivedTensor`,
  the derived operations in `DerivedPullbackTensorHom`, the finite positive
  twist `diagonalTwist` and the intrinsic twists reexported by
  `IntrinsicCoefficientTwistsUnrestricted`. They are the existing ordinary
  uncompleted categories and operations; this square imposes no extra ctf
  input object or condition.
* `def-weil-scheme-morphism-properties` is expressly a convention-only node;
  its lean record is null because its individually named Mathlib notions are
  used, not a private duplicate of this convention.

Edge cases checked before and after writing: d is a natural number without a
positivity assumption; bundleOrientation uses the empty ordered tensor at d=0.
No scheme has a nonemptiness hypothesis; all zero-fibre and bundle constructions
exist on the empty base. b has no flatness, immersion or smoothness hypothesis.
The identity square is permitted by `BaseChange.id`. Coefficients allow every
positive level, including ell=2 and level one; no divisibility or ramification
condition was introduced. The small pro-etale site and module universe remain
u+1 with morphism universe u, as in the recorded framework.

Searches: msearch leansearch on “Smooth closed section dualizing complex deformation to the normal bundle integration orientation commutes with pullback” returned eight unrelated manifold/vector-field results. msearch leanfinder on “Naturality under arbitrary base change of smooth
closed section deformation followed by integration orientation” returned eight
manifold vector-field pullback results, no match. msearch loogle query
`Etale.sectionInvariant, IsPullback` returned zero hits (unknown identifier in
Mathlib). msearch grep `(deformation|normalBundle).*(purity|integration)|(purity|integration).*(deformation|normalBundle)`
returned zero hits. Project rg searches for dncInvariance, normal/section
orientations, normalCone purity, integration sections, the item id, and the
proposed declaration names found the helper owners listed above but no statement
of this full arbitrary-base-change square and diagonal identification. The
upstream-name index was also checked. No new notion was defined in place of an
existing one. The current blueprint factors proof (1), read at
`literature/blueprint/latest/`, is the source of the two statements.

Validation: the module is compiled only through scompile.py. The first run found
that LocallyOfFiniteType X.g requires installing the published implication from
SmoothOfRelativeDimension to Smooth. This is now done in normalIntegration.
No statement correction, disputed statement or missing dependency interface.


## Returned delivery repair

The immutable head 299f163ea8cd was returned for H2 only. The maintainer accepted
its mathematics and asked to replace theorem-node ownership of plain definitions.
The original Lean module is retained byte-for-byte. Current main was read before
the repair: its item has no Lean record, and the two requested existing definition
owners are already landed. The delivery wrapper rebases this sandbox onto current
main; no direct Git command or edit in the shared clone was used.

* `lem-pur-section-etale-restriction-coherence` is removed from stmt_deps.
  New `def-pur-section-restriction-data` records exactly `Pair`, `BaseChange`,
  `invariant`, `normalPair`, `delta` and `baseComparison` in the published
  `Sheaf.Paper.PuritySectionEtaleRestriction` module. Pair and BaseChange include
  their full geometric and section equations, delta is the uniquely determined
  DNC arrow, and baseComparison is the actual counit-defined exchange.
* `lem-pur-diagonal-dnc-chart-normalization` is replaced in stmt_deps by existing
  `def-pur-diagonal-dnc-chart-data`, whose declarations explicitly include
  `chartDiagonalAlpha` and `chartSectionEtaleRestriction`.
* `lem-trf-finite-ring-section-deformation` is replaced in stmt_deps by existing
  `def-pur-finite-ring-section-data` for `coneBundleIso`, `coneBundleIso_spec`,
  and `bundleSectionAdjoint`, together with new
  `def-pur-bundle-integration-orientation` for `bundleOrientation`, `geometry`,
  and `bundleAdjoint_isIso`. The latter names both typing facts rather than
  silently assuming geometric or invertibility data. Its bundle orientation
  remains the inverse of the actual zero-section integration adjunct.
* `lem-pur-diagonal-orientation-refinement` is replaced in stmt_deps by new
  `def-pur-section-tate-pullback`, owning `OrientationRefinement.tate` in the
  published refinement module. The canonical ordered Tate comparison imposes
  no new geometric hypothesis.
* The original eleven proof_deps are retained exactly. No original statement
  dependency is dropped: only the four additions from the first returned
  delivery are replaced. The original statement, source, proof steps and all
  unrelated node fields remain unchanged. No statement_change is necessary.

## New nodes

`def-pur-section-restriction-data`: an existing:true ownership record in
`Sheaf.Paper.PuritySectionEtaleRestriction` for the six section-pair and canonical
comparison declarations above. Its source is factors proof (1), with the DNC
invariance uniqueness statement and orientation-charts Step 3. Its statement
introduces every pair field, the Cartesian square with section compatibility,
the actual normal pair, the unique normalized delta, and the counit-normalized
base comparison. Its main signature is the published `structure Pair` verbatim.
The finite setting, normal cone, DNC uniqueness, finite site comparison, and
co-smoothness conventions are cited in stmt_deps. No coherence theorem is
asserted. The new record owns existing data and does not copy any declaration.

`def-pur-section-tate-pullback`: an existing:true ownership record for
`WeilConjectures.PurityFiniteSetting.OrientationRefinement.tate` in
`Sheaf.Paper.DiagonalOrientationRefinement`. Its factors proof (1) source is the
Tate pullback identification for the two orientations. The statement specifies
pullback commuting with nu*, followed by the ordinary coefficient pullback of
the ordered shifted Tate tensor and the normalized roots/pure-tensor transport.
Its signature is copied verbatim. Existing owners of the site comparisons,
vector-integration coefficients and twist transport are cited; no refinement
conclusion or vector orientation theorem is included.

`def-pur-bundle-integration-orientation`: an existing:true ownership record in
`Sheaf.Paper.FiniteRingSectionDeformation` for `bundleOrientation` and the named
geometric and invertibility typing facts `geometry`, `bundleAdjoint_isIso`.
The source is factors proof (1), together with the local-construction and final
orientation portions of sk-thm-dnc. Its signature is `def bundleOrientation`
verbatim, with all finite-ring, invertible-exponent, Noetherian, and locally-free
hypotheses. The statement also records geometry's exact smooth, separated,
quasi-compact, compactifiable closed-section hypotheses. It uses the existing
Geometry proposition and bundle adjuncts, integration, zero section, and actual
Brown adjunction via their existing definition owners. The return expressly
requested ownership for these typing facts. Neither a new proof obligation nor
an arbitrary replacement orientation is introduced.

All three records have the item's chapter and unit, ancestor
`det-sp-purity-bc-factors`, the item prepended to blueprint.from.via, and
import_flags=[]. Their searches were run through msearch.py on 2026-10-24 UTC:
LeanSearch and LeanFinder on the plain-language descriptions of smooth section
pairs/base comparison, canonical shifted Tate pullback, and the inverse bundle
integration adjunct; grep on the exact helper names returned zero Mathlib hits.
The raw search records are included verbatim in each node's mathlib_searches.
The semantic results concerned manifolds, generic categorical pullbacks/shifts,
normalization or Kaehler sections, and none gave these constructions. Exact-name
rg searches in dag/nodes found only the theorem owners for the newly recorded
names; the finite-ring and diagonal-chart definition records were reused rather
than duplicated. Searches in lean/WeilConjectures found no exact declaration;
lean/Sheaf located the published modules above. blueprint_refs.py searches for
section invariant, Tate pullback and bundle orientation found no separate
ownership record for these names. The canonical DNC pull/site comparisons and
vector integration coefficient/adjunction/twist constructions already have
owners and are cited by the new records.

Edge cases for the repair records: Pair allows rank zero and empty schemes;
BaseChange has no flatness or nonemptiness hypothesis; delta retains separated
finite-type aB, while invariant and baseComparison retain their published
finite-type hypotheses. Tate pullback allows any h and all d. The bundle
orientation permits every finite commutative A killed by positive invertible N,
all d including zero, and empty Noetherian S. Geometry retains exactly its
published compactifiability hypothesis, which normalIntegration derives from
the original finite-type setting. Universes are Scheme.{u}, coefficient
Type (u+1), and the already published small-site categories throughout.


## Second reading by NK

This is the dispatched worker's repair check; the maintainer supplies the
independent review, as required by this dispatch (no other agents were started).
I reopened the node, the complete Lean file, the three new records and their
published declarations. I checked the theorem binders and both conclusions
against every original hypothesis and clause above. The H2 repair changes no
Lean text and no mathematical statement. The four former theorem ownership
citations are replaced by two existing and three new definition owners. The
original proof_deps list is retained verbatim. Each newly owned declaration has no existing
DAG definition owner. The original stmt_deps are retained, the statement/proof
are identical to current main, and the resulting statement graph is acyclic.
The finite-ring record includes the geometry and adjunct-isIso typing facts,
with their precise hypotheses; the Tate record includes no extra scheme
hypothesis. The actual normal-cone comparison still preserves projection and
zero section. Compile via scompile.py is clean (22.7 s library file after
private dependency preparation); no error or warning was reported.


## H7 repair of db73d92b38f1

The maintainer's second return supersedes its earlier request to add the four
theorem owners to proof_deps. Restored the item's exact eleven-entry base list,
in its original order, and removed the item lean.note clause claiming that those
four theorem owners remain proof dependencies. The proof_deps list now equals
both the explicit list in the return and current main. The item's statement,
proof steps and all accepted stmt_deps are unchanged. The three accepted
existing:true definition records are unchanged. In particular their published
geometry and bundleAdjoint_isIso typing facts remain declarations of
lem-trf-finite-ring-section-deformation's module; nothing is moved or redeclared.
The Lean file is unchanged from the accepted mathematical content of 299f and
db73. No statement correction or statement_change is introduced. This repair is
the requested proof metadata restoration, rather than an unchanged re-push.

Rechecked the exact proof list against current main and checked that the item
statement and proof are identical to main. The only item changes in this repair
are proof_deps, the specified lean.note clause, and lean.date (UTC delivery date).
The report's earlier descriptions of the proof_deps were updated accordingly.
Compilation, dry run and delivery use only the authorized wrappers.
