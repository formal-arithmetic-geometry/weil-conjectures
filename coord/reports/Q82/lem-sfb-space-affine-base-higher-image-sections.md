## Worker report

Item: lem-sfb-space-affine-base-higher-image-sections. The new module is
Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections. Its sole theorem is
AlgebraicGeometry.AlgebraicSpace.exists_affineBaseHigherImageSections_iso, with proof `sorry`.
The five other declarations are explicit abbreviations and a normalization predicate for this
same comparison. There is no selected unknown object and no postponed definition data.

Source read: literature/stacks-project/spaces-cohomology.tex, lines 238--265, Tag 08EX,
lemma-quasi-coherence-higher-direct-images-application. Its proof first replaces Y by V;
our affine Y is exactly this case V=T. Also read Tag 0720, lemma-higher-direct-image.
No mathematical statement correction is needed; the repair changes only dependency ownership.

Hypothesis and clause matching:

- A commutative ring: `(A : Type u) [CommRing A]`, with arbitrary universe u.
- The affine scheme T=Spec A: `(Y : Over S) (a : Y.left ≅ Spec (.of A))`.
  An isomorphism to Spec A retains the ordinary A-coordinate on sections, through the
  existing Gamma-Spec isomorphism. The arbitrary ambient scheme S merely presents the
  category of spaces. Every space over Spec A is covered by choosing S=Spec A and Y=id.
- The algebraic space Z and map p: `(X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)`.
  This is an arbitrary morphism, without representability or a scheme assumption on X.
- Quasi-compact: `hqc : IsQuasiCompactPresheafMap f.hom.hom`, the recorded affine-test
  characterization using a quasi-compact etale scheme atlas of each affine fibre product.
- Quasi-separated: `hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)`.
  The diagonal is the actual presheaf fibre-product diagonal, not a closed-immersion test.
- Every quasi-coherent module M on the original small etale site: the domain of the
  comparison functors is `X.QCoh`, the recorded full subcategory using Mathlib's
  `SheafOfModules.IsQuasicoherent`. Its inclusion is followed by the recorded restriction
  equivalence `X.smallModuleRestriction` with the small affine etale model.
- Every integer q>=0: `∀ q : ℕ`; negative degrees are not part of this node's claim.
- H^q(Z,M): `affineBaseModuleCohomology A Y a X f q` is the inclusion/restriction followed
  by `(affineScalarSections A Y a X f).rightDerived q`. Global sections is the existing
  Hom(O,-) functor with the actual pulled-back A-action.
- Gamma(T,R^q p_*M): `affineBaseHigherImageSections A Y a X f q` uses
  `(smallModuleDirectImage f).rightDerived q` followed by ordinary affine scalar sections
  on `schemeSpace Y`. The small direct image is precisely the conjugate of the recorded
  chart-limit `moduleDirectImage f` through the module restriction equivalences.
- Both derivations are in ALL module sheaves: rightDerived has domain `X.SmallModules`,
  never QCoh. The QCoh inclusion is composed only after constructing the derived functor.
  Mathlib rightDerived is defined using injective resolutions indexed by the natural numbers.
  Enough injectives follows from the already recorded Grothendieck theorem; no resolution
  existence, acyclicity or derived-category instance is an added hypothesis.
- Canonical natural isomorphism: `e q` is an isomorphism of functors on X.QCoh, valued in
  ModuleCat A. Thus it includes naturality in every module morphism, in particular scalar
  multiplication. `AffineBaseHigherImageSectionsNormalization ... e` fixes the actual
  Leray edge on EVERY module injective resolution I. The first equation specifies c by its
  composite with the cycles inclusion, using `affineSectionsComposition.inv`. The second
  says exactly that the edge takes a global cocycle to its cohomology-sheaf section.
  Sections preserve kernels, so c is the canonical cycles identification; the homology
  quotient in ModuleCat is epic. Consequently the formula determines the edge and rules
  out an arbitrary unrelated isomorphism. `isoRightDerivedObj` fixes the resolution
  comparisons. At degree zero this formula is the ordinary normalized sections compositor.
- No Noetherian, finite type, coherent, flat, proper or separated hypothesis occurs.

Dependency declarations used (source signatures and docstrings read):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, EtaleSite, structureSheaf, Modules;
  these use the fppf-sheaf/representable-diagonal/etale-atlas definition.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh, built from the unchanged
  Mathlib predicate IsQuasicoherent.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: ModuleDirectImageModel,
  moduleDirectImageModel, moduleDirectImage and their chart-limit normalization.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: SmallModules,
  smallModuleRestriction, smallModuleEquivalence. Actual affine-chart restriction is an
  equivalence and leaves rings and coefficient universe unchanged.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: smallModuleDirectImage, its
  additive instance and the interpretation of the derived direct image.
- Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections: affineScalarSections and its additive
  instance, using affineChartScalar and affineGlobalScalar for the genuine A-action.
- Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors: affineSectionsComposition,
  uniquely specified by AffineSectionsCompositionNormalization on every chart projection.
- Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal: IsQuasiCompactPresheafMap, owned by
  def-sfb-space-quasi-compact-presheaf-map, and diagonalPresheafMap, owned by
  def-sfb-presheaf-map-separated-diagonal. Both owners are live existing:true definition
  nodes. Only these definitions are used; quasiCompact_separated_etaleLocal is not used.
- Mathlib.CategoryTheory.Abelian.RightDerived: Functor.rightDerived,
  InjectiveResolution.isoRightDerivedObj; the actual injective-resolution construction.
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian:
  SheafOfModules.isGrothendieckAbelian, registered as an instance exactly as in the
  recorded Leray module. Mathlib's intrinsic Abelian structure is unchanged.
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives: the intrinsic
  enoughInjectives instance, giving injective resolutions for the small module category.

Recorded, already stated proof dependencies are imported privately:
AlgebraicSpaceHigherDirectImageQuasiCoherent.isQuasicoherent_higherDirectImage_of_quasiCompact_quasiSeparated
(with the declaration in AlgebraicGeometry.AlgebraicSpace),
SchemeZariskiEtaleQuasiCoherentEquivalence.scheme_zariski_etale_quasiCoherent_equivalence
(in AlgebraicGeometry.Scheme.Modules),
WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift with
AlgebraicGeometry.Etale.etale_affine_qcoherent_ulift,
Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence with
CategoryTheory.exists_ringedSite_leray_spectralSequence,
Sheaf.AlgebraicGeometry.AtlasEtaleRestriction with the existing enlarged ringed model,
and Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections with
AlgebraicGeometry.AlgebraicSpace.space_chart_limit_enlarged_sections.
The proof prerequisite lem-sfb-module-resolution-derived-presheaf-comparison currently
has neither a Lean record nor an upstream audit declaration; therefore there is no module
to import for it yet. It is not needed to TYPE this theorem. Its mathematical use is
retained explicitly in the proof docstring, for the maintainer's future proof-import update.

The only DAG changes beyond lean are adding six already landed definition interfaces:
def-sfb-space-small-ringed-model, def-sfb-space-derived-module-calculus,
def-sfb-space-affine-global-sections, def-sfb-space-affine-sections-compositors,
def-sfb-space-quasi-compact-presheaf-map, def-sfb-presheaf-map-separated-diagonal. These are used directly above, not new notions.
A dependency traversal of both statement and proof edges confirmed that none reaches this
item, so these additions introduce no dependency cycle. No new/dependency modules are needed.

Edge cases checked before and after writing: q=0 is included and has the augmentation/ordinary
sections normalization; M=0 gives zero modules; A the zero ring gives an empty affine base
and zero groups; f=id gives the usual affine quasi-coherent acyclicity; X empty is permitted;
non-Noetherian A and quasi-coherent modules with infinitely many generators are unrestricted.
No universes are equated to fit a specialized API: the small affine model has object,
morphism and section universe u, while the original scheme-chart site is retained by
its equivalence. `autoImplicit false` forbids undeclared variables.

Searches for existing statements (2026-10-24):

- msearch.py leanfinder, query "For a quasi compact quasi separated algebraic space over an
  affine scheme, quasi coherent module cohomology is global sections of its higher direct
  image"; repeated with "Quasi coherent algebraic space affine base higher direct image
  global sections Leray": eight scheme inverse-limit/affine global-function hits, no match.
- msearch.py leansearch, query "cohomology of a quasi coherent module on an algebraic space
  over an affine scheme equals sections of the higher direct image": eight hits on
  IsQuasicoherent and its local-presentation data, no affine algebraic-space comparison.
- msearch.py loogle, query "Functor.rightDerived, InjectiveResolution.isoRightDerivedObj,
  SheafOfModules.sections": zero hits, unknown identifier Functor.rightDerived in the
  external index. Read the actual pinned RightDerived source instead.
- msearch.py grep, query "leray|[Hh]igherDirectImage|[Gg]lobalSections" in
  CategoryTheory/Sites: six hits on ordinary GlobalSections; no theorem for spaces.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and
  "affine.*higher.*sections|higher.*image.*sections": supporting mentions in space
  finiteness/infinitesimal arguments; no implementation of this node. Read the nearby
  WeilConjectures.AlgebraicGeometry.AffineCohomologySectionEquiv and
  WeilConjectures.AlgebraicGeometry.AffineOpenHigherDirectImageSectionsIso: both concern
  SCHEMES and Zariski modules/opens and cannot replace the arbitrary algebraic-space
  small-etale statement. Existing scalar sections and their compositor are reused.
- rg in Mathlib, WeilConjectures and Sheaf for all chosen declaration names: no collisions.

Validation: scompile.py compiled both sandbox and library module modes cleanly; the final
header with explicit public statement imports also passed (9.1 s sandbox, 4.2 s library).
No warnings other than the permitted sorry warning. No library/global build was run.
The sole sorry matches this item and has the full four-step source proof in its docstring.
No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q82

I reopened the node and module for a separate checking pass. This is the worker's second
pass; no second agent was started, as the dispatcher explicitly forbids it. Independent
mathematical review remains the maintainer's delivery review.

I checked A/CommRing, the affine target isomorphism, arbitrary space X and morphism f,
quasi-compactness and the quasi-compact diagonal, QCoh as the full original module
subcategory, all q>=0, and both sides of the displayed comparison against the expressions
listed above. The QCoh inclusion is outside derivation, so the category is correct.
I checked the direction of the compositor in the cycles equation: source sections ->
sections after direct image is affineSectionsComposition.hom, so the map FROM target
cycles TO source cycles correctly uses its inverse. The last equation has the same
orientation as the recorded Leray cocycle formula and uses the canonical resolution
comparisons on both sides. A natural iso, rather than a bare existence of objectwise
isos, supplies the stated naturality. The normalization eliminates arbitrary choices.
No mathematical mismatch was found. I added explicit public imports of the recorded
base interfaces before the final compile; no statement change was made.


## Repair of return H2 (2026-10-24)

The returned immutable head was 96db718758bb. The saved packet still cited
lem-trf-space-qc-separated-etale-local in stmt_deps merely for two definitions.
The initial dry run passed (commit 7b125df88ca), but that mechanical success did not
resolve the independent review's H2 finding.

Replaced that theorem-node dependency with the live existing:true definition nodes
`def-sfb-space-quasi-compact-presheaf-map` and
`def-sfb-presheaf-map-separated-diagonal`. Read both current node records and the
full definition signatures/docstrings at SpaceQCSeparatedEtaleLocal.lean lines 38
and 49. They own exactly IsQuasiCompactPresheafMap and diagonalPresheafMap, respectively.
The latter owner also defines separatedness, but this item uses only its diagonal:
hqs is quasi-compactness of that diagonal, with no closed-immersion assumption.
No conclusion of quasiCompact_separated_etaleLocal is used.

The item's TeX has no bracket citation to the removed theorem, so there is no such
statement bracket to replace. Its existing TeX, mathematical content and Lean signature
are retained exactly; no statement_change is needed. No dependency node or Lean file
is changed. Against current main, stmt_deps only gains the six already landed definition
nodes listed above; none of main's original four dependencies is removed. This is the
addition of landed definition owners expressly allowed by brief-stage2 section 5.

Self-check: the hqc and hqs expressions still use the exact two owned declarations;
all other clauses, normalization, source proof and edge cases are the previously reviewed
ones. The repair creates no new notion, extra theorem hypothesis, or proof dependency.

Repair validation: scompile.py passed again on 2026-10-24 in both sandbox mode
(35.2 s) and library mode (27.3 s), with no compiler messages or warnings.
The self-check compared the repaired node against current main: only lean and stmt_deps
differ, all added dependencies are landed definition nodes, and the mathematical statement
and recorded Lean signature remain exact.
