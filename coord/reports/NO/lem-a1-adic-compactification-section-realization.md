## Worker report

This repairs the substantive normalization defects returned on immutable head
7cdc9d8e82e9. It replaces free mate aliases by equations involving the actual
point fibre, cohomology objects, continuous derived adjunctions, universal derived
units and finite Roos projections. The main theorem remains a statement with
`sorry`; all definitions have data. The source statement and proof of the item
are unchanged. Its stmt_deps gains the ten definition nodes listed below.

Hypotheses and clauses of the item are rendered as follows.

- The finite-field datum and prime condition are the explicit D, l, Fact l.Prime
  and hl binders. Coefficients E have Field, Algebra Q_l E and FiniteDimensional
  binders. FiniteFamily quantifies over every such E, and every coefficient
  embedding, including identities. The valuation ring, uniformizer and finite
  quotients are exactly Padic.coefficientExtensionIntegers,
  coefficientExtensionUniformizer and coefficientExtensionRing; n indexes
  exponent n+1, covering every positive quotient. Omega has its own universe v and IsAlgClosure
  binder; no equality with the scheme universe u is assumed.
- A separated finite-type k-scheme is exactly Geometry D = PerAdic.Base D.k.
  Every open-map binder has IsOpenImmersion, QuasiCompact and IsOver k. Properness
  appears only in CompactificationModel, FiniteProper, FiniteScalarProper and
  CommonProper, and their family fields. compactification D j has middle scheme
  T, open arrow j, and proper structure arrow b:T->Spec k.
- The categories are sfIntegralConstructibleCategory,
  sfRationalConstructibleCategory, sfRationalHeart and sfCommonStageHeart.
  FiniteAt.integral fixes J on integral representatives through purCoefficientModel
  and pbcDerivedExtend. The realization family fixes the actual inverse-limit
  coefficient sheaf through its integralIso and normalized reduction maps, and
  rationalCoefficientSheaf is the continuous rational coefficient sheaf.
  It does not substitute a discrete-coefficient etale category.
- FiniteOpen.tower identifies shriek on all arrows with the specified rational
  compact-support action at (j,id_T). Its additive, linear, limits and colimits
  fields give exactness on the heart. CommonOpen has the corresponding fields and
  stage comparisons for every represented object and arrow.
- FiniteOpen.sheafification is the actual proEtaleRingedExtensionByZero of
  continuousModuleToSlice. slice_coefficient and slice_normalized fix its
  coefficient identification. inverse_image and adjunction_unit identify the
  actual module pullback and the actual extension-by-zero adjunction unit.
- The invertible open unit is FiniteOpen.open_unit. FiniteOpen.inside uses exactly
  sfAdicRationalFiber at x and x composed with j. outside requires range(x) to lie
  in the complement and asserts IsZero for that same fibre. CommonOpen supplies
  the corresponding SfAdicCommonFiberSpec comparisons.
- The actual ordinary H0 objects are fixed by FiniteAt.ordinary_obj to
  rationalOrdinaryCohomology. PointSection.one_normalized sends the specified
  point-unit class to the actual tensor 1 tensor 1 through
  pointRationalNormalization, the single-complex comparisons and cohomology
  transport. PointSection.evaluation fixes its H0-to-Hom equivalence by evaluation
  at this class. PointSection.unit_normalized fixes realization of this unit by
  coefficientUnitArrow; its CoefficientUnitModel is fixed on ordinary sections by
  1->1 and tensor multiplication.
- FiniteAt.image is an identification of the actual rationalImage with the actual
  continuous derivedPush of J(F). image_integral fixes its arrow by the precise
  integralImage Roos vertex, ImageModel.projections, IntegralPushModel's
  identity-on-sections transport and right-derived-unit representative equation,
  and ContinuousRational.DirectImage.projection. These fields use direct_image.
  They are not arbitrary equivalences given a suggestive name.
- FiniteAt.ordinary_hom_transpose pins ordinary_hom explicitly: ordinary_obj H0
  cast, point.hom, point.J.map, image.hom, the inverse of
  direct_image.adjunction.homEquiv, and unit_pull.inv. unit_pull_normalized and
  unit_module_one fix the last unit identification by actual pullback counit and
  multiplication. evaluation_one then pins ordinary_sections by this Hom map and
  the actual coefficient section 1. There is no point_fibre or point_fibre_eq.
- FiniteProper.compact_obj is exactly rationalCompactCohomology at
  compactification D j. compact_point starts from the actual
  sfRationalCompactSupportValue underlying rationalCompactSections, rather than
  from another copy of ordinary_obj. CompactificationModel.projections fixes its
  integral comparison by equality of the actual finite projection adjuncts.
  FiniteIdentityImage fixes the identity pushforward in (j,id_T) on ordinary
  sections and right-derived representatives. compact_point_normalized transports
  this specified comparison through J and the actual ordinary-image comparison.
  compactification_h0 is its point-fibre H0 map. compactification_hom then pins
  hom to ordinary_hom after compactification; neither is free.
- realizedOpenInverseUnit constructs realization of the inverse open unit using
  the recorded heart, module-pullback and open-adjunction comparisons.
  derivedCompactOrdinaryArrow applies Rb_* to its adjunction transpose and then
  derivedPushCompositor. compactOrdinaryArrow adds the actual structure-morphism
  equality j composed with b = a_U. None of these definitions mentions hom,
  ordinary_hom, restrictionHom, or comparison. FiniteProper.comparison_derived_map
  requires comparison to realize this very arrow. comparison_canonical is a
  separate equation asserting the desired Hom restriction formula; it no longer
  defines comparison by that formula.
- natural_hom, natural_sections and FiniteProper.natural express naturality.
  FiniteOpen.ordinary_restriction_hom gives ordinary open restriction.
  FiniteScalar fixes actual completed coefficient extension, tensor-unit ordinary
  Hom and continuous sections comparisons. FiniteScalarOpen preserves extension,
  restriction, the coefficient unit and the actual open adjunction unit.
  FiniteScalarProper.hom, compactification and comparison preserve the now
  normalized maps on every 1 tensor x.
- CommonAt.ordinary_obj is adicOrdinaryCohomology; its actual underlying inclusions
  and ordinary_stage_normalized and hom_stage equations carry the normalized
  finite Hom map to Omega. inclusion_obj pins inclusion to the literal finite
  pair, underlying_normalized fixes its comparison to equality transport, and
  ordinary_stage_normalized fixes the stage map to the actual tensor-unit map
  on the recorded ordinary cohomology objects. CommonProper.compact_obj is adicCompactCohomology.
  compact_stage_normalized pins the stage map to the actual tensor-unit map
  on the recorded compact cohomology objects. compact_stage, hom_stage,
  compactification_stage and
  comparison_stage carry all three normalized finite maps to common stages.
  commonLinear is the existing finite-representative scalar action transported
  along closureEquiv. The common functors and natural comparisons include all
  common-stage morphisms, not just an objectwise family.
- The theorem asserts existence of FiniteFamily and CommonFamily. It asserts no
  injectivity or support criterion for a section.

Dependency interfaces used include OrdinaryCompactCohomology.rationalImage,
rationalOrdinaryCohomology, rationalCompactSections and rationalCompactCohomology;
FiniteCoefficientPoint.pointRationalFibre and pointRationalNormalization;
PointSectionsScalarExtension.pointCompletedSections and
pointModuleDerivedRationalization; SfConstructibleHeart.sfRationalHeart and
sfCommonStageHeart; CompactSupportFiniteAction.sfCompactSupportFiniteIntegralFunctor
and sfCompactSupportFiniteReductionIso; IntegralRationalQbarCompactSupport's actual
compact-support values and chosen reductions; AdicHeartIntrinsicFibres' actual
rational/common fibres; CompletedCoefficientPresentationTransport.purCoefficientModel;
ContinuousRationalDerivedRealization.Family; RationalDirectImageRealization's
Ordinary, projection and derivedPush; and the pro-etale ringed open-slice extension
and completed extension-zero comparisons. These declarations and their full
interfaces are reused, rather than privately copied.

Edge cases checked at statement level: empty U and T; j an identity or a proper
open subset; disconnected schemes; zero sheaf; geometric points on either side
of the complement; identity coefficient embeddings and ramified finite
extensions; Omega in an independent universe. No properness, connectedness or
nonemptiness was added to ordinary section realization. The comparison formulas
still apply for the identity open immersion. No STATEMENT-DISPUTED issue or
source-statement correction is claimed.

Searches: the retained LeanSearch and LeanFinder queries searched finite/common
adic compactification section data and found unrelated completion/topology
notions. The repair additionally searched canonical point-fibre H0/Hom and
ordinary direct-image Roos normalizations with LeanSearch and LeanFinder.
Matches concern Hom complexes, group cohomology and unrelated algebra; no exact
package was found. rg searched the DAG, Mathlib, upstream WeilConjectures and
lean/Sheaf for PointSection, CoefficientUnitModel, IntegralPushModel and
FiniteIdentityImage; matches concerned unrelated point sections. blueprint_refs
found no canonical-point-section node. Full outputs are recorded in the new
canonical-model node.

The theorem module imports only its statement data; proof-plan references are
docstrings and do not require importing all proof prerequisites. This removes unnecessary
proof prerequisites. The continuous-realization dependency still reaches the
coefficient-system modules, whose published interface repairs are described below. Validation uses scompile.py and the deliver2.py dry run; final results are recorded below.

## New nodes

`def-a1-adic-section-canonical-models` owns AdicSectionCanonicalModels.lean.
It defines the normalized point-unit/H0/Hom model, coefficient-unit contraction,
representative ordinary push transport and precise Roos comparison. The exact
cohomology transport helper allows different localization Hom universes, which
is necessary for the small point fibre and larger section modules. Source:
BS 6.7.2 and 6.8.14--15 and the canonical derived-unit constructions. The searches
above found no existing package. This node asserts no existence.

`def-a1-finite-adic-compactification-section-data` owns
FiniteAdicCompactificationSectionData.lean. It states the finite diagrams,
including the new canonical-model equations, literal compactification projection
comparison, independently constructed derived comparison arrow, and finite
scalar compatibilities. Source: BS 6.8.14--15 and Milne 18.1, 18.3(b).
Its component notions are existing declarations; the searched combined data
package is new.

The finite data use five explicit component nodes, each with the same sources
BS 6.7.2, 6.8.14--15 and Milne 18.1, 18.3(b):

- `def-a1-finite-adic-section-realization-core` owns
  FiniteAdicSectionRealizationCore.lean: the continuous realization, coefficient
  unit, ordinary H0 objects, actual direct-image adjunctions, and the derived
  direct-image compositor and compact-to-ordinary arrow construction.
- `def-a1-finite-adic-image-normalization` owns
  FiniteAdicImageNormalization.lean: the four specific ordinary-image arrows and
  their composability and equality in the arrow category, including endpoints.
- `def-a1-finite-adic-ordinary-section-data` owns
  FiniteAdicOrdinarySectionData.lean: FiniteAt, whose Hom equivalence is the
  normalized actual derived adjunction transpose, and the section of its unit.
- `def-a1-finite-adic-open-section-data` owns FiniteAdicOpenSectionData.lean:
  the finite open adjunction, actual compact-support action, sheafified continuous
  extension, ordinary restriction, and the specified adic fibres.
- `def-a1-finite-adic-proper-section-data` owns FiniteAdicProperSectionData.lean:
  the normalized integral compactification projections and FiniteProper's actual
  compact H0, compactification Hom, and independent derived comparison equations.

The saved searches for these component notions found no existing interface;
each node records LeanSearch, LeanFinder and grep outputs. They factor the
finite data definition into its mathematical components without dropping any
normalization obligation.

`def-a1-common-adic-section-data` owns CommonAdicSectionData.lean. It defines
ordinary common-stage data on the actual common heart with the finite-stage
normalization equations. Source: BS 6.8.14 and common-stage coefficient descent.
The searches found no existing package; the actual categories and scalar action
are reused.

`def-a1-common-adic-open-section-data` owns CommonAdicOpenSectionData.lean.
It defines common-stage open extension with the actual coefficient action,
finite-stage adjunction comparisons, restrictions and specified adic fibres.
Source: BS 6.8.14--15. The searches found no existing package.

`def-a1-common-adic-compactification-section-data` owns
CommonAdicCompactificationSectionData.lean. It defines CommonProper and CommonFamily,
including finite-stage equations for compactification, Hom and comparison.
Source: BS 6.8.14--15 and Milne 18.1, 18.3(b). The searches found no existing package.

## Second reading by NO

This is a self-check, not an independent second reading. No other worker was
started; the maintainer performs the independent immutable-head review.

H3/H12: the repaired ordinary equation now explicitly invokes direct_image's
actual adjunction homEquiv and the point-fibre Hom map. The latter's unit and
realization are fixed by ordinary coefficient multiplication and actual derived
counits. rationalImage is identified with derivedPush by an integral representative
and actual Roos projection comparison. Compact Hom and compactification are fixed
through the actual rationalCompactSections value at (T,j,b), with finite
projection normalization. comparison is fixed by an arrow constructed without
restrictionHom; the restriction formula is an independent equality. These maps
are propagated through finite scalar and common-stage equations. Redundant
point_fibre fields and the unnormalized mate aliases are deleted. All four
original definition-node statements are updated.

H11: this report identifies the exact equations carrying each normalization. It
makes no claim that a field name, comment, or bare equivalence alone gives
canonicity. The previous claims based on free aliases are withdrawn.

## Published dependency repairs reused

The saved packet supplied copies of `CoefficientRingedSequenceSite`,
`CoefDerivedSystemEvaluationCalculus` and `RingedSliceEvaluationTranspose` to
repair sheafification inference. The current published sources now carry their
own repairs. The first two already disable the specialized successor-universe
instance; the current slice source uses the general site-Abelian sheafification
instances and updated transparency settings. This retry drops the stale private
overrides and their three lean-only node copies, and uses those published sources.
No declaration or mathematical statement from those dependencies changes in this
delivery. This also avoids invalidating their entire downstream compilation closure.

## Published derived-operations dependency

The current published DerivedPullbackTensorHom source already includes the maintainer's
elaboration repairs. Its review also records that the earlier private instance-cache
variant did not improve compilation. This retry drops that stale dependency override
and its node copy, and uses the published interface. The substantive section-normalization
repairs are retained.

## Compilation repair and canonical-map self-check

The initial dry run failed because FiniteProper's expanded
compact_point_normalized equation timed out at 60 seconds. Prefix probes isolated
that equation. Naming the expanded predicate alone still timed out. The repaired
CompactPointNormalized retains the same equation using five named component arrows,
four intermediate objects, and equality in Arrow for each component (so both
endpoints and the arrow itself are fixed). The final equation uses their abstract
composable endpoints. This removes repeated conversion through large coefficient
objects; the complete proper module compiles in 8.8 seconds. No theorem was added.
The realization-family parameter is explicit in compactIntegralTransport.

The subsequent full compile found an underconstrained scheme in the finite scalar
section tensor, a geometric compactification shadowed by the common record field,
and a line-broken compactification projection. Explicit scheme parameters, the
qualified geometric function and FiniteProper.compactification fix these without
changing any objects or equations. All module declaration inventories and verbatim
signatures were regenerated from their source files.

For H3/H12, I reread ordinary_hom_transpose, ImageNormalization,
CompactPointNormalized, compactification_h0, compactification_hom,
comparison_derived_map, derivedCompactOrdinaryArrow and derivedPushCompositor.
The actual direct_image adjunction appears in the ordinary transpose and in the
independent compact-to-ordinary arrow. Its compositor is the mate of the given
pullback compositor. The proper H0 map starts from rationalCompactCohomology's
actual compact-support object at (T,j,b). CommonAt's normalized ordinary_stage
and CommonProper's normalized compact_stage, hom_stage, compactification_stage
and comparison_stage propagate these maps to every finite-stage representative.
FiniteScalar.hom and FiniteScalarProper.hom/comparison/compactification carry them
along every coefficient embedding. No point_fibre field remains. The four
original definition-node statements describe these equations; the added finite
component nodes and canonical-model node spell out their constructions.

For H11, the second reading remains explicitly a self-check, as the dispatcher
forbids starting another agent. The independent maintainer review remains required.
The source rereading checked BS Proposition 6.8.14 and Remark 6.8.15 in the local
PDF (printed pages 61--62), and Milne Definition 18.1/Proposition 18.3(b).
The construction uses continuous coefficient sheaves and the canonical ringed
adjunction, exactly as those sources and the item's nine-step proof require.

All twelve delivered files passed the per-file server compile in the third dry run
(expected sorry warning only). Preflight then identified five newly added finite
component nodes whose blueprint.from.via omitted the existing support-section
ancestor. Their provenance chains now match the item's complete ancestry.

## Repair of return L (immutable head 0bda8c757340)

Removed the unused Galois-lisse compatibility module and its new definition node,
the corresponding item stmt_dep, and the obsolete report paragraph. The saved
packet initially passed the required dry run (5166868d05), but that automatic
check does not supersede the maintainer's substantive return. Current
AdicHeartPullbackFibres imports GaloisLisseRepresentations without the retired
compatibility path. GaloisLisseFiniteData belongs to the published
GaloisLisseCorrespondenceData module and def-pod-galois-correspondence-data-e4;
no delivered module imports or uses the removed alias. The ten mathematical
definition nodes and all section-normalization equations are retained.

The second reading remains a self-check. The return's advisories are retained:
the open unit and comparison admit a common scalar through the extension,
inverse-image and ordinary-pull identifications (the restriction equation is
invariant), and inside-fibre identifications assert Nonempty isomorphisms.
There is no claim of an independent second reader.

Post-repair validation (2026-10-19): scompile.py compiled each of the eleven
delivered modules separately, including its library module, with exit status 0
and no errors or warnings. The live --source reading confirms the retired import
is absent. Comparing the item with the current published node shows changes only
in lean and stmt_deps, with ten new definition dependencies and no published
dependency removed. There is exactly one sorry, the main theorem; all retained
definition data and normalization equations are unchanged by return-L repair.
