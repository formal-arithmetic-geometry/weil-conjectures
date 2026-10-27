## Worker report

Q68 states `WeilConjectures.IntegralSupportNormalization.integralSupportFunctorNormalization`
in `Sheaf.Paper.IntegralSupportFunctorNormalization`. The conclusion is `Nonempty
(Normalization l E D i j)`: one coherent package of natural comparisons,
restricted adjunctions, normalization equations and preservation assertions.
The original mathematical statement, proof and proof dependencies are unchanged.
The landed system-realization dependency supplies the actual system functors.
The new definition node `def-sf-ordinary-integral-comparison-data` owns the
existing ordinary closed comparison definitions, without a duplicate declaration.

Source read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md`,
including its integral and rational support paragraphs, and the node's seven-step
proof with the Stacks source references. No repair note exists for this item.

Hypothesis and conclusion correspondence:

- The global geometric datum is `D : FiniteFieldDatum.{u}`; `_hl : l ≠ D.p`
  retains the different-characteristic hypothesis. `l : ℕ`, `[Fact l.Prime]`,
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` are exactly the prime and finite coefficient
  extension. Its integer ring and quotient rings are the existing Padic objects.
- `X.Over (Spec (.of D.k))`, locally finite type plus quasi-compact, and
  `IsSeparated (X ↘ Spec (.of D.k))` express separated finite type over k.
  `i`, `j`, their closed/open immersion instances and
  `_hcomplement : Set.range j = (Set.range i)ᶜ` retain the closed/open pair.
  Induced structures on U and Z, quasi-compactness of j and invertibility of l
  are package outputs, not extra hypotheses.
- `scalarReductionSource l E T` is modules over the recorded completed integral
  sheaf. `sfIntegralConstructible` and its full inclusion `.ι` are the published
  complete, uniformly bounded finite-constructible category. Our coefficient
  exponent `n+1`, for n natural, enumerates precisely the node's n ≥ 1.
- `openPull`, `closedPull`, and `closedPull_formula` identify the actual
  `constructibleIntegralPullback` with ordinary pullback. `closedPull_formula`
  fixes the inverse of the representative-normalized ordinary comparison.
  The ordinary adjunction equations and both strict-system equations fix the
  open identification. Per H3's explicit alternative, the unreferenced
  `pullOpen` and `pullClosed` package fields have been removed. The cited
  immersion normalization remains the proof input and owns `HasReductionInterval`;
  no detached comparison witness is included in the conclusion.
- J is literally `sfCompactSupportFiniteIntegralFunctor` for
  `Compactification.ofIsOpenImmersion j`, i.e. (j,id_X). I is literally
  `FrobeniusExchange.integralDirectImage`, with its already published full
  subcategory restriction `directImageFunctor`. The published reduction,
  system direct/open operations, sequence limit and evaluation comparison
  retain quotient transitions. No tower is reconstructed from independently
  chosen object values or unnormalized isomorphisms.
- `dj` and `di` are natural isomorphisms of functors into the ambient derived
  category. `dj_formula` fixes dj as the inverse published compact-support
  realization followed by `openIdentity`. The identity comparison is uniquely
  fixed on sections by identity base change, then derived. In particular this
  is the published actual reduction/limit unit normalization for (j,id).
- `closedReduction` uses the ordinary pullback comparison and the actual
  reduction counit. `closedLimit` is its right-adjunction conjugate.
  `closedAlpha` is the ordinary image of the actual completion unit followed
  by this comparison. `di_formula : di.inv = closedAlpha ...` fixes di as the
  required inverse. `closedProjection` explicitly identifies its nth
  projection through `sfDerivedRestrictionComparison` (scalar restriction
  commuting with direct image) and the normalized system evaluation mate.
- `openReduction` is the natural finite-reduction comparison with the finite
  compactification (j,id), which is finite ordinary open extension with its
  identity direct-image factor. `openProjection` fixes it by
  `sfCompactSupportFiniteReductionIso`, not an unspecified invertible map.
  `closedReductionComparison` asserts invertibility of the existing canonical
  `sfOrdinaryPushReduction` at each finite level. These are exactly the
  finite reductions j! N_n and i_* M_n (the latter is termwise by closed
  exactness, recorded in `closedModuleLimits` and `closedModuleColimits`).
- `openComplete`, `closedComplete` assert preservation of completeness on
  complete ambient objects. `openConstructible`, `closedConstructible` assert
  membership in C_X for inputs in C_U/C_Z. `openInterval`, `closedInterval`
  use the dependency's `HasReductionInterval` with the *same* arbitrary a,b
  for all finite reductions. Thus constructibility and the uniform interval
  are retained, not merely a separately chosen bound at each level.
- `limitShift`, `reductionShift`, `directShift` construct shifts from exact
  scalar restriction, derived limit and its adjunction, then the actual
  system direct image. The fields `openShiftNormalization` and
  `closedShiftNormalization` make dj and di compatible with those shifts.
  `closedTermwiseShift` fixes the ordinary closed derived/termwise
  comparison, and `closedShiftInclusion` fixes the restricted I shift to
  the specified ambient one. `openExact`, `closedExact` assert triangulated
  exactness of J and I with those shifts; `openLinear`, `closedLinear`
  assert linearity over `Padic.coefficientExtensionIntegers l E`.
- `openAdjunction` is J ⊣ j_R*, and `closedAdjunction` is i_R* ⊣ I, on
  the actual full integral constructible categories. `openUnit`,
  `openCounit`, `closedUnit`, `closedCounit` spell out each ordinary-derived
  unit/counit through dj, di and the pullback comparisons. The ordinary
  open adjunction is the exact derived module adjunction; the ordinary
  closed adjunction is the published derived adjunction. Consequently
  these are the ordinary termwise maps with their actual normalizations.
- `openSystemUnit`, `openSystemCounit` separately identify both open
  adjunction maps with the whole strict-system adjunction maps through
  the actual reduction counit and `compactOperationReduction`. The proper
  identity factor is removed by the unique right-adjoint comparison
  `systemDirectId` to the actual system pullback identity.
- `disjoint` says `IsZero (j_R*.obj (I.obj M))` for every M in C_Z. The
  functorial composition and its zero objects supply the natural zero
  assertion; no choice of objectwise vanishing maps is substituted.

Dependency declarations used, with modules:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the existing coefficient rings.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its completed coefficient sheaf.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory` and `IsSfDerivedComplete`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`:
  the recorded ring-sheaf inverse-image conventions; concrete module
  pullback, open extension and direct image use the imported existing
  `AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage`,
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage` interfaces.
- `Sheaf.Paper.IntegralImmersionPullbackNormalization`:
  `IntegralImmersionNormalization.Comparison`, `HasReductionInterval`.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`, using `PurCompactSupport.completed`,
  `openExtension`, `image` and the specified compact-support functor.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`,
  `sfCompletedModuleDirectImage`, `sfCompletedDerivedDirectImage`,
  `sfDerivedRestrictionComparison`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`.
- Added landed dependency `def-weil-system-operation-exchange-realization`,
  module `Sheaf.Paper.SystemOperationExchangeRealization`:
  `FrobeniusExchange.models`, `reduction`, `systemDirect`, `integralDirectImage`,
  `directImageFunctor`, `systemAdjunction`, `systemDerivedOpenAdjunction`,
  `systemDirectEvaluation`, `compactOperationReduction`; inherited sequence
  site reduction/unit/projection interfaces are used unchanged.
- New definition dependency `def-sf-ordinary-integral-comparison-data`,
  owning exact existing definitions in
  `Sheaf.Paper.SfIntegralOrdinaryRecollementRealization`:
  `SfOrdinaryIntegralComparison`, `sfOrdinaryDerivedAdjunction`,
  `sfOrdinaryDerivedPull`, `sfOrdinaryPushReduction`.
- `Mathlib.CategoryTheory.Adjunction.Restrict`: `restrictFullyFaithful` and
  its unit/counit formulas are proof dependencies. `conjugateIsoEquiv` and
  `Adjunction.rightAdjointUniq` construct actual comparisons.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`:
  `Functor.rightDerivedFunctorNatIso`,
  `Functor.rightDerivedFunctorIsoMapDerivedCategory`,
  `Functor.mapDerivedCategoryIdIso`.
- All other recorded proof-dependency modules are imported for the seven-step
  proof plan, including open reduction, closed localization, direct-image
  limits, Koszul reconstruction, finite constructibility and site comparison,
  strict Roos comparison, triangulated/linear subcategories, exact derived
  adjunction and Mathlib exact derived functors.

Edge cases checked before and during writing: empty X, empty U or Z,
identity open/closed immersion, zero input, nonreduced Z, arbitrary positive
quotient exponent (including Lean n=0, which is R/t), arbitrary integer shifts,
intervals including negative degrees, and reversed intervals for zero objects.
No nonemptiness or density is added. No finite Tor dimension assumption is
introduced. Derived reduction is never replaced by ordinary reduction; exact
closed image, not arbitrary morphism direct image, supplies the same bounds.
The site object/morphism universes and coefficient universes are the existing
ones; no additional universe equality is imposed to solve instance selection.

Searches for an existing statement:

- `msearch.py ... leanfinder "integral constructible proetale sheaves open extension closed direct image normalized adjunction"`:
  eight ordinary normalization/structure-sheaf restriction hits; no full match.
- `msearch.py ... loogle "Functor.mapDerivedCategory, Adjunction.restrictFullyFaithful"`:
  no hits (unknown queried identifier); source reading located the exact APIs.
- `msearch.py ... grep "integralSupport|supportNormalization|IntegralDirectImage|extensionByZero" CategoryTheory`:
  no matches.
- `msearch.py ... leansearch "normalized integral support functors constructible proetale sheaves open closed immersion adjunction"`:
  eight ordinary structure-sheaf results; none is this normalization package.
- `rg` on project `WeilConjectures` and `Sheaf` for integral support,
  normalization, direct image, open extension and strict realization names;
  direct item-id search in `WeilConjectures`: no existing exact declaration.
  These searches located the reused ordinary and system realization modules.

No STATEMENT-DISPUTED issue, statement correction or missing dependency module.
One new definition node records existing interfaces as requested in H2. The identity and limit comparison helpers belong to this
node's normalization, have source/blueprint docstrings, and are all listed in
`lean.declarations`. Only proofs are postponed. In particular the identity iso
is selected from a section-characterized *unique* isomorphism, not bare existence.

## Second reading by Q68

Author's second pass against the node and current source (not an independent
reader). The dispatcher explicitly forbids starting other agents and assigns
independent review to the maintainer. The returned independent review found H2
and H3; both are repaired as recorded below. Checked each hypothesis and conclusion
against the fields above, the direction of both adjunctions and all four
unit/counit equations, both strict-system open maps, the canonical inverse
orientation of di, and preservation of the original interval. Added the
closed full-subcategory shift/inclusion equation so the restricted shift
cannot be independently chosen. No mathematical statement was changed.

Compilation uses only the prescribed server `scompile.py`; no local Lean or
library build was run. The final delivery is checked by `deliver2.py` preflight
and its per-file compilation.


## New nodes

`def-sf-ordinary-integral-comparison-data` is a definition node for the ordinary
completed-coefficient immersion interfaces already present in
`Sheaf.Paper.SfIntegralOrdinaryRecollementRealization`: ordinary module inverse
image and adjunction, their derived functor/adjunction, the actual finite-reduction
adjunct, and `SfOrdinaryIntegralComparison` with its full normalized data fields.
Its `lean` record uses `existing: true`, lists all four requested interfaces
and their defining helpers, and points directly to that published module.
This is ownership of the existing definitions, with no copy, alias or second
construction. The theorem `sfIntegralOrdinaryRecollement_realization` is not
listed, assumed or used. The source is the ordinary support/adjunction passage
of the localization blueprint and Stacks 03D2, 07A6, 0941, 099N; the node's
statement gives the actual model, strict Roos, finite projection, unit,
constructibility and interval data of the existing structure, without asserting
its existence.

New-node searches: LeanSearch query `ordinary completed coefficient immersion
pullback derived adjunction quotient normalized integral comparison` returned
eight generic pullback/derived-unit declarations; LeanFinder query `canonical
ordinary immersion pullback and direct image comparison with strict quotient
tower realization` returned eight scheme-immersion/base-change declarations;
Mathlib grep `SfOrdinaryIntegralComparison|sfOrdinaryDerivedPull|sfOrdinaryPushReduction`
returned zero. Project rg found the four exact definitions in the published
ordinary recollement module, no upstream WeilConjectures copy, and only the
ordinary-recollement *theorem* node in the DAG. `blueprint_refs.py search
'ordinary integral comparison'` returned no definition node. The exact wrapper
search results are retained verbatim in `mathlib_searches` of the new node.
Thus this uses §1(A)'s existing-definition record rather than creating a
duplicate module. The generic data type imposes no new geometric assertion;
the empty scheme, zero object, first positive quotient and arbitrary shifts
remain valid. Its fields do not require a global finite-field datum.

## Repair of returned head 197c081aaa3c

1. H2: replaced the added theorem-node statement dependency
   `lem-sf-integral-ordinary-recollement-realization` by
   `def-sf-ordinary-integral-comparison-data`. The definition node owns
   `SfOrdinaryIntegralComparison`, `sfOrdinaryDerivedPull`,
   `sfOrdinaryDerivedAdjunction`, `sfOrdinaryPushReduction` and their defining
   helpers in the existing module. It does not bind the existence theorem.
   The item's original TeX statement and proof are unchanged. The ordinary
   module import now implements this definition dependency.
2. H3: chose the return's alternative “drop the unused fields”. Removed the
   two unreferenced structure fields `pullOpen` and `pullClosed`.
   `closedPull_formula`, `openSystemUnit`, `openSystemCounit` and all four
   ordinary unit/counit normalization equations remain, so the actual
   pullback identifications remain pinned by the existing canonical maps.
   No independent immersion-comparison witness is asserted and ignored.

Compared the sandbox node with current main without Git mutations: the original
mathematical statement matches exactly; differences are the authorized `lean`
record and statement-dependency additions. The previous head is identified in
its retained delivery log. The prescribed delivery wrapper performs the rebase
and builds the repaired delivery atop current main. All other clauses marked
OK by the maintainer are retained. Only the two unused fields have been removed
from the Lean conclusion; this is an actual content repair, not an unchanged push.


The initial repair dry run requested the new-node schema field `import_flags`;
added the empty list, matching current definition-node records. Also separated
the grouped new-node citations so every statement dependency is explicitly cited.
No Lean change was needed for this metadata repair. The new definition's
dependencies have no return path to the item, so the added edges introduce no
cycle. A broader traversal found an unrelated existing cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`; reported here for maintenance,
without changing those nodes.
