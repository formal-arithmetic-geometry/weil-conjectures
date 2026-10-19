## Worker report

Repair of L's immutable return b9138306191c (H3/H13). The rejected generic package
has been replaced by the actual completed integral categories and their published raw
rationalizations. No arbitrary category, scalar functor, unconstrained coherence Prop,
or Nonempty package remains. The node's mathematical statement is unchanged.

The primary module is `Sheaf.Paper.PbcScalarExtension`, namespace
`AlgebraicGeometry.Scheme`. Its primary theorem `pbcCoherentScalarExtension` states exactness,
literal identity transitions, both unit equations, the four-field pentagon, and shift
compatibility. Its companion declarations state the ambient operation comparisons,
the actual exchange equation and their conditional rational restrictions. Every theorem
is postponed with `sorry`; definitions have explicit data or use a unique universal
property that determines the object up to its unit-compatible isomorphism.

The node's hypotheses and clauses correspond as follows:

- Prime: `(l : ℕ) [Fact l.Prime]`.
- Finite coefficient fields and inclusion: `[Field E] [Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]`, likewise for F, with
  `i : E →ₐ[Padic l] F`. Nested fields use `Padic.FiniteCoefficientFields l Ω`
  and their actual `IntermediateField.inclusion`; Ω need not be algebraically closed
  for this finite tower. Every nested finite field chain embeds in such an Ω.
- Scheme hypotheses: `T : Scheme.{u}`, `[IsNoetherian T]`, the explicit proposition
  `∃ n : ℕ, topologicalKrullDim T ≤ n`, and
  `∀ t : T, IsUnit (l : T.presheaf.stalk t)`. These become named Fact instances
  only where the inherited triangulations need instance synthesis.
- Integral category and raw rationalization: `PbcIntegralCategory` and
  `PbcRationalDerivedCategory` from `Sheaf.Paper.PbcRationalCategory` and its
  imported bounded-constructible-complete construction. These are exactly the
  published full subcategory and `ScalarLocalization`, with unchanged integral
  objects and tensor Hom modules; no Karoubi completion is introduced.
- Integral completed coefficient change: `pbcEmbeddingIntegerMap` restricts the
  actual field embedding to the lifted integer rings. `pbcScalarQuotientMap`
  induces the map on each positive quotient. `pbcScalarCoefficientMap_exists`
  uniquely fixes the completed ring map by all finite limit projections.
  `pbcEmbeddingAmbientTensor` is the existing `pbcDerivedExtend` of this map.
- Constructible restriction: `pbcEmbeddingAmbientTensor_preserves` states
  preservation of all three membership conditions, and
  `pbcEmbeddingIntegralTensor` is `ObjectProperty.lift` of that exact functor.
- Rational scalar extension: `pbcRationalScalarHom_exists` uniquely specifies
  its additive Hom map on every scalar times a localized integral morphism.
  The source scalar is sent through the actual field inclusion and the
  integer-normalized `pbcRationalCoefficients` isomorphisms.
  `pbcRationalScalarExtension` uses these Hom maps and the integral object map.
  This is scalar localization after integral change of completed rings.
- Exactness and canonical shifts: `pbcAmbientScalarShift_exists` fixes shifts
  by the universal derived counit. `pbcIntegralScalarShift_exists` fixes their
  restriction by the faithful inclusion, and `pbcRationalScalarShift_exists`
  fixes localization by `pbcScalarLocalizationIso`. `pbcRationalScalarExact`
  asserts Additive and IsTriangulated for this shift structure.
- Balanced natural associator: `pbcAmbientScalarComp` uses the existing
  adjunction-normalized `pbcReductionNormalization`. Its rational components
  are their actual localizations (`pbcRationalScalarCompComponent`), with
  naturality on all rational morphisms asserted before forming the NatIso.
- Literal identity: `pbcStageTransition` uses the identity functor when its
  coefficient fields are equal. `pbcStageNormalization` identifies the raw
  tensor with that functor through the ordinary tensor multiplication unit.
  `pbcStageAssociator` is the specified balancing conjugated by these units.
  `pbcStageAssociator_laws` and the primary theorem state the unit and pentagon
  equations, including coincident adjacent fields. `pbcStageAssociatorShift`
  asserts `NatTrans.CommShift` for the chosen associator.
- Ordinary and completed operation comparisons: `pbcScalarOrdinaryPullIso`
  uses the derived tensor/pullback comparison normalized on flat K-flat
  representatives. `pbcScalarDirectImageMap` is its actual adjunction mate;
  `pbcScalarDirectImageMap_isIso` asserts its invertibility for finite coefficients.
  `pbcScalarCompletionIso_exists` uniquely fixes completion comparison by the
  actual completion units. `pbcScalarCompletedPullIso` is their stated composite.
  These are natural isomorphisms on the ambient module derived categories,
  and hence on the derived-complete objects. `pbcScalarPreservesComplete`
  records preservation of the intrinsic complete subcategory.
- Conditional constructible/rational comparisons:
  `pbcScalarDirectImage_rational` and `pbcScalarCompletedPull_rational`
  take exactly the two preservation hypotheses needed for those restrictions.
  Their unique NatIsos have the localized ambient components. No preservation
  for an arbitrary morphism is asserted.
- Cartesian square and exchange: `sq : ChosenCartesianSquare g' f' f a`
  retains the chosen identification. `pbcActualCompletedAmbientExchange` in the
  dependency module is the mate of its canonical derived pullback square.
  `pbcActualCompletedExchange` is that mate followed by completion and the
  direct-image/completion comparison. `pbcScalarCompletedExchange` equates
  the two explicitly written routes using these transformations and the scalar
  comparisons. `pbcScalarCompletedExchange_rational` states equality of their
  actual localized components when the endpoints belong to the integral categories.
- Coherence of operation comparisons: `pbcScalarOperations_identity`,
  `pbcScalarCompletedPull_identity`, `pbcScalarDirectImage_comp`,
  `pbcScalarOrdinaryPull_comp`, `pbcScalarCompletedPull_comp`, the three
  corresponding `_coefficients` declarations, `pbcScalarCompletion_coefficients`,
  and `pbcScalarOperations_shift` assert equations against the specified units,
  canonical composition comparisons, balancing and shift comparisons.

Edge cases checked: empty schemes (pointwise invertibility is vacuous and the
published integral category still applies); zero complexes; positive quotient
levels n+1 including n=0; ramified extensions (the source uniformizer ideal maps
into, not onto, the target ideal); arbitrary finite field embeddings; identity
extensions; repeated fields in the pentagon; identity and composed scheme maps;
and arbitrary morphisms whose direct image does not preserve constructibility.
No equality of source and target uniformizer powers is used under ramification.
The site object universe remains u+1 and its morphism universe u. Coefficients and
module values are in u+1, using the published lift of the integer ring.

Searches (including the retained searches.jsonl from this reconstruction):

- `msearch.py` LeanFinder, query “finite scalar extension on derived complete
  constructible pro-etale sheaves compatible with exchange and scalar towers”:
  eight algebraic etaleness hits; no match for this package.
- `msearch.py` Loogle, query
  `CategoryTheory.Functor.CommShift, CategoryTheory.Functor.IsTriangulated`:
  twelve general triangulated-functor hits; reused those Mathlib interfaces.
- `msearch.py` grep, `scalarExtension|changeOfRings|ChangeOfRings` in
  Mathlib/CategoryTheory: no hits for the completed constructible package.
- `rg` over slopmaster2 WeilConjectures and the project's Lean for scalar
  extension, rational categories, associators and this blueprint id: found
  ordinary field/module scalar extension, the older etale derived-complete
  stages, and the existing integral/completed constructions. The older etale
  categories are different from this node's completed pro-etale constructible
  category. Their declarations are not substituted for it.
- Current server sources were read through `scompile.py --source`, including
  `Sheaf.Paper.PbcRationalCategory`. The now-landed specialization is imported
  directly, replacing the earlier generic rational-category dependency module.
  Missing local modules of this delivery were supplied together to the wrapper.

The local literature paths are absent on this worker machine. I opened the cited
primary sources online: [Stacks 099N](https://stacks.math.columbia.edu/tag/099N),
which specifies completed pullback as ordinary pullback followed by completion and
its inverse-limit formula, and [Stacks 0944](https://stacks.math.columbia.edu/tag/0944),
the perfect coefficient projection formula. The complete node proof is retained
in the main theorem docstring; Milne Section 19 is background, not a claim that
it states this entire coherent package.

No new definition nodes and no statement correction are needed. The eight
prerequisite interfaces are listed below; their node copies change only `lean`.
Their ids are added to the item's statement dependencies because its concrete
functors, shift structures and exchanges use their declarations. This is the
human's 2026-10-16 authorization to state previously unstated prerequisites in
this same delivery. Explicit exchange-route types and irreducible comparison definitions prevent
unnecessary elaborator unfolding; the per-file compiler limit stays at 60 seconds.
No second-reading certificate is claimed by this worker;
the next reader must independently inspect this reconstruction.

## Dependency modules

- `def-weil-pbc-proetale-modules`: import-only repair in
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`; explicitly import
  `Sheaf.CategoryTheory.RingedSiteModules` to resolve the initial unknown
  `ringedSiteModules` identifier and all returned cascading category and
  realization errors. All original declarations are retained verbatim.
  The current refinement realization module remains available unchanged.

- `def-weil-integral-scalar-extension`: the additional
  `IntegralScalarExtensionUniverses` interface exposes the already published
  K-flat/Roos construction with independent scheme and coefficient universes;
  its predecessor abbreviation identified those universes. The construction,
  its normalized representative comparison and additivity are retained.
- `lem-weil-finite-free-completed-scalar-comparison`: the published module
  failed to compile after that predecessor's universe restriction. Its delivered
  repair changes only the scalar-interface import and references to the same
  generalized construction, preserving the finite-free, completion-comparison,
  completeness and identity-unit assertions. Full details appear below.

The earlier proposed repairs of `lem-weil-pbc-uniform-complete-triangulated`
and `prop-weil-pbc-rational-transport` were removed during the earlier reading.
The delivery uses their published modules `Sheaf.Paper.PbcUniformCompleteTriangulated`
and `Sheaf.Paper.PbcRationalTransport` directly; neither is a dependency override.
Their actual uniform predicate, selected triangulation, field identification and
inter-category transport are sufficient, as detailed in the second readings below.

- `lem-weil-pbc-ringed-topoi-module-adjunction`:
  `Sheaf.Paper.PbcCompletedPullbackActual`,
  `AlgebraicGeometry.Scheme.pbcActualModuleAdjunction_exists`. Reuses the published
  completed module pullback and direct image, with the unique tensor-unit-normalized
  adjunction, their universal derived pairs, shifts, the intrinsic completion
  reflector and its actual unit. The original equal-universe theorem remains
  imported. It does not instantiate the small pro-etale universes and noninvertible
  completed coefficient structure map required here.
- `def-weil-pbc-completed-pullback`:
  `Sheaf.Paper.PbcActualStrictPullback`,
  `AlgebraicGeometry.Scheme.pbcActualStrictCompletedPull`. Publicly imports and
  reuses the now-published `CompletedTowerPullback` constructions in full. Adds
  the functorial strict-tower formula and its unique unit-compatible natural
  comparison with the completion reflector on the complete subcategory. No
  private replacement of the recorded tower, derived limit or unit is used.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:
  `Sheaf.Paper.PbcActualScalarPullback`,
  `AlgebraicGeometry.Scheme.pbcActualScalarDerivedPullIso_exists`. Retains the
  recorded general tensor theorem by public import, and adds its coefficient
  comparison for the actual potentially noninvertible completed structure maps.
  The right-adjoint comparison is identity on sections; ordinary pullback is
  its adjunction conjugate; the derived comparison is uniquely fixed on all
  flat K-flat representatives; the direct-image map is its mate.
- `def-weil-pbc-ambient-ringed-exchange`:
  `Sheaf.Paper.PbcActualRingedExchange`,
  `AlgebraicGeometry.Scheme.pbcActualCompletedAmbientExchange`. Reexports the
  original arbitrary compatible invertible-coefficient square and its exchange.
  Supplies the same canonical mate for actual completed coefficient structure
  maps, together with section/representative-normalized composition comparisons.
  The completed mate uses the actual completion unit and direct-image comparison.
  Thus the old recorded invertible-coefficient interface is preserved and its
  required noninvertible completed-coefficient specialization is exposed.

Other dependency declarations read and reused directly:
`Padic.finite_coefficientExtensionRing` from
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`;
`PbcRationalDerivedCategory`, `pbcRationalization`, and its constant-section
linearity from `Sheaf.Paper.PbcRationalCategory`;
`ChosenCartesianSquare` from `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`;
and `sfIntrinsicDerivedPullback` from the current dependency module
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`, which publicly retains
`Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` and its finite operations.
The recorded intrinsic specialization was reread after it landed during this repair.
The main module also imports the stated proof dependencies, including finite-free
completed scalar comparison, K-flat coefficient change, constant completion,
stratified-perfect characterization, coefficient inverse image, projection mate,
exchange coherence, Koszul and strict-tower limit interfaces.

## Repair of immutable head b9138306191c

The reconstruction is compared with the two rejected modules retained in
`scratchpad/returned-PbcScalarExtension.lean` and
`scratchpad/returned-PbcRationalCategory.lean`. It replaces those statements;
it is not an unchanged rebase. The return's defects are addressed individually:

1. **Arbitrary categories (H3).** The rejected theorem quantified over unrelated
   abelian categories `C` and `C'`. The reconstructed functors have source and
   target `PbcIntegralCategory` and `PbcRationalDerivedCategory` for the specified
   scheme and finite coefficient fields. These abbreviations reduce to the
   published bounded-constructible-complete predicate and raw Hom localization.
2. **Arbitrary scalar functor (H3).** There is no scalar functor parameter or
   package field. The coefficient inclusion is fixed on every finite quotient;
   its unique completed map feeds `pbcDerivedExtend`. The rational functor uses
   the uniquely specified balanced map on Hom modules. Identity normalization
   uses the ordinary tensor multiplication unit, and composition uses the
   adjunction-normalized balanced tensor comparison.
3. **Unasserted Prop fields (H3).** `PbcFunctorComparison` and
   `PbcScalarExtensionPackage` are absent from all delivery modules. Exactness
   is asserted as `Additive` and `IsTriangulated`; coherence is asserted by
   equalities of specified transformations, not by data fields of type `Prop`.
4. **Natural coherence and exchange equations (H3).** The associator is a
   `NatIso`; the unit and pentagon equalities and `NatTrans.CommShift` are
   explicit theorems. Ambient operation comparisons are actual natural
   transformations or isomorphisms. Their identity, composition, coefficient
   tower and shift equations are explicitly stated. The exchange routes are
   defined from the canonical mate and completion units, and
   `pbcScalarCompletedExchange` equates those routes. The rational statement
   applies the actual localization to their integral components.
5. **Unspecialized rational dependency (H13).** The old generic
   `Sheaf.CategoryTheory.PbcRationalCategory` replacement is not delivered.
   All seven modules use the published
   `Sheaf.Paper.PbcRationalCategory` and its actual scheme/coefficient
   specialization. The rational-transport dependency states its own
   specialization to these completed integral categories, together with the
   generic tensor-Hom universal property from which that specialization follows.
   The other dependency repairs publicly retain their general recorded
   interfaces and supply the normalized completed-coefficient interfaces
   required by this statement, as detailed above.

The previous second-reading section belonged to an earlier pass and has been
removed. This worker report does not certify an independent second reading;
the dispatcher-provided second reader must inspect and deliver this reconstruction.

## Published finite-stage overlap audit

The current source search additionally found
`Sheaf.Paper.PbcFiniteCompletedCoefficientMap` and
`Sheaf.Paper.FiniteStagePairCategory`. Their coefficient stages use
`pbcFiniteField = Shrink E.val`, require an algebraic closure, and accept only
inclusions of its finite intermediate fields. This delivery must also state
ambient comparisons for a specified arbitrary Padic-algebra embedding
`i : E →ₐ[Padic l] F` on the published `pbcIntegralDatum l E` itself. Those
stage-specialized signatures cannot instantiate that interface without an
additional coefficient transport. The reconstruction therefore exposes this
more general embedding interface, using the same published `pbcDerivedExtend`
and integral full-subcategory/localization constructions; it does not introduce
a different tensor construction. Its generic names now explicitly use
`pbcEmbedding...`; its subfield inclusion is `pbcSubfieldInclusion`, and its
primary theorem is `pbcCoherentScalarExtension`. This avoids collisions with
all seven existing finite-stage declarations. The finite-stage modules and
their existing consumers are untouched. A scan of all named declarations in
the seven delivery files against the current project sources found exactly
these seven overlaps before renaming and none afterward.

The completed-pullback dependency now also publicly imports its current recorded
`Sheaf.Paper.CompletedPullback` interface, which itself reexports the strict
resolving construction. This retains both published presentations as the base
moves; the helper still supplies the natural unit-compatible comparison with
the reflection onto the actual intrinsic complete predicate. Dependency node
copies were refreshed from the current shared DAG, preserving every field except
this delivery's `lean` records.


## Additional dependency modules after compile diagnosis

- `def-weil-integral-scalar-extension`:
  `Sheaf.Paper.IntegralScalarExtensionUniverses`,
  `WeilConjectures.integralScalarExtensionOfUniverses`. The current recorded
  abbreviation binds both the scheme and coefficient field to `u`; the already
  published `integralScalarExtensionWellDefined` uses independent `t` and `u`.
  The helper exposes that very same universal witness and its normalized
  representative comparison, keeping both universes independent and publicly
  retaining the old interface. There is no change of scalar functor, no arbitrary
  comparison and no additional hypothesis. Its three definitions have real data.
- `lem-weil-finite-free-completed-scalar-comparison`:
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`,
  `WeilConjectures.finiteFreeCompletedScalarComparison`. Local compilation of
  the published module failed at lines 206, 209, 218 and 335: a scheme in `t`
  was passed to the now equal-universe scalar-extension API. The delivered
  module retains its complete source and changes only the import and references
  to the generalized universal interface above. The finite-free isomorphism,
  strict mapping-cocone component equations, canonical completion comparison,
  completeness assertion and multiplication/completeness-unit equation are
  all preserved. The two node copies change only `lean`; both already landed
  prerequisite IDs are added to the item's `stmt_deps`. This is a universe
  interface repair under section 1(B), with no statement correction.

The new interface was checked against the complete source and docstring of
`integralScalarExtensionWellDefined` and the current server source of
`IntegralScalarExtension`, and the existing finite-free module and node were
read in full. The generalization uses the existing resolving-class construction
rather than identifying the site and coefficient universes. All nine delivered
modules are included in the final compile and dry run.

## Repair of immutable head 9404282461d0

The returned overlap is repaired by removing
`AlgebraicGeometry.Scheme.pbcActualIntegralShiftLinear` completely from
`Sheaf.Paper.PbcIntegralTriangulationActual` and from that module's owning node's
`lean.declarations`. The module now publicly imports
`Sheaf.Paper.IntegralTStructure`, using the existing instance
`AlgebraicGeometry.Scheme.pbcIntegralShift_isLinear` instead. No alias or replacement
postponed theorem is introduced.

I read the existing source and docstring both in the shared checkout and through
`scompile.py --source Sheaf.Paper.IntegralTStructure`. Its binders are explicitly
`(T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]`,
`[Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, `[IsNoetherian T]`,
`[Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]`,
`[Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`, and `(n : ℤ)`.
The removed theorem had exactly these binders (with T after E). Both assert
`(shiftFunctor (PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) n).Linear
(PbcIntegralRing l E)` in the same namespace. Neither `open` directives nor
universe binders change those fully qualified objects. The inherited shift and
constant-section action are identical, including n = 0, negative shifts, the empty
scheme and zero objects. The existing theorem imposes no additional hypothesis.

A fresh `rg` search of the delivery found no explicit callers of the removed name;
its use was via instance synthesis. The public import supplies the existing
instance to both `PbcActualRationalTransport` and the primary scalar-extension
module. The node's primary triangulated-and-isomorphism-closure statement is
unchanged. The earlier second-reading certificate has been removed because this
repair needs a new independent reading.

The item additionally cites the already landed node
`prop-weil-pbc-integral-tstructure` in `stmt_deps`, recording the reused shift
instance under the permission to cite landed nodes requested by a return. A DAG
reachability check found no path from that node back to this item; the addition
therefore introduces no dependency cycle. Its node and module are not redelivered.

Fresh validation after this repair: all nine delivered Lean files passed
`scompile.py Q30 prop-weil-pbc-scalar-extension` with exit code 0 and no
warnings or errors. The repaired triangulation module compiled in 2.4 seconds;
the final library scalar-extension module compiled in 41.2 seconds, within the
unchanged 60-second per-file limit. Full output is retained in
`scratchpad/compile-repair-940428.log`.

## Earlier second reading (a previous round; superseded)

I independently read the current node, the initial nine modules and the final seven modules, rather than
certifying the earlier return or its previous reader. I also opened the recorded
coefficient, rational-category, Cartesian-square and pro-etale-operation interfaces,
IntegralTStructure, the generic scalar localization and triangulation modules, the
published completed pullback and intrinsic completion, and the original interfaces
retained by the dependency modules. The mathematical statement is unchanged, and
there is no statement_change or new definition node in this delivery.

Source check: the cited literature checkout is absent here. I fetched the actual
Stacks sources into scratchpad/second-{proetale,sites-cohomology,sites-modules}.tex
and read the named lemmas with their surrounding hypotheses. In particular,
[099N](https://stacks.math.columbia.edu/tag/099N),
proetale.tex, lemma-pushforward-Noetherian-case, assumes a Noetherian coefficient
ring and an ideal and gives completion after ordinary pullback, its reduction-limit
formula, and direct-image/completion compatibility. It imposes no properness or
constructibility-preservation assertion for an arbitrary morphism. The preceding
paragraph explicitly distinguishes constant and completed coefficient categories.
[03D7](https://stacks.math.columbia.edu/tag/03D7) uses an arbitrary ringed-topos
structure map, not an invertible one. The K-flat and tensor comparisons are
[0G7E](https://stacks.math.columbia.edu/tag/0G7E) and
[07A4](https://stacks.math.columbia.edu/tag/07A4); the projection map and its perfect
coefficient case are [0944](https://stacks.math.columbia.edu/tag/0944).
[093M](https://stacks.math.columbia.edu/tag/093M) supplies the completed constant
coefficient flatness and quotient comparisons. I also read 09C3's local-model
lemma: it is contextual input, not a statement of the whole uniform-tower theorem.

I fetched and read Bhatt--Scholze, arXiv:1309.1198, Definition 3.4.10, Lemma
3.4.12, Proposition 3.5.1 (including its constant Noetherian/replete setting),
Lemma 6.8.2 and Proposition 6.8.14, and Milne's Lectures on Etale Cohomology,
Section 19, pp. 123--126. These support the completed and rational coefficient
conventions. Milne does not state the entire coherent derived package verbatim;
its precise specification here is the blueprint node and its eight-step proof.
No additional assumptions from a different finiteness theorem are imported.

The node's objects, hypotheses and conclusion clauses, matched in order:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Verdict: exact; no fixed prime is chosen.
2. Finite fields E contained in F: `[Field E] [Algebra (Padic l) E]` and
   `[FiniteDimensional (Padic l) E]`, likewise F, with the specified algebra
   embedding `i`. For chains, `Padic.FiniteCoefficientFields l Ω` and
   `IntermediateField.inclusion` give actual nested subfields. I read that
   abbreviation: its definition and finite-dimensional instance do not retain
   the unused surrounding algebraic-closure variable. Thus Ω has only Field and
   Algebra assumptions here. Any finite nested chain is represented in its
   largest field; no algebraic-closure hypothesis is imposed. Verdict: exact.
3. T: `(T : Scheme.{u}) [IsNoetherian T]`, finite dimension
   `∃ n : ℕ, topologicalKrullDim T ≤ n`, and
   `∀ t : T, IsUnit (l : T.presheaf.stalk t)`. Facts used for inherited
   structures carry exactly these propositions. Verdict: exact; no separatedness,
   excellence, properness or base-field assumption is added.
4. Integral and rational categories: I unfolded `PbcIntegralCategory` through
   `PbcIsBoundedConstructibleComplete` (intrinsic completeness, uniform
   constructible reductions and compatible etale origins). I unfolded
   `PbcRationalDerivedCategory` through `PbcRationalCategory` to
   `ScalarLocalization`: objects are integral objects and Homs are the tensor
   modules localized at the uniformizer. `pbcRationalCoefficientEquiv` fixes the
   identification of localized scalars with E on the actual integer elements.
   Verdict: the recorded categories, without a Karoubi envelope.
5. Specified integral coefficient extension: `pbcEmbeddingIntegerMap` is the
   lifted restriction of i to the valuation rings, `pbcScalarQuotientMap` is
   its quotient lift, and `pbcScalarCoefficientMap_exists` specifies every
   finite projection of the completed map uniquely. `pbcEmbeddingAmbientTensor`
   is the recorded `pbcDerivedExtend` of this very map. Verdict: actual ordinary
   derived tensor along the completed coefficient inclusion, not a functor input.
6. Constructible restriction and rationalization:
   `pbcEmbeddingAmbientTensor_preserves` concerns the actual three-clause
   predicate; `pbcEmbeddingIntegralTensor` is its full-subcategory lift.
   `pbcRationalScalarHom_exists` specifies the additive map on all scalar times
   localized integral arrows, with scalar transported by i. The resulting
   `pbcRationalScalarExtension` has exactly the integral object map. Verdict:
   the node's derived scalar extension followed by raw scalar localization.
7. Exactness: `pbcRationalScalarExact` asserts Additive and IsTriangulated with
   the prescribed CommShift instance. `pbcStageExact` and the primary theorem
   retain them after normalization. Verdict: an exact functor on these categories.
8. Literal identity: `pbcStageTransition` selects `𝟭` for equal fields.
   `pbcStageNormalization` uses the ambient tensor multiplication unit, not an
   unspecified equivalence. The primary theorem asserts the identity equality.
   Verdict: literal equality, including the equal-field case.
9. Three-field associator: `pbcAmbientScalarComp` is the recorded
   `pbcReductionNormalization` for the actual coefficient maps;
   `pbcRationalScalarCompComponent` localizes its full-subcategory components.
   `pbcStageAssociator` conjugates this balanced comparison by the specified
   units. Verdict: natural balancing isomorphism, with the stated direction.
10. Unit and pentagon clauses: `pbcStageAssociator_laws` and the primary theorem
    give both unitor HEqs and the four-field component equation. Its left route
    first maps the E,F,G associator through G-to-H extension; its right route
    first applies the F,G,H associator. Verdict: precisely the associativity
    pentagon, with repeated fields allowed and ordinary functor associativity
    accounted for by the component form.
11. Canonical shift: `pbcAmbientScalarShift_exists` fixes it by the universal
    derived counit; `pbcIntegralScalarShift_exists` fixes its restriction by the
    faithful inclusion; `pbcRationalScalarShift_exists` fixes its localization
    by `pbcScalarLocalizationIso`. The normalized transitions transport this
    same shift. `pbcStageAssociatorShift` asserts NatTrans.CommShift for the
    actual associator. Verdict: the stated shift-one comparison and coherence;
    the integer-shift interface includes shift one, zero and negative shifts.
12. Scheme maps f and g: the ambient-operation declarations quantify over actual
    scheme morphisms with no preservation assumption. These constructions exist
    on the larger ambient derived categories, so specialize to every scheme
    satisfying the node's hypotheses. Verdict: no restricted class of maps.
13. Direct-image comparison: `pbcScalarDirectImageMap` is the adjunction mate of
    the normalized scalar/pullback square. `pbcScalarDirectImageMap_isIso`
    asserts invertibility for the finite field extension, and its asIso is
    `pbcScalarDirectImageIso`. Verdict: the specified ordinary ringed-topos
    derived direct image comparison, in the node's direction.
14. Completed-pullback comparison: `pbcScalarOrdinaryPullIso` has its flat K-flat
    normalization. `pbcScalarCompletionIso_exists` fixes the comparison by the
    actual completion unit, uniquely. `pbcScalarCompletedPullIso` is their
    explicit composite. The dependency's `pbcActualCompletedPullback_tower`
    identifies this reflector construction with the recorded strict tower on
    complete inputs and identifies their units. Verdict: the node's completed
    pullback, not ordinary pullback incorrectly assumed complete.
15. Ambient completeness: `pbcScalarPreservesComplete` preserves the actual
    intrinsic complete predicate. The completion reflector has values in that
    predicate. The published completed direct-image interface supplies its
    completion comparison. Verdict: the displayed ambient comparisons apply
    on derived-complete objects; none requires constructibility.
16. Conditional restrictions: `pbcScalarDirectImage_rational` and
    `pbcScalarCompletedPull_rational` assume exactly that the two coefficient
    versions of the relevant operation preserve the integral category. Their
    unique NatIsos have the localized ambient components. Verdict: the explicit
    conditional assertion, without preservation for arbitrary f or g.
17. Cartesian square: `sq : ChosenCartesianSquare g' f' f a` retains both the
    chosen pullback isomorphism and its projection equations. Its commutativity
    `sq.w` forms the ringed pullback square. Verdict: the same chosen square.
18. Specified exchange: `pbcActualCompletedAmbientExchange` is `mateEquiv` of
    the canonical derived pullback square with the normalized adjunctions.
    `pbcActualCompletedExchange` applies completion and the unit-compatible
    direct-image/completion comparison. Verdict: the specified mate and its
    completion, before constructibility or rationalization.
19. Exchange compatibility: I traced both `pbcScalarExchangeLeft` and
    `pbcScalarExchangeRight` from their common source to target. The former
    uses E-exchange and the two coefficient comparisons; the latter uses
    the coefficient comparisons and F-exchange. `pbcScalarCompletedExchange`
    equates the actual transformations. Its `_rational` companion applies
    the actual localization to those same components under endpoint membership.
    Verdict: equality for the specified exchange, not existence of some map.
20. Remaining coherence: `pbcScalarOperations_identity` and
    `pbcScalarCompletedPull_identity` use the canonical scheme identity
    comparisons; the three `_comp` theorems use canonical composition;
    the three `_coefficients` theorems and `pbcScalarCompletion_coefficients`
    use actual tensor balancing for successive extensions;
    `pbcScalarOperations_shift` uses their canonical shifts. Verdict: all the
    identity, composition, coefficient-extension and shift clauses are asserted.

Dependency reading (no new nodes):

- `lem-weil-pbc-uniform-complete-triangulated`: H4/H13 mismatch found. The
  current recorded `Sheaf.Paper.PbcUniformCompleteTriangulated` already states
  exactly isomorphism closure AND triangulation of the published three-clause
  predicate, with the same geometric hypotheses. I read its actual signature,
  also fetched the current server source with scompile.py --source, and removed
  the duplicate PbcIntegralTriangulationActual module and its node-copy repair.
  IntegralTStructure supplies the inherited triangulation and shift linearity;
  the owning item merely exposes the recorded isomorphism-closure theorem as
  an instance through the existing Fact hypotheses. No new closure theorem.
- `prop-weil-pbc-rational-transport`: H4/H13 mismatch found. The current recorded
  `Sheaf.Paper.PbcRationalTransport` already has `ScalarLocalization.transport`
  between different categories, its pure-tensor formula, uniqueness and natural
  transformations; it ALSO has `WeilConjectures.pbcRationalTransport` and
  `pbcRationalExchange` on exactly the published integral/rational categories.
  I read all these signatures, their supplied-operation hypotheses, the canonical
  field equivalence and their selected triangulation, and fetched the current
  server source. I removed the duplicate PbcActualRationalTransport module and
  node-copy repair. The item now uses `ScalarLocalization.transport` and the
  existing `pbcRationalCoefficientEquiv` directly. Its data-only instances
  `pbcScalarRational*` expose the SAME selected scalar-localization witnesses
  and existing field action when erased geometric proofs obstruct instance
  inference. They neither introduce new categories nor restate transport.
  These findings supersede the older Worker report's generic-interface claims.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: publicly retains the existing
  general interface (through ModulePullbackPushforwardAdjunction), and adds the
  actual small-site completed module functors, the section-normalized adjunction
  and its derived interfaces. The old general theorem identifies site object and
  morphism universes and cannot directly instantiate this small site. The new
  specialized functors reuse completedModulePullback/DirectImage and the actual
  coefficient structure map. Completion is the reflection of the actual intrinsic
  predicate, with its universal unit; its data is determined up to the unique
  unit-compatible isomorphism. Verdict: authorized interface extension, no
  arbitrary adjunction or hollow completion object.
- `def-weil-pbc-completed-pullback`: the dependency publicly retains both
  CompletedPullback and CompletedTowerPullback, and composes the published
  reduction tower, tower pullback and derived limit. Its comparison unit uses
  those exact quotient augmentations. Its unique reflector comparison is only
  asserted on complete inputs, exactly as in the node. Verdict: no replacement
  tower, no arbitrary cone filler and no extra completeness assumption.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the general simultaneous
  tensor comparison remains public through RingedTopoiCanonicalTensorPullback
  and ProEtaleCanonicalTensorPullback. The additional coefficient square uses
  the actual completed structure maps. Its right-adjoint comparison is identity
  on sections, ordinary pullback is its adjunction conjugate, and the derived
  comparison is fixed on every flat-term K-flat representative. Verdict: the
  needed specialization is normalized, and the original general statement is
  preserved rather than replaced by a special case.
- `def-weil-pbc-ambient-ringed-exchange`: the arbitrary compatible ring-sheaf
  interface remains public through ProEtaleAmbientRingedExchange. The additional
  completed-coefficient square has section-normalized compositions and canonical
  derived counits before taking the mate. Verdict: same exchange notion, with
  the additional potentially noninvertible completed coefficient structure maps
  exposed for the consumer; the general recorded declaration is retained.
- `def-weil-integral-scalar-extension`: the original public abbreviation binds
  scheme and coefficient field to u; IntegralScalarExtensionWellDefined itself
  has independent universes t,u and specifies the strict Roos/K-flat descent
  uniquely up to comparison-preserving isomorphism. The three new declarations
  select this exact witness and its normalized comparison and additivity.
  Verdict: justified universe-interface repair without a new tensor construction.
- `lem-weil-finite-free-completed-scalar-comparison`: I read the quotient-
  projection characterization, the strict mapping-cocone comparison (including
  its zero shifted component), normalized derived descent, finite free rank,
  completeness implication and identity multiplication/completeness-unit equation.
  They are all retained. The only scalar-construction change is to the identical
  generalized interface above. Verdict: the node's complete comparison, with
  arbitrary Y and independent site/coefficient universes.

Edge cases: empty T is allowed (the dimension inequality and pointwise ell
invertibility have their usual empty-space meaning); zero complexes remain
objects of the full subcategory and raw localization. Positive quotient levels
are n+1, so n=0 is the first quotient, not A/(1). Repeated coefficient fields
exercise both unit equations and all degenerate pentagons. A ramified extension
only uses inclusion of uniformizer-power ideals, not equality of quotient
systems. The shift interface allows every integer. Finite coefficient fields
have characteristic zero automatically, and schemes are constrained only by
ell invertibility. No index set of fields is assumed finite or nonempty by the
coherence theorem; it quantifies over supplied chains. The small site retains
object universe u+1 and morphism universe u, with modules in u+1. The separate
universe helper retains t and u independently. No new universe equality is used.

Independent searches: msearch LeanFinder for “derived coefficient extension
proetale rational constructible category pentagon base change” returned eight
unrelated algebraic-etaleness hits. Loogle on
`CategoryTheory.Functor.IsTriangulated` returned the standard exact-functor API;
those Mathlib structures are used. A first Loogle query involving the project's
ScalarLocalization name was not meaningful to the Mathlib index and was replaced
by that successful query. msearch grep for scalar change, coefficient extension
and rational transport returned ordinary algebraic scalar-change material.
I independently ran rg over Mathlib, slopmaster2 WeilConjectures, the current
project's Sheaf tree and its newer ProEtale/ModuleObject framework, and read
coord/pefw-upstream-framework.md. The condensed module-object categories and
old etale packages are not the raw integral rationalizations required here.
I opened PbcFiniteCompletedCoefficientMap and FiniteStagePairCategory: their
Shrink fields in a fixed algebraic closure do not directly accept the arbitrary
embedding i on pbcIntegralDatum l E used by the ambient comparisons. The present
embedding interface reuses the same coefficient/derived construction and does
not replace those stages. The semantic search of the current dependencies exposed
the duplicate uniform-triangulation and rational-transport declarations described
above; same-name searching alone would not have found these. Those modules and
their node-copy overrides are removed, and their current owning modules are used.
The repaired finite-free module intentionally keeps its existing module and owner.
A final rg search found none of the eight new adapter names in the current project
or upstream. The final seven modules contain 185 declarations, all accounted for
in their owning lean.declarations lists.

Changes made by this second reader: removed both redundant dependency modules
and their node-copy overrides; reused the published uniform triangulation,
canonical rational coefficient equivalence and inter-category rational transport;
retained only data adapters to expose those structures through Fact hypotheses
in the owning item module; moved that paper-specific module from CategoryTheory
to `Sheaf.Paper.PbcScalarExtension`, as required by the module conventions.
All changes are recorded in the item's lean module/file/declaration metadata.
No source statement, proof plan, mathematical hypothesis or target unit changed.
The seven primary lean.statement strings match the literal signatures, including
whitespace and line breaks; declaration lists exactly match their owning files.
All postponed statements have named docstrings with source and blueprint id;
the primary docstring carries all eight node-proof steps. No definition contains
sorry. Choices of maps, functors and comparisons retain unique universal
characterizations rather than mere uncharacterized existence. The six supporting
node overrides are only lean interface repairs under section 1(B); no new nodes
or statement_change are needed. Compilation and delivery checks follow below.

Final validation: deliver2.py --no-push returned OK at 98b6afb951 after
compiling all seven final modules, each separately, through scompile.py. There
were no errors or disallowed warnings, and the current-server preflight passed.
The metadata check independently verified all 185 declaration names, each
primary literal signature, real definition bodies, sorry-only theorem bodies
and the 100-character Lean line limit. No target statement changed.


## Repair of immutable head 70af360f4afc

The current source and the failed file-only compilation were compared against the
retained delivery. The first diagnostic is at ProEtaleFiniteModules line 81:
`Unknown identifier ringedSiteModules`. The later unknown realization theorems,
unresolved Category instances and nonfunctional derived-category abbreviations
are cascading errors from that first missing name.

The repair adds a direct public import of
`Sheaf.CategoryTheory.RingedSiteModules` to the owning canonical module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`. It leaves every existing
declaration body, signature and docstring unchanged. The explicit import makes
the general-site module abbreviation available even when the published compiled
site-comparison module does not reexport it. The delivered owner node receives
a lean-only section 1(B) record, and the item cites this already-landed node.
No mathematical statement, construction, universe, hypothesis or target changes.

## Dependency modules

Additional import-only repair: `def-weil-pbc-proetale-modules`, module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, primary declaration
`AlgebraicGeometry.ProEtale.FiniteCoefficientModules`. It explicitly imports
the existing `CategoryTheory.ringedSiteModules` abbreviation, which is exactly
Mathlib `SheafOfModules`, with no new definition of module sheaves. All original
continuous-function coefficient presheaves, sheafifications, scalar maps,
realizations, exactness instances, derived comparison and constructible full
subcategory remain verbatim. The existing refinement realization module remains
available to its importers. This repairs the returned compiler error rather
than suppressing or replacing any statement. The other six dependency repairs
remain as documented above.

Repair validation so far: the repaired finite-module source passes scompile.py
both as an isolated sandbox module and at its library module name, with no
diagnostics (6.8 s and 6.5 s). Its only source difference from the current
server copy is the direct public import above. All eight primary metadata
signatures are byte-for-byte equal to their source signatures; all declaration
lists match their files, and all eight files satisfy the 100-character limit.
The ordinary multi-file compile and required dry run are also running server
confirmation: their local overlay stage reports a missing object file while
trying to build a downstream import before the supplied sibling is available.
A private-source-overlay attempt also exposed an unavailable shared compiled
artifact. These local wrapper failures do not invalidate the clean individual
compile; the complete server result is recorded below once available.

The complete eight-file scompile.py run returned exit 0 after server
confirmation. Every delivered module compiled separately in dependency order,
including ProEtaleFiniteModules (5.1 s), the independent-universe adapter
(3.2 s), finite-free comparison (22.4 s), the four actual pullback/exchange
interfaces (1.8--4.6 s each), and PbcScalarExtension (36.0 s). The confirmed
server output contains no errors or warnings; every file stayed below 60 s.
The required dry run is completing its own compile and current-base preflight.

The first required dry run compiled all eight files successfully on the server,
then found one report-section defect: its parser reads only the first
`## Dependency modules` section, while the new import repair was documented in
a later section with that heading. The repair is now also listed in the first
section. No Lean or node change was necessary for this preflight-only fix.

Final repair validation: deliver2.py --no-push returned OK at 9a5271840d.
All eight delivered files compiled and the current-base server preflight passed.
Nothing was pushed; the second reader delivers.

## Earlier second reading (a previous round; superseded)

This is an independent reading of the present eight-module delivery. I read the
item node, its blueprint source at order 1307, the recorded statement-dependency
signatures and all eight delivered modules. The older reading and repair logs
above describe earlier snapshots; this section records the final reading.

Source check: the blueprint specifies exact scalar extension, literal identity,
balanced associators, units, pentagon, shifts, operation comparisons and the
specified exchange. Milne Section 19 discusses finiteness and adic sheaves, and
is not a proof of this entire coherent derived package. I read the supplied
Milne text at Section 19 and the node's explicit eight-step replacement proof.
I also read Stacks sites-modules.tex, lemma-completion-flat (093M),
proetale.tex, lemma-pushforward-Noetherian-case (099N), including its Noetherian
coefficient-ring hypothesis and clauses (1)--(5), and sites-cohomology.tex,
lemma-projection-formula (0944) with its preceding definition of the projection
mate and following exchange diagram. These are the source hypotheses actually
used by the node, rather than an added assumption that every scheme map preserves
constructibility. The scalar fields' valuation rings supply the Noetherian adic
coefficients. The item's statement and proof are unchanged from its reviewed node;
there is no statement_change and no target-unit change.

The object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Finite coefficient extensions:
   `(E F : Type u) [Field E] [Field F]`, their `Algebra ℚ_[l]` and
   `FiniteDimensional ℚ_[l]` instances, and the actual algebra embedding
   `i : E →ₐ[ℚ_[l]] F`. An algebra map between fields is injective; no separate
   injectivity, unramifiedness or finite-type assumption is imposed. PASS.
2. T is noetherian, finite dimensional, ell invertible:
   `(T : Scheme.{u}) [IsNoetherian T]`, `∃ n : ℕ, topologicalKrullDim T ≤ n`,
   and `∀ t : T, IsUnit (l : T.presheaf.stalk t)`. The coherence sections package
   the last two in Fact instances; these express the same hypotheses. PASS.
3. Integral category: `PbcIntegralCategory` unfolds to the published full
   `PbcBoundedConstructibleComplete` category. I read its underlying predicate:
   intrinsic completeness, the uniform bounded constructible reduction tower,
   and compatible etale-origin witnesses. `pbcEmbeddingAmbientTensor_preserves`
   concerns exactly this predicate, not just finite-level constructibility. PASS.
4. Rational category and no envelope: `PbcRationalDerivedCategory` is the
   published `PbcRationalCategory`, namely `ScalarLocalization` of that full
   integral category at `pbcUniformizer`. Its Hom action is the actual tensor
   action; `pbcRationalCoefficientEquiv` is the existing canonical identification
   of the localization with E. Objects are retained and no Karoubi construction
   occurs. I opened these declarations and their signatures. PASS.
5. Actual integral coefficient change: `pbcEmbeddingIntegerMap` is the lifted
   restriction of i to the recorded valuation rings. `pbcScalarQuotientMap`
   uses its genuine ideal-kernel theorem. `pbcScalarCoefficientMap_exists`
   fixes every residue projection uniquely, and `pbcEmbeddingAmbientTensor`
   is the existing `pbcDerivedExtend` along this exact map. PASS.
6. Restriction and rationalization: `pbcEmbeddingIntegralTensor` is its full
   subcategory lift. `pbcRationalScalarHom_exists` specifies the additive map
   on every scalar times an integral arrow, transporting that scalar by i;
   `pbcRationalScalarExtension` uses that map and the integral object map.
   This is integral completed-ring change followed by raw localization. PASS.
7. Exact functor: `pbcRationalScalarExact` asserts Additive and IsTriangulated
   for the normalized shift structure, with `pbcStageExact` and the primary
   `pbcCoherentScalarExtension` retaining both after normalization. PASS.
8. Literal identity: `pbcStageTransition` selects `𝟭` when its two subfields
   are equal. `pbcStageNormalization` uses the actual multiplication tensor
   unit through `pbcRationalScalarUnit`; it is not an unspecified equivalence.
   The equality in `pbcStageAssociator_laws` and the primary theorem is literal.
   The nested-field encoding uses actual finite intermediate fields in Ω and
   does not require Ω algebraically closed. PASS.
9. Specified three-field associator: `pbcAmbientScalarComp` uses the recorded
   adjunction-normalized `pbcReductionNormalization`; its rational components
   are their actual localized full-subcategory images. `pbcStageAssociator`
   conjugates that balancing comparison by the stated tensor units. PASS.
10. Unit equations and four-field pentagon: both unitor HEqs and the component
    equality in `pbcStageAssociator_laws` and the primary theorem have the
    correct source and target. The left route applies the E,F,G associator
    then the G,H extension; the right route applies the F,G,H associator
    first. Repeated adjacent fields are allowed. PASS.
11. Canonical shift and its compatibility: `pbcAmbientScalarShift_exists`
    normalizes by the universal counit; the integral shift is fixed through
    the faithful inclusion and the rational shift through
    `pbcScalarLocalizationIso`. `pbcStageTransitionShift` transports this
    structure and `pbcStageAssociatorShift` asserts NatTrans.CommShift of
    the specified associator. Integer shifts include the requested shift one.
    PASS.
12. Scheme morphisms f and g: the ambient declarations bind actual arbitrary
    scheme morphisms, so apply to all schemes with the node's hypotheses.
    `pbcScalarDirectImageMap` is the actual derived adjunction mate;
    `pbcScalarDirectImageMap_isIso` asserts invertibility for finite coefficient
    extension and its `asIso` gives `pbcScalarDirectImageIso`. PASS.
13. Completed pullback comparison: `pbcScalarOrdinaryPullIso` is normalized on
    flat-term K-flat representatives. `pbcScalarCompletionIso_exists` uniquely
    fixes the completion comparison by its unit. Their explicit composite is
    `pbcScalarCompletedPullIso`; the strict-tower dependency identifies this
    reflector with the node's completed pullback on complete inputs. Its
    direction is exactly scalar then target pullback to source pullback then
    scalar, using Lean's diagrammatic functor composition. PASS.
14. Ambient complete categories: `pbcScalarPreservesComplete` concerns the
    actual intrinsic predicate; the reflector lands in it. The direct-image
    completion comparison is normalized by its actual unit. These comparisons
    are available before constructibility and specialize to complete objects.
    PASS.
15. Conditional constructible restrictions/rationalizations:
    `pbcScalarDirectImage_rational` and `pbcScalarCompletedPull_rational`
    bind exactly the two coefficient versions' integral preservation
    hypotheses. Their unique natural isomorphisms have the localized ambient
    components. `pbcConditionalRational` reuses the published
    `ScalarLocalization.transport`. No claim of arbitrary-map preservation
    has been substituted. PASS.
16. Chosen cartesian square: `sq : ChosenCartesianSquare g' f' f a` includes
    commutativity, the chosen pullback isomorphism and both projection
    equations. I read that structure's declaration. PASS.
17. Specified ambient and completed exchange: the dependency's
    `pbcActualCompletedPullSquareIso` uses normalized pullback compositions and
    `sq.w`, and `pbcActualCompletedAmbientExchange` takes its mate under the
    normalized derived adjunctions. `pbcActualCompletedExchange` then applies
    completion and the direct-image/completion comparison. It does not select
    an arbitrary transformation. PASS.
18. Scalar compatibility of that exchange: I traced the common endpoints of
    `pbcScalarExchangeLeft` and `pbcScalarExchangeRight`. They respectively use
    the E-exchange then scalar comparisons and the scalar comparisons then
    F-exchange. `pbcScalarCompletedExchange` equates these very composites;
    its `_rational` companion applies the actual localization under endpoint
    membership hypotheses. PASS.
19. Identity, composition, successive coefficients and shifts: the two
    `_identity` theorems, three operation `_comp` theorems, three operation
    `_coefficients` theorems, completion `_coefficients` theorem, and
    `pbcScalarOperations_shift` express the corresponding component equations
    using the actual canonical identity, pasting, balancing and shift maps.
    Their localized versions inherit these equations on their specified
    components. All concluding coherence clauses are present. PASS.

Dependency reading under section 1(B): no new definition nodes occur. The
module-adjunction repair publicly retains the arbitrary-site theorem and reuses
published completedModulePullback/DirectImage with its tensor-unit-normalized
adjunction. Its general predecessor fixes site object and morphism universes
equal, which cannot instantiate the small site directly. The strict-pullback
repair publicly retains CompletedPullback/CompletedTowerPullback and composes
exactly their reduction tower, resolving tower pullback and derived limit. Its
unique reflector comparison is restricted to complete inputs, as the node says.
The tensor-pullback repair retains the arbitrary-ringed and pro-etale tensor
interfaces and adds the actual coefficient square, with identity right-adjoint
section maps, ordinary adjunction conjugacy and the K-flat derived equation.
The ambient-exchange repair retains the original arbitrary compatible
invertible-coefficient square and adds its noninvertible completed-coefficient
specialization, with normalized composition and identity maps. These are
extensions of the owning interfaces, not replacements by unrelated special cases.

The integral-scalar universe adapter selects the existing
integralScalarExtensionWellDefined witness with independent t,u. I read that
theorem's uniqueness up to comparison-preserving isomorphism; this is stronger
than mere uncharacterized existence. The finite-free-comparison repair retains
its actual quotient projections, zero shifted cone component, normalized descent,
relative rank, completeness and tensor-unit equation, changing only references
to that same generalized construction. The finite-module repair adds the direct
public RingedSiteModules import to the canonical owning module; its definitions
of continuous-function sheafification, left modules, derived comparison and
constructible essential image remain unchanged. I checked them against that
node, including noncommutative finite rings. The current uniform-triangulation
and rational-transport dependencies are used directly: I opened
pbcIntegralUniformComplete_isTriangulated, pbcRationalTriangulationData,
pbcRationalCoefficientEquiv and transport. The eight owning data adapters merely
expose these same structures through Fact hypotheses.

Edge cases: empty schemes and zero complexes are not excluded. The scheme
hypotheses are pointwise/bounded dimension, not nonemptiness. Finite reduction
level zero means exponent n+1=1. No argument identifies source and target
uniformizer ideals under ramification; same-index ideal inclusion is enough,
and completion comparisons use cofinal filtrations. Equal adjacent fields give
both unit equations and degenerate pentagons. The index of quotient towers is
all naturals and no finite/nonempty index restriction is introduced. Fields have
characteristic zero from their Q_l algebra structure; schemes need exactly ell
invertibility. Shifts allow all integers. The site keeps object universe u+1,
morphism universe u and modules in u+1; the separate unrestricted comparison
keeps independent t,u. Coefficient fields and schemes are expressed in a common
ambient size for the published PBC categories, with lifted integral rings; no
extra equality of site object and morphism universes is imposed.

Independent searches this reading: msearch LeanFinder for "finite coefficient
change derived complete sheaves exact functor associativity exchange mate"
returned eight generic exact-functor/derivability/derived-adjunction results, not
this package. Loogle on CategoryTheory.Functor.CommShift returned twelve standard
shift structures and transport operations, which are used. msearch grep on
extendScalarsComp/coefficientExtension/scalar-exchange found ordinary module
scalar extension. I opened Mathlib ModuleCat.ChangeOfRings at extendScalarsComp
and extendScalars_assoc: these concern ordinary modules, not actual complete
constructible sheaves. I also ran rg on the project's Sheaf tree, upstream
WeilConjectures and Mathlib using scalar-extension, change-of-coefficients and
exchange words, and checked the newer ModuleObject framework's documented
coefficient encoding. Its condensed categories, older generic coefficient
frameworks and the finite-stage algebraic-closure encoding do not state this
node on the actual raw PBC categories. The reusable actual uniform and rational
transport interfaces have already been reused, not delivered again.

Mismatches repaired in this reading: two inherited final declarations in
ProEtaleFiniteModules lacked complete source/blueprint docstrings, and its final
equivalence theorem lacked a natural-language proof. I added those references
and the proof using local bijectivity and the associated-module-sheaf adjunction.
The first dependency-report section still listed the two removed duplicate
modules: I replaced those obsolete bullets by their actual published reuse.
I refreshed the copied tensor-pullback node's reviewed_proof bookkeeping from
the read-only base, preserving the current base record rather than reverting
another landing. No Lean signature, construction, hypothesis or mathematical
node field changed in this reading. All eight primary lean.statement strings
are literal signatures, all 215 declarations are listed in their owner records,
and all delivered lines meet the 100-character limit. Data definitions have
real constructions or uniquely characterized choices; postponed theorems retain
sorry proofs and source/proof docstrings. The primary theorem's docstring
contains all eight node-proof steps.

Concurrent-base check: the refreshed finite-module owner also gained a direct
public ProEtaleDerivedCategory import while this reading ran. I retained it in
the sandbox. Against that refreshed owner the only remaining source differences
are the two docstring repairs (and an immaterial final blank line). The
finite-free module differs only in its import and four references to the
independent-universe adapter; the other six files are new owning modules.

Validation in this reading: the required eight-file scompile.py invocation
returned exit 0 after current-server confirmation. All delivered modules compiled
separately with no server errors or warnings: finite modules 5.1 s, universe
adapter 3.0 s, finite-free comparison 21.3 s, completed-pullback interface 2.8 s,
strict pullback 1.8 s, scalar pullback 3.5 s, exchange 4.4 s, main scalar package
36.2 s. Every invocation kept nice 19, two threads and the default 60-second limit.
The local attempt's missing published finite-module artifact was resolved by the
wrapper's authorized server confirmation; it is not a Lean-source failure.
The required dry run recompiles the final docstring/import snapshot and runs
current-base preflight before delivery.

Final dry-run result: deliver2.py --no-push returned exit 0 and
`OK (dry run): commit 2ed9ef40a7 passes the preflight and compiles; nothing pushed`.
It compiled the final eight-module snapshot, including the preserved current
import and repaired docstrings, and passed the server's current-base preflight.
The second reader now runs the prescribed delivery wrapper.

## Repair of immutable head d72b12bcae52

The return reports that `PbcScalarExtension` passed its temporary module-name
check but exceeded 60 seconds when compiled at its final library module name.
The retained eight-module sandbox was compared with the current shared node
records: dependency copies differ only in `lean`; the item additionally retains
its documented added `def-weil-pbc-proetale-modules` dependency. The current
published finite-free comparison still uses the equal-universe predecessor,
so validation must supply all eight retained sibling modules to `scompile.py`.
The sandbox already contains the independent-universe repair; no further change
to that dependency was needed for this return.

The actual Lean repair marks nine constructed comparison isomorphisms
`irreducible`: `pbcAmbientScalarComp`, `pbcRationalScalarCompComponent`,
`pbcRationalScalarComp`, `pbcScalarRestrictId`, `pbcEmbeddingAmbientUnit`,
`pbcRationalScalarUnitComponent`, `pbcRationalScalarUnit`,
`pbcIntegralScalarInclusionIso`, and `pbcScalarLocalizationIso`.
Their full types and construction bodies remain unchanged. In particular, the
balanced tensor comparison, localized components, tensor multiplication units,
and inclusion/localization normalizations are exactly the previous constructions.
Opacity prevents elaboration from repeatedly expanding those construction bodies
when it only needs the declared endpoints. The definitions remain explicitly
unfoldable for future proofs. No hypothesis, mathematical node field, dependency, declaration name, proof
docstring or canonical-map choice changes. The primary signature is unchanged.

Temporary profiler options are used only for diagnosis and will be removed from
the final delivery. The full eight-file compile and required dry run are recorded
below once complete. Every invocation retains the prescribed 60-second limit.

The exchange companion theorem now states
`pbcScalarExchangeLeft l E F i sq = pbcScalarExchangeRight l E F i sq`.
These are the already-defined exact composite routes. Their bodies are precisely
the formerly expanded left and right sides, so this is the same proposition after
definitional unfolding. It avoids re-elaborating the entire composite twice in a
third declaration; no map or comparison is omitted. The original route definitions
and their construction bodies are unchanged. All temporary profiling options have
been removed before validation and delivery.

Source comparison for this repair confirms that both route definitions are
byte-for-byte unchanged and that, after whitespace normalization, their two bodies
are exactly the former expanded sides of `pbcScalarCompletedExchange`. The primary
`lean.statement` remains byte-for-byte equal to its source signature. Every
delivered Lean line remains within 100 characters, and no profiler/trace option
remains. No new declaration or node is introduced.

The structured profiler identified the largest elaboration in
`pbcScalarRationalIsTriangulated`: comparing the pretriangulated structure adapter
with its nested `Classical.choose` witness took about eight seconds on the server.
The six rational triangulation adapters now directly project the same existing
`pbcRationalTriangulationData` witness instead of introducing `let data` aliases
before projecting it. This is precisely zeta expansion of the previous bodies:
their types, selected data and selected proofs are definitionally unchanged.
Removing these aliases avoids the repeated alias/motive comparison seen in the
trace. No new mathematical assertion is proved, and no debug options remain.

The final two checks initially lost a published local import artifact during the
parallel library refresh (`ProEtaleDerivedPullbackComposition.olean`), after the
preceding delivered siblings had compiled. Both wrappers automatically requested
current-server confirmation. A fresh unchanged-source local retry was also made
to obtain final-module timings after the mirror refresh. These transient missing
artifacts are distinct from the returned main-module timeout; no live artifact or
source was edited to bypass them. The final results follow below.

Final validation of the unchanged repaired Lean snapshot:

- The full eight-file `scompile.py` invocation returned exit 0 after current-server
  confirmation. The main package compiled there in 33.2 seconds, with no warnings
  or errors in the confirmed final sources.
- The fresh local eight-file retry also returned exit 0 without warnings or errors.
  It compiled every sibling separately at its temporary and library module name.
  The repaired main module took 29.2 seconds at the temporary name and 55.8 seconds
  at its final library name, including artifact generation. Thus the exact local
  check that exceeded 60 seconds in the return now passes within that limit.
- `deliver2.py Q30 prop-weil-pbc-scalar-extension --no-push` returned exit 0 and
  `OK (dry run): commit 1498fe9a30 passes the preflight and compiles; nothing pushed`.
  Its current-base preflight preserved the newer review bookkeeping on the
  tensor-pullback dependency. The wrapper rebased the delivery onto current main.

No source change followed these successful final compiles. This paragraph records
only their results. The second reader performs delivery; no push was made.

## Earlier second reading (a previous round; superseded)

I read the current shared node, its eight-step proof, the blueprint source at
order 1307, all eight delivered modules and their owning dependency records.
This reading follows the repair of immutable head d72b12bcae52. The earlier
second-reading sections above are historical. No statement_change is present
or needed: the delivered mathematical statement equals the reviewed shared node.

Source check: the blueprint specifies tensor extension, literal identities,
balancing associators, units, pentagon, shifts and operation/exchange coherence.
Milne Section 19, pp. 123--125, supplies the classical adic motivation, not this
complete derived coherence package. I read the actual auxiliary source places:
Stacks proetale.tex, lemma-pushforward-Noetherian-case (099N), including its
constant Noetherian setup and clauses (1)--(5); sites-modules.tex,
lemma-completion-flat (093M); sites-cohomology.tex, lemma-projection-formula
(0944) and remark-compatible-with-diagram (0E48). I also read the cached
Bhatt--Scholze text at Definition 3.4.10, Lemma 3.4.12, Proposition 3.5.1,
Lemma 6.8.2 and Proposition 6.8.14. The valuation rings supply the Noetherian
coefficient hypotheses. None of these sources justifies silently identifying
completed-ring inverse image with an invertible coefficient structure map;
the delivered helpers correctly retain the actual structure map.

Object, hypothesis and conclusion checklist (Lean rendering; verdict):

1. Prime ell: `(l : ℕ) [Fact l.Prime]`; PASS. This is primality, not an
   independent characteristic assumption.
2. Finite Q_l extensions and their inclusion: fields E,F with Q_l algebra and
   FiniteDimensional instances, `i : E →ₐ[Padic l] F`; PASS. The embedding is
   the actual coefficient map. Nested towers use finite IntermediateFields in
   Ω, with IntermediateField.inclusion; Ω has no algebraic-closure hypothesis.
3. Noetherian finite-dimensional T with ell invertible: `[IsNoetherian T]`,
   `∃ n : ℕ, topologicalKrullDim T ≤ n`, and the pointwise stalk-unit condition;
   PASS. The Fact binders in the coherence sections merely expose these same
   propositions to instance synthesis.
4. The integral category: `PbcIntegralCategory` is the published full
   `PbcBoundedConstructibleComplete` category; PASS. I opened its predicate,
   which conjoins intrinsic completeness, uniform constructible reductions,
   and compatible etale origins. The scalar preservation theorem retains all
   three conditions and their actual quotient-transition normalizations.
5. Raw rationalization, without adjoining retracts:
   `PbcRationalDerivedCategory` unfolds to `ScalarLocalization` at the actual
   lifted uniformizer; PASS. I read PbcRationalCategory and
   pbcRationalCoefficientEquiv. The localized Hom modules use the recorded
   integer ring and its canonical fraction map to E.
6. Integral change of completed coefficient rings:
   pbcEmbeddingIntegerMap restricts i to the valuation rings, the quotient
   maps are induced using the named kernel theorem, and the unique completed
   map is fixed by every finite projection; PASS. pbcEmbeddingAmbientTensor
   is precisely pbcDerivedExtend of this map.
7. Constructible restriction followed by scalar localization:
   pbcEmbeddingIntegralTensor is the full-subcategory lift; the unique
   pbcRationalScalarHom maps each pure tensor with scalar transported by i;
   pbcRationalScalarExtension uses those exact object and arrow maps; PASS.
8. Exact functor: pbcRationalScalarExact and pbcStageExact state Additive and
   IsTriangulated for the normalized shift; the primary theorem retains both;
   PASS. The triangulation adapters project the existing
   pbcRationalTriangulationData witness, not a newly chosen triangulation.
9. Literal identity T_E/E: pbcStageTransition selects the identity when the
   coefficient fields are equal, and the primary theorem states equality;
   PASS. pbcStageNormalization uses the actual multiplication tensor unit.
10. The specified three-field associator: pbcAmbientScalarComp uses
    pbcReductionNormalization with the actual composite coefficient map;
    its integral images are rationalized and conjugated by those tensor
    units in pbcStageAssociator; PASS. It is not an arbitrary natural iso.
11. Both unit equations and the four-field pentagon: the two HEqs compare
    with the correctly oriented left/right functor unitors. The component
    pentagon first extends the E,F,G associator to H on one route and first
    associates F,G,H on the other; PASS, including repeated adjacent fields.
12. Canonical shifts and associator compatibility: ambient shift is fixed by
    its universal counit, restriction by the faithful inclusion, and rational
    shift by pbcScalarLocalizationIso. NatTrans.CommShift of the specified
    associator is asserted for ℤ, hence includes shift one; PASS.
13. Ordinary derived direct image and its scalar comparison:
    pbcActualDerivedPush is the published completedDerivedDirectImage, and
    pbcScalarDirectImageMap is the mate of the normalized derived pullback
    comparison. Its named IsIso theorem yields pbcScalarDirectImageIso; PASS.
    The module does not replace the mate by an unrelated isomorphism.
14. Completed pullback comparison: pbcScalarOrdinaryPullIso retains the
    flat-term K-flat equation; pbcScalarCompletionIso is uniquely fixed by
    the completion unit. Their explicit composite is
    pbcScalarCompletedPullIso; PASS. The strict-tower dependency identifies
    this reflector presentation with the node's strict-tower completed
    pullback, with its augmentation, on complete inputs.
15. Ambient derived-complete scope: pbcScalarPreservesComplete uses the actual
    intrinsic complete predicate; completed pullback lands in it and
    pbcActualDirectCompletionIso retains its unit equation; PASS. The
    comparison definitions exist on the ambient derived categories and
    therefore specialize to all complete objects in the node.
16. Conditional constructible restriction and rationalization:
    pbcScalarDirectImage_rational and pbcScalarCompletedPull_rational require
    exactly the E and F preservation hypotheses and uniquely fix localized
    ambient components; PASS. No arbitrary-map constructibility assertion
    has been added. pbcConditionalRational reuses ScalarLocalization.transport.
17. The chosen cartesian square and exchange: ChosenCartesianSquare contains
    commutativity, the chosen pullback iso and both projection equations.
    pbcActualCompletedPullSquareIso is formed from normalized compositions
    and sq.w, and pbcActualCompletedAmbientExchange is its actual mate;
    PASS. Completed exchange applies the reflector and its direct-image
    comparison in the stated order.
18. Scalar extension carries the specified E-exchange to the F-exchange:
    pbcScalarExchangeLeft and pbcScalarExchangeRight have identical endpoints.
    The former applies E-exchange followed by scalar comparisons; the latter
    applies scalar comparisons then F-exchange. pbcScalarCompletedExchange
    equates these exact routes, and its rational companion localizes their
    actual components under endpoint-membership hypotheses; PASS.
19. Coherence for identities, composition, successive coefficients and
    shifts: pbcScalarOperations_identity, pbcScalarCompletedPull_identity,
    the three operation _comp theorems, the three operation _coefficients
    theorems, pbcScalarCompletion_coefficients and pbcScalarOperations_shift
    retain the actual identity/pasting/balancing/unit/shift comparisons;
    PASS. Localized comparisons are fixed componentwise, so inherit these
    equations. Every clause of the node has a corresponding declaration.

Dependency-module check: these are repairs of existing nodes, not new nodes.
The completed-pullback module publicly retains the published strict tower and
adds its unique unit-compatible functor comparison on complete inputs. The
module-adjunction module publicly retains the arbitrary-site theorem and uses
the published completedModulePullback and completedModuleDirectImage, with the
actual tensor-unit section normalization. The tensor-pullback module retains
both current arbitrary-ringed and small-site APIs and adds the exact coefficient
square and its ordinary adjunction conjugate, K-flat-normalized descendant and
mate. The exchange module retains the original arbitrary compatible coefficient
square and adds the completed-coefficient specialization with canonical pasting.
The universe adapter projects the existing universal strict Roos/K-flat
localization witness with independent t,u and retains its representative
comparison; it is determined up to the comparison-preserving isomorphism, rather
than chosen from mere existence. The finite-free repair only redirects its
existing normalized comparison to that same construction. Its rank, finite
projections, zero shifted cone component, completeness and identity-unit clauses
are intact. The finite-module repair retains continuous-function sheafification,
left modules, the derived comparison and the constructible essential image,
including finite noncommutative rings. Its direct imports and final source/proof
docstrings repair the previously reported interface/documentation defects.

Edge cases: empty schemes and zero complexes are allowed; none of the hypotheses
asserts nonemptiness. Positive quotient exponents are n+1, so index zero is the
first genuine reduction. Ramified extensions use ideal inclusion at equal
indices, not equality of source and target uniformizer powers; completion uses
cofinal filtrations. Identity inclusions, repeated fields, and degenerate
pentagons are present. Shifts range over all integers. Characteristic zero of
coefficient fields follows from their Q_l algebra structures; schemes require
exactly stalkwise invertibility of ell. The small site retains object universe
u+1 and morphism universe u, and the unrestricted scalar comparison retains
independent scheme and coefficient universes. No smaller test universe or extra
equality of site universes is imposed. Finite coefficient fields can be placed
in a common ambient size, as in the existing category definitions.

Independent searches: I ran msearch LeanFinder for "adic sheaf coefficient
extension commutes with derived direct image completed pullback associativity"
(eight results: ordinary scheme/module pullback and pushforward coherence),
Loogle for CategoryTheory.Functor.CommShift (twelve standard shift results), and
grep for extendScalarsComp/completed Scalar/scalar exchange (seven ordinary
module results). I independently ran rg on Mathlib, upstream WeilConjectures
and the shared Sheaf tree, with scalarExtension, change-of-coefficients and
coefficient-change words. I opened Mathlib ModuleCat.ChangeOfRings at
extendScalarsComp and extendScalars_assoc; these are ordinary module results.
I opened the exact shared newer pro-etale ModuleObject two-colimit source and
coord/pefw-upstream-framework.md: its condensed module-object categories are
not the node's raw completed-integral rationalizations. I opened and reused
the existing PbcUniformCompleteTriangulated and PbcRationalTransport interfaces.
No exact existing declaration states this package on these actual categories.

Mismatches found and repaired in this reading: concurrent maintenance changed
the tensor-pullback dependency's recorded canonical interface to
RingedTopoiCanonicalTensorPullbackOfUniverses. The sandbox still publicly
imported only its predecessor. I changed that public import to the current
independent-universe module, which itself retains both earlier APIs. This
preserves the newly published general interface as well as the delivery's
completed coefficient-square specialization. I also copied the current
reviewed_lean metadata into the sandbox dependency record to avoid reverting
that maintenance review, and explained the retained API in lean.note. No
signature, definition body, mathematical hypothesis, conclusion, statement
change, or target-unit change was made. I checked all eight lean.statement
strings literally occur as signatures, all delivered lines are at most 100
characters, and no profiler/trace option or new axiom occurs. Data definitions
remain actual constructions or uniquely characterized universal choices;
postponed theorems retain sorry and proof/source/blueprint docstrings. The
primary theorem's docstring carries all eight node proof steps.

Validation of this final second-reading snapshot is recorded below after the
required scompile.py and deliver2.py checks complete.

Final second-reading compilation: the eight-file scompile.py invocation for the
current-interface snapshot returned exit 0, with no errors or warnings. Every
file compiled separately at its sandbox and library module names, using the
default 60-second limit. PbcScalarExtension took 29.3 seconds at its sandbox
name and 48.3 seconds at its final library name. No Lean source change followed
this successful compile. The exact log is
scratchpad/second-final-review-current-interface.log.

Final dry run: deliver2.py Q30 prop-weil-pbc-scalar-extension --no-push printed
`OK (dry run): commit 256f0d66fe passes the preflight and compiles; nothing pushed`.
It compiled the final eight-module snapshot and passed the current-base checks.
Only this validation result was added afterward; no Lean or node change followed.
The prescribed delivery wrapper is now run to push the reviewed delivery.

Delivery tool failure after the successful final compilation and dry run:
The prescribed push invocation returned exit 1 before delivery. The local
compiler attempted the shared overlay's IntegralScalarExtensionWellDefined and
reported a kernel application type mismatch in the imported
CochainComplex.IsKFlatIndependentCoefficients application (first at line 153).
The server confirmation rebuilt KFlat/KFlatIndependentCoefficients but then
reported the same kernel mismatch in IntegralReductionTowerUnrestricted
(first at line 50). Both errors pass the coefficient ring sheaf where the
current predicate expects its HasSheafCompose, WEqualsLocallyBijective and
HasSheafify instance binders. I read the current server
DerivedChangeOfRingsIndependentCoefficients via the prescribed --source wrapper;
its source uses the predicate by named J/R arguments and supplies the new
infrastructure binders. This is an incompatible imported compiled interface,
not a missing mathematical object or a reason to strengthen the item.

An unchanged-source deliver2.py --no-push retry also returned exit 1, with the
same local overlay error and the same server confirmation error. No module in
this delivery was reached by that retry. Logs:
scratchpad/second-final-review-delivery.log and
scratchpad/second-final-review-dry-run-refresh.log. No source, live artifact,
compiler script, or cache was edited to work around the failure. The sandbox
retains the reviewed eight-module snapshot and the current-interface repair.
The earlier successful dry run is recorded honestly above, but the subsequent
current-environment failure prevents pushing. Nothing was pushed.

## Repair retry, 2026-10-16 08:35 UTC

The retained repair of immutable head d72b12bcae52 is still present: irreducible
comparison definitions, shared exchange routes, and direct projections of the
published rational triangulation witness. Its prior successful final-library
compilation is documented above. The current failure occurs before that file,
so this retry cannot measure or certify the returned timeout repair.

I reran scompile.py for the primary file, then for all eight delivered files,
and deliver2.py --no-push twice. Both local compilation and server confirmation
fail in published prerequisites. The all-file compilation reaches the server's
IntegralReductionTower.lean:66, where integralTowerAugmentationIso expects the
old IsKFlatResolutionIndependentCoefficients application. The current dry run
fails locally in IntegralScalarExtensionWellDefined.lean:153 and on the server
in IntegralReductionTowerUnrestricted.lean:50, with the imported old K-flat
argument list applied to the new predicate containing three additional instance
binders. This is an incompatible published compiled interface, not a timeout
or an error in an elaborated delivery declaration.

I read the current server DerivedChangeOfRingsIndependentCoefficients and
IntegralReductionTowerUnrestricted sources using scompile.py --source. The
former explicitly binds HasSheafCompose, WEqualsLocallyBijective and HasSheafify
and calls the predicate with named J and R arguments. The latter uses that
published witness. I also inspected the wrappers read-only: there is no
worker-facing refresh option; the local wrapper already tracks source and
direct-artifact inputs and confirms failure against the server. Neither caches
nor compiler scripts nor live sources were modified.

Affected recorded prerequisites are lem-pur-derived-change-of-rings,
def-weil-integral-reduction-tower and
lem-weil-integral-scalar-extension-well-defined. The current bottom-up instruction
forbids stating other DAG nodes in this delivery; their published compiled
interfaces must first be made mutually consistent by the maintainer. No new
mathematical assumption, replacement construction, or node repair is made to
conceal this failure. All sandbox Lean and node files remain retained.

Evidence: scratchpad/repair-retry-all-compile.log,
scratchpad/repair-retry-dry-run.log,
scratchpad/repair-current-derived-source.log and
scratchpad/repair-current-reduction-source.log. The dry run did not print OK;
nothing was pushed.

## Repair retry, 2026-10-16 08:38 UTC

I compared the retained main module with
`scratchpad/returned-d72-PbcScalarExtension.lean`, the archived immutable returned
head. The substantive timeout repair remains present: the nine comparison
definitions have irreducible bodies, the exchange theorem uses its existing
two route definitions, and the six triangulation adapters project the original
witness directly. This is not the returned source merely rebased. Comparison of
all eight sandbox node copies with the current shared DAG found changes only in
`lean`, plus the item's previously documented additional statement dependency.

Fresh validation still cannot reach the main module. The prescribed eight-file
`scompile.py Q30 prop-weil-pbc-scalar-extension` invocation exited 1. Locally the
wrapper fails while compiling the published
`Sheaf.Paper.IntegralScalarExtensionWellDefined`, first at line 153, with a kernel
application type mismatch: the old compiled application passes the completed
ring sheaf where `IsKFlatIndependentCoefficients` now expects the
`HasSheafCompose`, `WEqualsLocallyBijective`, and `HasSheafify` instance binders.
Server confirmation also exited 1, at `IntegralReductionTower.lean:66`: the
compiled `integralTowerAugmentationIso` expects the old argument list for
`IsKFlatResolutionIndependentCoefficients`, so the actual proof `hq` is rejected.

I then ran the required `deliver2.py Q30 prop-weil-pbc-scalar-extension --no-push`.
It exited 1 with the same local kernel error; server confirmation failed in
`IntegralReductionTowerUnrestricted.lean`, first at line 50, with the same
coefficient-sheaf/instance-binder mismatch. It did not print OK. The fresh logs
are `scratchpad/repair-current-compile.log` and
`scratchpad/repair-20261016-dry-run.log`.

I retrieved the current server sources for `IntegralScalarExtensionWellDefined`,
`IntegralReductionTower`, and `KFlatIndependentCoefficients` using the authorized
`scompile.py --source` interface; the snapshots are
`scratchpad/repair-20261016-*-source.lean`. I also read the shared source signatures
of `IsKFlatIndependentCoefficients`, `IsKFlatResolutionIndependentCoefficients`,
`integralTowerAugmentationIso`, and the derived-change-of-rings witness. Their
current source calls use named `J` and `R` arguments; the compiler diagnostics
expose incompatible imported compiled applications. This failure is in the
published prerequisite packet, not in a newly elaborated sandbox declaration.

The affected DAG prerequisites are `def-weil-integral-reduction-tower`,
`lem-weil-integral-reduction-tower-well-defined`,
`lem-weil-integral-scalar-extension-well-defined`, and
`lem-pur-derived-change-of-rings`. The current bottom-up instruction forbids
restating other DAG nodes in this delivery. No live source, compiled artifact,
cache, or wrapper was edited, and no mathematical hypothesis was changed to
avoid these imports. The prior successful timings in this report are historical;
they do not certify the current published environment. The retained repair is
preserved for verification after that environment is consistent. Nothing was
pushed.

## Repair retry, 2026-10-16, fresh current-source validation

The retained timeout repair was compared directly with the archived returned
`d72b12bcae52` source in `scratchpad/returned-d72-PbcScalarExtension.lean`.
The current source retains the nine irreducible comparison constructions, the
exchange equality through its already-defined two routes, and direct projections
of the original rational triangulation witness. Those changes are substantive
relative to the returned head; this retry does not re-push that returned source.
All eight sandbox node copies were compared with the current shared DAG. Their
differences remain lean-only, except the item's previously documented added
statement dependency. No other node is newly stated or repaired in this retry.

I ran the prescribed scompile.py on the primary module twice. Both attempts
failed locally before the delivered module, at published
BoundedConstructibleTower.lean:124 and :133. The kernel reports an imported
IsKFlatIndependentCoefficients application whose ring-sheaf argument occupies the
position now reserved for HasSheafCompose, followed by WEqualsLocallyBijective
and HasSheafify. These are incompatible compiled interface applications. Server
confirmation rebuilt further published prerequisites, then failed in
ConstantCompletionEquivalence.lean:6 with:
`import Sheaf.Algebra.Homology.KFlatIndependentCoefficients failed, environment
already contains 'SheafOfModules.isMonoidal_W_independentCoefficients' from
Sheaf.Algebra.Homology.KFlat`.

I investigated the duplicate rather than treating the diagnostic alone as a
blocker. The current shared and server source for KFlatIndependentCoefficients
contains only `public import Sheaf.Algebra.Homology.KFlat`; it declares no
duplicate. ConstantCompletionEquivalence already directly imports KFlat. The
conflicting module is imported transitively inside published prerequisites, so
removing a direct import from the delivered module cannot repair that packet.
The prescribed --source snapshots are
`scratchpad/latest-server-kflat-independent.lean` and
`scratchpad/latest-server-constant-completion.lean`. Neither source, compiled
artifact, cache, nor compiler wrapper outside this sandbox was changed.

The required `deliver2.py Q30 prop-weil-pbc-scalar-extension --no-push` then
checked all eight delivered files and exited 1 before elaborating any of them.
Locally IntegralScalarExtensionWellDefined.lean:153 (also :171, :178, :197)
reported the same old K-flat argument application against the new interface.
The wrapper's server confirmation failed in
IntegralReductionTowerUnrestricted.lean:50 (also :68, :75, :96) with the same
ring-sheaf/instance-binder mismatch. It printed `COMPILE FAILED on the server,
nothing pushed`, not OK. The exact fresh logs are
`scratchpad/compile-current-primary.log`,
`scratchpad/compile-current-primary-2.log`, and
`scratchpad/repair-latest-dry-run.log`.

Thus current validation cannot reach or time the returned primary module. The
retained source repair is preserved, but its historical successful timings are
not claimed as current validation. The published prerequisite packet needs a
consistent refresh; the bottom-up instruction forbids restating those other DAG
nodes in this delivery. No mathematical statement was weakened to evade their
imports, and no delivery was pushed.

## Repair retry, 2026-10-16, current prerequisite refresh

I compared the retained eight-module delivery with the current shared sources and
DAG, and compared PbcScalarExtension with the archived returned d72b12bcae52
source. The retained repair is substantive: nine comparison definitions have
irreducible bodies, the completed exchange theorem uses its two unchanged named
composite routes, and six triangulation adapters directly project the same
universal witness. The theorem signatures and canonical construction bodies are
unchanged by these performance repairs, apart from replacing the expanded exchange
equality by its definitionally equal named routes. No new DAG node is stated.

The current-base audit found only lean-record changes in the seven dependency
node copies; the item additionally retains its four previously documented landed
statement dependencies, with none removed. All eight recorded primary signatures
occur verbatim in their modules, and every delivered Lean line has at most 100
characters. The shared versions of ProEtaleFiniteModules and the finite-free
comparison were read and compared: the former differs only by the retained
docstring repair, and the latter retains the independent-universe scalar-extension
interface needed by this delivery. The current statements and full signatures of
the six original statement dependencies were read again.

Unlike the earlier failed retries, the current prescribed scompile.py invocation
has rebuilt past IntegralReductionTower, IntegralReductionTowerUnrestricted,
IntegralScalarExtensionWellDefined and the downstream bounded-constructible and
rational-transport prerequisites. No published source, cache, build artifact or
compiler tool was edited to obtain this refresh. The result of this invocation
and the required current-base dry run are recorded below after they complete.

Current validation: the prescribed eight-file scompile.py invocation returned
exit 0 with no errors or warnings. It compiled every delivered file individually
at its sandbox and final library module names. PbcScalarExtension took 26.1
seconds at the sandbox name and 43.1 seconds at the final library name, within
the unchanged 60-second limit. The fresh log is
`scratchpad/repair-current-session-compile.log`. Thus the original returned
timeout is repaired and the later prerequisite mismatch no longer reproduces
in this current wrapper run.

The required `deliver2.py Q30 prop-weil-pbc-scalar-extension --no-push`
returned exit 0 and printed:
`OK (dry run): commit cffce64f3c passes the preflight and compiles; nothing pushed`.
The exact log is `scratchpad/repair-current-session-dry-run.log`. The wrapper
constructed the reviewable delivery on current newtargets-dag and the current
server preflight accepted it. No Lean or node change followed this successful
validation; only this result paragraph was appended. Nothing was pushed.

## Second reading by Q30

Fresh independent reading, 2026-10-16. I read the current DAG statement and its
 eight proof steps, the master blueprint scalar-extension page, the actual Lean
 declarations and their dependency interfaces. I also read Stacks `proetale.tex`,
 `lemma-pushforward-Noetherian-case` (099N), clauses (1)--(5),
 `sites-cohomology.tex`, `remark-base-change` and `lemma-projection-formula`
 (07A7 and 0944), and `sites-modules.tex`, `lemma-completion-flat` (093M).
 These assume a Noetherian coefficient ring for completion and a perfect
 coefficient complex for projection. The finite extension integer rings and
 finite-free completed coefficient extension supply those hypotheses. Milne
 Section 19 is background, not a source stating this entire explicit package.

Object/hypothesis/conclusion checklist, matched to the file:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Exact match.
2. Finite extensions and inclusion: `(E F : Type u)` with `Field`,
   `Algebra (Padic l)` and `FiniteDimensional (Padic l)`, and
   `i : E →ₐ[Padic l] F`. For towers, `Padic.FiniteCoefficientFields l Ω`
   is the actual finite intermediate-field subtype, and its maps are
   `IntermediateField.inclusion`. Any finite chain can be placed in its
   largest field. No algebraic-closure assumption is added. Exact match.
3. Scheme: `T : Scheme.{u}`, `[IsNoetherian T]`, dimension bound
   `∃ n : ℕ, topologicalKrullDim T ≤ n`, and
   `∀ t : T, IsUnit (l : T.presheaf.stalk t)`. The last two are packaged as
   `Fact` where instance synthesis needs them. No stronger geometric
   hypothesis is substituted. Exact match.
4. Categories: I opened `PbcIntegralCategory`, the actual bounded constructible
   complete predicate and `PbcRationalDerivedCategory`. The latter is
   `ScalarLocalization` of the former, with its constant completed-section
   action and recorded uniformizer. It retains integral objects and has
   tensor-localized Hom modules, without a Karoubi envelope. The triangulation
   adapters project the same witness as `pbcRationalTriangulationData`, whose
   triangles are the integral image triangles. Exact match.
5. Scalar construction: `pbcEmbeddingIntegerMap` restricts the actual field
   embedding; `pbcScalarQuotientMap` is its quotient lift. All finite
   projections uniquely determine `pbcScalarCoefficientMap`.
   `pbcEmbeddingAmbientTensor` is `pbcDerivedExtend` of that map, its
   preservation theorem supplies `ObjectProperty.lift`, and
   `pbcRationalScalarHom_exists` uniquely specifies the semilinear Hom map
   on every scalar times an integral arrow. `pbcRationalScalarExtension`
   uses exactly these maps. This is integral completed coefficient change
   followed by raw scalar localization, as required.
6. Exactness: `pbcRationalScalarExact`, `pbcStageExact`, and the first two
   conjuncts of `pbcCoherentScalarExtension` assert `Additive` and
   `IsTriangulated` for the specified shift structure. Exact match.
7. Literal identity: `pbcStageTransition` selects `𝟭` when `E = F`.
   `pbcStageNormalization` uses the actual tensor multiplication unit,
   obtained from identity-on-sections restriction. Its identity equation is
   asserted in `pbcStageAssociator_laws` and the main theorem. Exact match.
8. Associator: `pbcAmbientScalarComp` uses the adjunction-normalized
   `pbcReductionNormalization`. Its naturality and rational naturality hold
   for all arrows. `pbcStageAssociator` conjugates it by the specified tensor
   units. `pbcStageAssociator_laws` and the main theorem give both units and
   the four-field pentagon, including repeated fields. Exact match.
9. Shifts: `pbcAmbientScalarShift_exists` fixes them by the universal derived
   counit; the integral inclusion and `pbcRationalScalarShift_exists` fix their
   restriction and localization. `pbcStageAssociatorShift` and the final
   conjunct give `NatTrans.CommShift`, including the required shift by one.
10. Direct image: `pbcScalarDirectImageMap` is the actual mate of
    `pbcActualScalarDerivedPullIso`, whose flat K-flat representative
    characterization I read. `pbcScalarDirectImageMap_isIso` asserts its
    invertibility, and `pbcScalarDirectImageIso` retains that arrow via
    `asIso`. These are the published completed-module ordinary derived
    direct images, not arbitrary functors. Exact match.
11. Completed pullback: `pbcScalarCompletionIso_exists` uniquely fixes its
    comparison by the actual units. `pbcScalarCompletedPullIso` composes it
    with the ordinary comparison. The dependency
    `pbcActualCompletedPullback_tower` identifies the published strict
    quotient-tower construction with the intrinsic reflector on complete
    inputs, preserving its unit. The Lean isomorphism is displayed in the
    inverse direction to the node's pullback isomorphism; its inverse is
    precisely that displayed arrow. No object or direction is lost.
12. Conditional restriction and rationalization:
    `pbcScalarDirectImage_rational` and `pbcScalarCompletedPull_rational`
    assume exactly preservation by the two displayed operations. Their
    unique NatIsos have the localized actual ambient components. No
    constructibility preservation for arbitrary morphisms is asserted.
13. Square and exchange: I opened `ChosenCartesianSquare`, including its
    chosen pullback isomorphism and both projection equations.
    `pbcActualCompletedAmbientExchange` is `mateEquiv` of the canonical
    composition/commutativity square. `pbcActualCompletedExchange` applies
    completion and the specified direct-image/completion comparison.
    `pbcScalarExchangeLeft` and `pbcScalarExchangeRight` are the two actual
    routes; `pbcScalarCompletedExchange` equates them, and its `_rational`
    companion localizes their components on the exact endpoint membership
    hypotheses. This retains the canonical exchange, not an arbitrary map.
14. Coherence of operations: `pbcScalarOperations_identity`,
    `pbcScalarCompletedPull_identity`, the three scheme-composition
    equations, the three `_coefficients` equations,
    `pbcScalarCompletion_coefficients` and `pbcScalarOperations_shift`
    compare the specified routes using canonical units, pasting, balancing
    and shifts. All four final coherence clauses are explicitly asserted.

Dependency modules (H13): the seven dependency records retain their DAG
statements and change only `lean`. `ProEtaleFiniteModules` retains finite
possibly noncommutative coefficient modules and their actual etale realization,
with the missing `RingedSiteModules` import. The independent-universe integral
interface selects the published strict Roos/K-flat construction and its
normalized comparison. The finite-free comparison still specifies the actual
coefficient map, zero shifted cone component, derived descent, completeness and
identity normalization. The module-adjunction interface uses the published
module pull/push functors with the literal tensor unit, universal derived
adjunction and actual reflector. The strict-pullback adapter imports
`CompletedPullback` and reuses the existing tower and limit. The tensor/pullback
adapter reexports the general interfaces and adds the completed coefficient
square comparison normalized on flat K-flat representatives and its actual
mate. The exchange adapter reexports the general coefficient-square exchange
and supplies its completed-coefficient specialization with canonical pasting
and completion. These are interface repairs, retaining general declarations
by import, rather than private weaker replacements. No new definition nodes
are present.

Edge cases: empty schemes and zero complexes are included. Quotient `n = 0`
means the first positive quotient `n+1`. Ramification uses inclusion of
uniformizer ideals and cofinal powers, never equality of same-index powers.
Ell is prime and invertible exactly as required. Identity extensions and
repeated fields are included in the units and pentagon. Identity and composed
scheme morphisms are included. No properness, separatedness, finite-type or
arbitrary constructibility-preservation condition is imposed. The small site's
object universe is `u+1`, its morphism universe is `u`, and module values and
lifted coefficients use `u+1`. The dependency repair retains independent
coefficient and scheme universes. A common size bound for finite coefficient
fields and schemes does not identify site object and morphism universes.

Independent duplicate searches: reran LeanFinder with “finite scalar extension
derived complete constructible category” (eight unrelated condensed/finite
module hits), Loogle with `CategoryTheory.NatTrans.CommShift` (general interface,
reused), and grep with `completedScalar|scalar.*[Cc]omplete|[Cc]omplete.*scalar`
(ordinary completion hits, no coherent package). I also searched project Lean
and slopmaster2 `WeilConjectures` for the blueprint id, scalar extension, stage
transitions and associators. The existing `FiniteStagePairCategory`,
`ScalarExtensionExact` and `CommonStageCalculus` signatures do not state this
whole package on these actual categories with conditional operations and the
canonical completed exchange. Existing category, tensor, localization,
adjunction and shift declarations are reused. There is no exact existing
attachment for the node.

Changes: no mathematical mismatch required a Lean or statement change. I
restored current-base `blueprint_update` metadata in the item, completed-pullback
and ambient-exchange node copies; their stale metadata would otherwise change
unauthorized fields. I appended this exact required heading and certificate,
leaving the worker report and earlier repair history in place. No canonical
construction, hypothesis or conclusion changed. There is no `statement_change`,
so a corrected-statement citer audit does not apply.

Checks: all eight `lean.statement` strings occur verbatim in their files. The
primary docstring retains all eight node proof steps. The postponed theorems
have source/blueprint proof docstrings; definitions have explicit data or
uniquely normalized universal constructions. Delivered Lean lines are at most
100 characters; no variable or universe is unbound. The fresh required
eight-file `scompile.py` run returned exit 0 with no errors or warnings. Each
file compiled individually at both sandbox and final names; the primary
final-name compile took 40.1 seconds, within the unchanged 60-second limit.

Fresh second-reader dry run: `deliver2.py Q30 prop-weil-pbc-scalar-extension
--no-push` returned exit 0 and printed `OK (dry run): commit c9569d4a09 passes
the preflight and compiles; nothing pushed`. No Lean or node change followed
this successful check; this validation paragraph is the only further edit.
