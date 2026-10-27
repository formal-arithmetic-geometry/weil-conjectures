## Worker report

Item: `lem-sf-adic-finite-realization-cocone`. Module:
`Sheaf.Paper.AdicFiniteRealizationCocone`. The only postponed theorem is
`WeilConjectures.AdicFiniteRealization.adic_finite_realization_cocone`.
All predicates, records and comparison functors in this module are helpers spelling
out this node's own clauses. They contain actual data, not sorry-based choices.
No statement correction or dependency-module repair is needed. The H2 repair adds
two definition nodes bound to existing published structures; no Lean declaration
is copied or changed.

Sources read: Bhatt--Scholze, Proposition 6.6.11 (integral stratified perfect
characterization), Definition 6.8.8 (constructibility), Proposition 6.8.14(2)
(raw rationalization and continuous realization); the accepted six-step DAG argument
including its specified chi and balanced tensor normalization. The HRS Theorem 7.7
and Lemma 7.9 references and their uses are retained in the theorem docstring.
The existing dependency signatures and their normalization fields were read before
composing them. In particular raw rationalization, rather than its idempotent envelope,
is essential here.

### Hypotheses and conclusions

- `D : FiniteFieldDatum.{u}` supplies the finite field, its cardinality, and its
  fixed algebraic closure `D.k`. `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p`
  render the prime distinct from the characteristic. No Noetherian or dimension
  hypothesis is imposed on the input scheme.
- `T : Over (Spec (CommRingCat.of D.k))` is the scheme over that algebraic closure.
  `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom]` is finite type, and
  `[IsSeparated T.hom]` is separatedness. The coefficient closure is the existing
  canonical `PadicAlgCl l`; its finite subextensions are the existing
  `Padic.FiniteCoefficientFields l (PadicAlgCl l)`. These present the fixed
  algebraic closure in the node, not a completed algebraic closure.
- The output supplies `IsNoetherian T.left`, the finite dimension witness
  `Fact (∃ n : ℕ, topologicalKrullDim T.left ≤ n)`, and stalkwise invertibility
  `Fact (∀ x, IsUnit (l : T.left.presheaf.stalk x))`.
  `IsNoetherian` includes `CompactSpace`; the conjunction additionally supplies
  `QuasiSeparatedSpace T.left`. Thus qcqs and all other first-clause properties
  are conclusions. The output instances are used dependently in `Data`.
- The site throughout is `Scheme.ProEt.topology`, with objects in universe `u+1`,
  morphisms in `u`, and module/abelian section size `u+1`. No site universe equality
  is assumed. `pbcFiniteField` is the recorded canonical Shrink presentation of a
  finite subextension, with its actual inclusion `pbcFiniteFieldInclusion`.
- `Core.stage` uses `FdRationalStageComparison`. Its `integral_identity` identifies
  the two full integral subcategories through the existing quotient-normalized
  `integralDetailedTransport`, not through an arbitrary equivalence of categories.
  Its integral and rational equivalences retain every derived morphism, and its
  `objects` and `tensors` specify the raw localization on objects and pure arrows.
  The coefficient transport is the existing comparison of the same inverse limit
  and quotient projections. No Karoubi envelope is introduced.
- `finiteFreeTarget T A` is an object property on the ordinary ambient
  `DerivedCategory (pbcModules T A)`: an ordered bounded interval and, for every
  integer cohomology degree, a `FiniteLocallyClosedStratification` on whose strata
  the actual inverse-image modules are `IsFiniteLocallyFree`.
  Thus it describes the full target subcategory without extra completeness or Tor
  hypotheses. The definition uses existing pullbacks, cohomology and local freeness.
- `internalFiniteFreeTarget` expresses the same condition for internal abelian-sheaf
  modules. Its local trivializations use the existing pro-etale covers and
  `Mod.IsFree`, whose definition means a finite rank free module (not arbitrary rank).
  `Data.finite_constructibility` and `Data.closure_constructibility` give the two
  equivalences with the recorded `ProEtale.boundedConstructible` predicate, i.e.
  stratified local finite presentation, for the finite and native closure rings.
- `closureRing` is exactly the section ring of
  `ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T`.
  Its condensed sections take values in one finite subextension. It is not the
  entire continuous-map ring into the topological algebraic closure.
  `sectionDerived` is the derived equivalence induced by the recorded
  `InternalAbelianSheafModule.sectionModuleEquivalence`; additivity follows from
  preservation of binary products by an equivalence. `Data.finite_sections` and
  `Data.closure_sections` identify internal constructibility with the ordinary
  `finiteFreeTarget` after this actual section-module transport.
- `Core.realization E` is the existing `RationalModuleRealization` for the uniform
  integral category. `finiteFunctor` composes its `J` with `raw.family.Φ E` from
  the original raw category. `Core.fully_faithful` gives bijections on every Hom;
  `Core.image` gives precisely the finite-free essential image. Together these
  assert equivalence onto the specified full subcategory.
  Exactness and field linearity are retained, rather than postulated for an
  unrelated functor: `raw.finite_functor` identifies Φ with `stage.rational.functor`,
  which has `additive`, `shift`, `exact`, and the pure tensor identity `tensors`;
  `raw.exact` retains the specified shifts; `RationalModuleRealization.J` has its
  recorded additive, linear and triangulated structures. Its `objects` formula is
  derived extension along `integralIso.hom ≫ inclusion`, so, after the fixed
  inverse-limit coefficient comparison, it is exactly `E_T ⊗^L_{B_E,T} K`.
  Its `fractions` formula and the stage `tensors` formula render `u ⊗ a` as
  the image of `u` multiplied by the image of `a`.
- `Core.raw` uses `FdCompletionScalarComparison`, whose integral `chi` field fixes
  the quotient-tower map, including the zero shifted-product coordinate and actual
  tensor-generator transport. `scalarComparison` is DEFINED to be its beta inverse
  followed by the continuous tensor comparison `ScalarData.theta`.
  `ScalarData.integral` identifies theta with the existing
  `RationalRealizationScalarComparison.theta`, whose `integral_normalization` is
  the balanced multiplication comparison on integral representatives and whose
  coefficient map sends functions pointwise through the field inclusion.
  Natural isomorphisms act on every rational arrow; the raw tensor and fraction
  normalizations fix the scalar in both routes as the same image of `a`.
- `Coherence.coefficient_comp` fixes the composed coefficient maps.
  `Coherence.tower` is the direct-versus-successive equation using the ACTUAL
  `GeneralAlgebraicallyClosedCoefficients.stageSystem.assoc` and
  `pbcReductionNormalization`. The latter is the universal derived balancing
  comparison, normalized on K-flat representatives by multiplication of the
  scalar factors. Thus the tower is `g ⊗ (f ⊗ (e ⊗ x)) ↦ gfe ⊗ x`.
  `Coherence.unit_normalization` fixes the ordinary tensor unit on every section
  as `a ⊗ x ↦ a • x` and fixes its derived map by the specified complex counit.
  `Coherence.identity` uses the existing completed-scalar `unitor` itself.
  Its `HEq` accommodates only the published abstract stage-system presentation
  versus its specified concrete identity-transition presentation; it does not
  introduce a new unitor or weaken the map equation.
- `ClosureData.finite_normalization` fixes the finite section-ring isomorphism
  pointwise using `chartComparison` and the actual Shrink algebra equivalence.
  `leg_normalization` and `coefficient_normalization` use exactly the published
  condensed finite-field inclusions and their section-ring maps; `cocone` gives
  their equality after extension. This prevents arbitrary choices of ring maps.
  `closureComparison` is DEFINED by extending `scalarComparison` along these legs
  and applying the canonical adjunction-derived balancing isomorphism.
  `Data.closure_tower` and `Data.closure_identity` assert the corresponding actual
  tower and identity equations after scalar extension to `R_T`.
- The common-stage pair category is the recorded
  `generalAlgebraicallyClosedConstructibleCategory`; the node only introduces this
  notation, and asserts no additional pair-category equivalence. Its actual finite
  transitions and associators are exactly those used in the comparison equations.

### Dependency declarations used

| Recorded module | Declaration or interface used |
| --- | --- |
| `Sheaf.Paper.FiniteFieldFiber` | `WeilConjectures.FiniteFieldDatum` |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` | `Scheme.ProEt`, `ProEt.topology` |
| `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` | recorded completed integral sheaf and quotient cone; reexports the completion |
| `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` | `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj` |
| `Sheaf.Paper.CompletedCondensedCoefficients` | `completedCondensedIntegral`, `completedCondensedRational`, finite-field coefficient comparisons |
| `Sheaf.Paper.SfRationalizationKaroubi` | `sfIntegralConstructibleCategory`, `sfRationalConstructibleCategory`, raw localization |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | `Stage`, `stageSystem`, `unitor`, actual completed scalar transitions |
| `Sheaf.CategoryTheory.RingedSiteModules` | `CategoryTheory.ringedSiteModules`, specialized `pbcModules` |
| `Mathlib.Algebra.Homology.DerivedCategory.Basic` | `DerivedCategory`, standard homology and boundedness |
| `Sheaf.Paper.IntegralUniformCoefficient` | `PbcIsBoundedConstructibleComplete`, reexported through the existing stage category |
| `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` | general internal `boundedConstructible`, retained by the recorded module |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | `completedScalarComparison`, `finiteFreeCompletedScalarComparison`, via the normalized raw interface |
| `Sheaf.Paper.FdCoefficientComparison` | `FdRationalStageComparison`, `FdOrdinaryScalarTransport` |
| `Sheaf.Paper.FdCompletionInverseScalarCoherence` | `FdCompletionScalarComparison`, including integral chi and raw beta |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | `RationalModuleRealization` |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | `RationalRealizationScalarComparison` |
| `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` | `sectionRingSheaf`, `sectionModuleEquivalence` |
| `Sheaf.Paper.ContinuousCoefficientModuleEncoding` | `CondensedRing.sectionRingMap` |
| `Sheaf.Paper.ContinuousCoefficientRealizations` | `chartComparison` and its point-adjunction normalization |
| `Sheaf.Paper.BoundedConstructibleTower` | `pbcReductionNormalization`, derived scalar adjunctions and composition |

The additional statement dependencies name definitions, not existence theorems:
`def-fd-coefficient-comparison-datum` retains ownership of the raw stage comparison;
landed `def-pur-inverse-scalar-coherence` owns the inverse-scalar coherence module;
`def-sf-rational-module-realization-datum` and
`def-sf-rational-realization-scalar-comparison` below bind directly to the two
existing plain structures. The item does not use the Nonempty conclusion of any
of the three theorem nodes removed from its former statement dependencies.
The accepted split, mathematical statement, and proof dependencies are unchanged.

The original proof dependencies are retained and imported: scheme dimension from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; Noetherianity/qcqs
from the recorded Mathlib morphism instances; integral characterization from
`IntegralStratifiedPerfectCharacterization`; finite and closure local triviality
from `CondensedFieldLfpLocalTriviality` and `CondensedQbarLfpLocalTriviality`;
`CondensedERealization`, `CondensedFlatCoefficientCalculus`,
`ContinuousCoefficientImmersionRestriction`, `ScalarCompletionAssociator`,
`OrdinaryDerivedChangeOfRings`, and
`ModuleObjects.InternalTensorCompositionUnitNormalization`.
The theorem docstring gives the complete six-step natural-language assembly proof.

### Edge cases

Checked against the definitions before and during the second reading:
empty `T` (the empty stratification is permitted and all section conditions are
vacuous); zero cohomology and rank zero (finite rank includes zero); negative and
zero cohomological degrees (all integer degrees, with an ordered bounded interval);
`E = F`, repeated fields and the all-equal tower (explicit normalized unit and
actual unitor equations); ramified extensions (the quotient-normalized chi is used,
not a presumed equality of uniformizers); torsion integral morphisms and zero raw
arrows (the raw tensor/fraction formulas remain valid); arbitrary finite fields in
the chosen closure and arbitrary scheme universe (canonical coefficient Shrink and
section ULift, no size equality); further extension to the bounded-image closure
ring (actual native coefficient legs, not an arbitrary coefficient map).
No false-statement counterexample or statement dispute was found.

### Searches

All search wrappers were run as group NP for this item.

- LeanFinder: `Coherent continuous realizations of raw rational adic finite coefficient
  diagram scalar extension equivalence`. Eight results, chiefly adic completion
  and scalar-extension algebra; no existing theorem states this cocone.
- LeanSearch: `Exact equivalence raw rational adic constructible sheaves continuous
  coefficient scalar extension coherence`. Eight results including
  `Padic.adicCompletionEquiv`, `LinearMap.extendScalarsOfIsLocalizationEquiv`, and
  Laurent-series completion comparisons; no match.
- Loogle: `Functor.IsEquivalence, NatIso, Linear`. No results; the tool reported
  unknown `Functor.IsEquivalence`. This negative query was supplemented by the
  two natural-language searches and the source searches below.
- Mathlib grep via msearch: `realization|scalar.*[Cc]oherence|[Cc]ompletion.*[Aa]ssociator`
  in `CategoryTheory`: six unrelated geometric realization entries, no match.
- Repository `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id and adic realization/scalar
  coherence/completion associator keywords: the exact item has no existing
  declaration; related published interfaces above were found and reused.
- Targeted source searches for `rationalCoefficientSheaf`, `sectionRingMap`,
  `chartComparison`, `pbcReductionNormalization`, `FdRationalStageComparison`, and
  `FdCompletionScalarComparison` located the exact normalization declarations
  used. The relevant DAG node records were read with their signatures/docstrings.

### Validation

Every compile uses the prescribed server `scompile.py`. Errors encountered while
elaborating were repaired: explicit public imports for section-module declarations;
additivity of the derived equivalence; use of the natural adjunction composition iso
rather than an objectwise iso; and heterogeneous equality for the two published
identity-transition presentations. No tests or global builds are used.
Final server compilation passed under both the sandbox and final library module names.
The prescribed `deliver2.py --no-push` passed preflight and compilation, printing
`OK (dry run): commit 4c5127a944f passes the preflight and compiles; nothing pushed`.
Only the expected declaration-uses-sorry warning is permitted; no errors or other
warnings remain.

## Second reading by NP

The dispatcher explicitly forbids starting other agents, so this is a separate
self-reading with the node and module open, not a claim of independent-agent review.
The maintainer's independent delivery review remains applicable.

I checked the hypothesis list against the final theorem: finite-field algebraic
closure, prime distinct from characteristic, separated finite type, with all
Noetherian/dimension/invertibility/qcqs properties concluded. I then checked every
conclusion against the definitions and the actual imported structure fields.
The integral identity uses the normalized coefficient transport; raw localization
retains its pure arrows; full faithfulness plus exact essential image gives the
specified full-subcategory equivalence. The realization record fixes derived tensor
on integral representatives and its scalar formula. Scalar j is a real composite
of beta inverse and normalized continuous balancing. The tower uses the source's
actual associator, and the identity uses its actual unitor.

This reading found and repaired a potential ambiguity: a finite section-ring
isomorphism alone would permit a twisted identification in the closure legs.
`ClosureData.finite_normalization` now fixes that isomorphism at every section and
point via the existing `chartComparison` and canonical Shrink algebra map.
The native closure uses finite-subextension-valued sections throughout. Both
constructibility presentations and their section-module comparison are asserted.
The final identity equations require HEq solely because the upstream stage-system
interface presents the same transition via a specified abstract functor; the maps
on both sides are the prescribed maps, not freely chosen replacements.
No clause of the node was dropped or changed. The helper declarations introduce
no arbitrary replacement functor, coefficient ring, completion map or associator.


## Repair of return H2

Returned immutable head: `616951560d9b`. The maintainer accepted the mathematics
and identified one dependency-ownership defect: three theorem nodes were cited
only to obtain the types of their plain data structures, rather than their
Nonempty conclusions. I removed
`lem-fd-completion-inverse-scalar-coherence`,
`lem-per-rational-module-realization-functor`, and
`lem-per-rational-realization-scalar-coherence` from `stmt_deps`.
I retained `def-fd-coefficient-comparison-datum` and replaced the removed entries
with landed `def-pur-inverse-scalar-coherence` and the two new existing:true
definition nodes below. The current read base contains
`dag/nodes/sec-smooth-purity/def-pur-inverse-scalar-coherence.json`, whose
`lean.module` is `Sheaf.Paper.FdCompletionInverseScalarCoherence`; delivery uses
the current base through the prescribed wrapper.

The item on the current main read clone and the retained returned node differ
only in `lean` and the added statement dependencies. I preserved the current
accepted main node fields, and the module is byte-for-byte the accepted returned
module (SHA256 `b66c9f6fa33651aa221e562dac16dea77ba7bea2c06b19e6f524a5130c27d96b`).
No rebase alone is claimed as the repair: the new definition-owner nodes and the
replaced item dependencies are the concrete change. There was no released repair
note file for this item in the read clone.

## New nodes

`def-sf-rational-module-realization-datum` binds existing:true to
`AlgebraicGeometry.Scheme.RationalModuleRealization` in
`Sheaf.Paper.RationalModuleRealizationFunctor`. It defines the normalized record
with quotient/limit/localization coefficient identifications; locally closed
restriction; constant-section field action; exact ordinary scalar extension and
its triangulated derived functor and cohomology comparisons; bounded finite-free
constructibility; the raw E-linear triangulated functor with object/fraction
formulas; and ordinary finite-free models for every finitely presented integral
module, including torsion. It asserts neither existence nor full faithfulness.
Its hypotheses are exactly the finite coefficient extension and Noetherian,
finite-dimensional scheme with l invertible of the existing structure's section
parameters. Source: BS 6.8.2, 6.8.11(3), 6.8.14(2). The node cites the existing
definitions for its site, coefficients, module/derived/tensor categories, raw
rationalization, cohomology and continuous coefficient restrictions/models.
The recorded Lean signature is copied verbatim from the structure declaration;
no module or declaration is added for this node.

`def-sf-rational-realization-scalar-comparison` binds existing:true to
`AlgebraicGeometry.Scheme.RationalRealizationScalarComparison` in
`Sheaf.Paper.RationalRealizationScalarCoherence`. Its parameters are l prime,
finite E,F, a Q_l-algebra embedding, the same scheme hypotheses, and given
realization records. Its fields are the continuous coefficient map, its
pointwise field-inclusion normalization, its actual completed integral
coefficient square, theta, and its exact balanced normalization on every
integral representative (coefficient, coefficient_normalization,
coefficient_square, theta, integral_normalization). No existence or tower theorem is asserted.
The two flattening routes use pbcReductionNormalization and the object equalities
of the supplied realization records, exactly as in the source declaration.
Source: BS 6.8.2, 6.8.14(2), 6.8.15. It cites the realization definition above
and the recorded coefficient/scalar/derived/tensor definitions and the actual
well-defined raw scalar functor supplied by prop-weil-pbc-scalar-extension.
Again the signature is verbatim and there is no new Lean module.

For both nodes I searched the complete DAG definition ownership, Mathlib,
WeilConjectures and Sheaf. Only the two existing Sheaf structures were found;
no definition node already owns either. LeanSearch and LeanFinder returned eight
unrelated rational-module or scalar algebra hits for each query, and Mathlib grep
for both structure names returned zero hits. The complete wrapper outputs and
queries are embedded in each node's mathlib_searches. Source rg located the
structures at RationalModuleRealizationFunctor.lean:93 and
RationalRealizationScalarCoherence.lean:73. Blueprint searches for the natural
phrases and exact names returned no nodes; the item's ancestor is None, which is
retained as null provenance and supplemented with its native biduality origin.
The existing structures are reused directly, not recreated. Both new nodes carry
required import_flags and are cited by the item.

### H2 second reading

I reread the two published structure bodies and their section binders against
the new definition statements and lean records. Each field of the realization
record is represented: all coefficient comparisons and normalizations, restriction
square, module action, ordinary/derived exactness, cohomology, constructibility,
J and its additive/linear/shift/triangle structures, objects, fractions and models.
Each field of the scalar-comparison record is represented: coefficient,
coefficient_normalization, coefficient_square, theta and integral_normalization.
The latter is the actual two-route equation, not an arbitrary natural iso.
The new nodes define types of data and do not claim Nonempty; their empty proof
and proof_deps reflect this. They do not use the existence theorem statements.
The prior second reading of the accepted Lean mathematics remains applicable,
with the independent-agent restriction explicitly noted above.

### H2 repair validation

The unchanged module passed the prescribed scompile.py server checks under both
the sandbox and final library names. The repaired delivery then passed
`deliver2.py NP lem-sf-adic-finite-realization-cocone --no-push`, which compiled
its existing-declaration probes and the module and printed
`OK (dry run): commit 6389a048a9e passes the preflight and compiles; nothing pushed`.
Both new existing:true signatures were also checked verbatim against the published
sources, every new node dependency exists, and an in-memory traversal of statement
and proof dependencies confirmed no cycle back to this item. The item differs
from the current main node only in the permitted lean and stmt_deps fields.
