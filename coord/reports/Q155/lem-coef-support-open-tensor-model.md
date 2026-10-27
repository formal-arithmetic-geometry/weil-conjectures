## Worker report

The item module states `WeilConjectures.CoefSupportOpenTensor.supportOpenTensorModel`.
It uses ordinary unbounded derived categories throughout, and indexes the positive
quotient exponent by `n + 1`. Definitions contain real functors, maps, structures
specifying the claimed conclusions, and canonical composites. The sole new
postponed mathematical assertion is the named main theorem, whose docstring gives
the six-step proof from the node. Structural witnesses are existential conclusions,
not extra hypotheses.

The coefficient hypotheses are `(l : ℕ) [Fact l.Prime]`, a field `E : Type u`,
`[Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Rings, quotient maps, completed
coefficient sheaves, exact scalar restriction and derived reduction are the recorded
project constructions. The common ambient universe contains the field and schemes;
the pro-etale site still has object universe `u + 1` and morphism universe `u`,
and coefficients and module values are lifted to `u + 1`. There is no replacement
of the small pro-etale site by an equal-object-and-morphism-universe site.

Hypotheses and clauses, in the order of the node:

- `k` has `[Field k]`, and `_hl : IsUnit (l : k)` says exactly that ell is invertible.
  `X.Over (Spec (.of k))`, `Y.Over ...` supply the two k-schemes. Locally finite type
  and quasi-compact structure morphisms say finite type. `a.IsOver ...` says it is
  a k-morphism; `IsSeparated a`, `LocallyOfFiniteType a`, `QuasiCompact a` say
  separated finite type. `c : Compactification a` supplies the fixed open `c.i`,
  proper `c.g`, and their composite equation. No compactification is newly chosen.
- `operation l E c` is native exact sequence-site open extension followed by the
  separately right-derived proper image. Its finite evaluation uses the recorded
  `compactSupportSystemEvaluation`, with `sfIntrinsicCompactSupport c A_(n+1)`.
- The existential `SX : CoefficientDerivedSystemCalculus ... X` includes the canonical
  derived reduction, its scalar adjunction, its simultaneous flat-term K-flat
  representative `P tensor A_(n+1)`, all quotient maps, and the reduction evaluations.
  It introduces no condition on `K`. The theorem quantifies all unbounded `K`.
- `tower l E c SX` is defined as `SX.reduction`, then `operation`, then
  `coefficientSequenceDerivedRestriction`. Thus the first displayed whole-derived
  realization identifies the specified lifting composite itself, rather than an
  arbitrary tower selected merely from its finite values. The predecessor tower
  theorem only existentially quantifies a tower; the item explicitly requires its
  constructed lifting composite. This definition follows node proof step 2 and its
  stage-1 review instruction.
- `evaluation` composes the actual restriction/evaluation isomorphism, the native
  compact-support evaluation, and `SX.reductionEvaluation`. Its codomain is
  `compactSupportRestrictedLevel`, exactly `Res_n F_n K_n`. The first quantified
  equality in the main theorem identifies every `m → n`, including `m = n`, with
  `compactSupportRestrictedTransition`: compact support of the quotient reduction
  map followed by the specified scalar comparison.
- `ordinarySections`, `ordinaryQuotientSections`, `ordinaryLevelSections` are actual
  R-linear sections with the structural constant-to-completion scalar action.
  `integralSections`, `quotientSections`, `levelSections` are their total right
  derived functors. Their targets are derived categories of strict R-module
  towers or R-modules. None takes an inverse limit. The imported `coefTrace*`
  structural helpers are reused; neither the finite dualizing theorem nor the
  trace-rectification theorem is invoked.
- `SectionsModel.comparison` is the point-square comparison on the entire derived
  quotient-system category, fixed by `comparison_unit` on the canonical derived
  units. Its evaluation comparison is likewise fixed by `evaluation_unit`, and
  `transitions` retains every actual tower arrow. `pointComparison` is that same
  comparison applied to the compact-support lifting composite; `pointEvaluation`
  gives the natural R-linear finite values `RΓ(Y,F_n K_n)`. The final main-theorem
  equality says that their arrows are derived sections of precisely the same
  `compactSupportRestrictedTransition`.
- `SystemOpenModel` uses the actual quotient sequence rings, native module open
  extension and pullback, and the actual inverse-image unit on sections. Its
  `gamma` is a natural isomorphism on all pairs of unbounded derived objects
  `U,L`. Its inverse adjoint-transpose equation is the open-unit normalization of
  `lem-sf-open-tensor-normalization`. No tensor over the completed ring is identified
  with a tensor over the quotient sequence ring.
- The restriction comparison is fixed on the actual sheafified pure tensor
  generators (`restrictionPure`). The ordinary open comparison is fixed by its
  adjoint-unit equation (`ordinary_inverse`), giving the localized formula
  `[u]_f tensor l ↦ [u tensor l|_X]_f`. `chain` is a genuine morphism of the existing
  signed direct-sum total complexes; `summand` fixes every bidegree summand to that
  ordinary map. In particular it commutes with the differential and, because it is
  a morphism of modules on the full sequence site, with all horizontal semilinear
  restrictions. It is not merely a family of unrelated finite chain maps.
- The existing `RingedDerivedTensorComparison` permits any pair with at least one
  K-flat factor. `OpenTensorModel.ambientBoth`, `ambientNaturality`, `openBoth` and
  `openNaturality` reuse its recorded agreement and naturality conditions. Thus
  the representative clause permits arbitrary first `C` and requires only the
  second `P` to be K-flat with flat terms. Pullback retains K-flatness and flat
  terms; `derived_model` says the localized chain map is exactly `gamma`. This
  supplies the representative and independence clauses without defining a second
  one-K-flat tensor comparison.
- `FiniteOpenModel` uses the same unit normalization over each actual constant
  finite ring. `GammaEvaluation` is the equality of the evaluated derived natural
  transformation with this finite canonical transformation, through the recorded
  open, restriction and tensor evaluation comparisons, for every `U,L,n`.

Dependency declarations used (all signatures and docstrings read):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing`, its finite instance, and the actual quotient maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the completed ring.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- Mathlib's `DerivedCategory`, standard localization, and exact derived functors.
- `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceModules`,
  `coefficientSequenceDerivedRestriction`, `coefficientRestrictedEvaluationIso`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` and
  `Sheaf.Paper.CoefficientRingedTensorHomModel`: the recorded ordinary derived
  internal Hom, `CoefficientClosedStructure`, `CoefficientTensorModels`.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionDerivedRestriction`.
- `Sheaf.Paper.CompactSupportReductionTower`: the existing strict-tower statement,
  `compactSupportRestrictedLevel`, `compactSupportRestrictedTransition`.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`:
  `exactDerivedAdjunction`, owned by `def-weil-exact-derived-adjunction`. The older
  normalization theorem is a source of the normalization equation, with its
  incompatible tensor-model interface explained below.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, its tensor, reduction and evaluation models.
- `Sheaf.AlgebraicGeometry.VaryingRingOperations`: `extension`, `pull`, `moduleAdj`,
  `moduleJAdj`, `J`, `G`, `P`, `evalJ`, `evalG`, and native exactness instances.
- `Sheaf.Paper.CompactSupportNativeSystemEvaluation`:
  `compactSupportSystemLevel`, `compactSupportSystemQuotient`,
  `compactSupportSystemEvaluation`. The transition theorem is a proof dependency
  of the DAG, not a declaration used by this statement; its import is removed.
- `Sheaf.Paper.SemilinearSystemModels`: the recorded module tensors, pure sections,
  total summands, two-K-flat model and `TensorComparisonModel`.
- `Sheaf.SixFunctors.CoefTowerTraceRectification`: only existing structural helpers
  `coefTraceRing`, `coefTraceConstantScalars`, `coefTraceSystemRestriction`,
  `coefTraceSections`, `coefTraceEvaluation`, `coefTraceTransition` and their
  categorical instances. No assertion involving finite dualizing objects is used.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  `Functor.rightDerivedFunctorUnitQ`; `...Sites.SectionsWithSupport` gives the
  additive section instance.

Edge cases checked against the types: empty open (no nonemptiness assumption),
identity open (the unit normalizations specialize to the identity tensor map),
zero inputs, equal indices (the all-pair transition includes the identity),
nonflat quotient changes (no flatness hypothesis on quotient homomorphisms),
unbounded and non-K-flat first representatives, and all representative changes.
All point-sections outputs remain strict towers before limits.

Existing-declaration searches:

- `msearch.py leanfinder`, query “Derived compact support of quotient coefficient
  sequences agrees with the reduction tower and normalized open extension tensor
  comparison”: eight tensor/adic quotient hits, none with this statement.
- `msearch.py loogle`, query `CategoryTheory.Sheaf, CategoryTheory.Adjunction`:
  twelve generic sheafification/adjunction facts, no compact-support system model.
- `msearch.py grep`, query `compactSupport.*[Tt]ower|extensionByZero.*[Tt]ensor`:
  no Mathlib matches.
- `msearch.py leansearch`, query “Derived extension by zero tensor projection formula
  for strict coefficient systems and reduction towers”: eight generic derived
  category, projective resolution and Kaehler differential hits, no exact statement.
- `rg` in `lean/WeilConjectures` found the etale-adic compact-support tower, whose
  category and inputs differ from ordinary quotient-sequence module categories.
  The literal item-id search found no matching declaration there.
- `rg` in `lean/Sheaf` found `CompactSupportSystemRealizationNormalization` and
  `CompactSupportNormalizedRealization`. Their Frobenius/constructibility/finite-Tor
  settings do not state this arbitrary-unbounded realization plus open comparison.
  The existing tower, native-system, tensor-model and open-normalization declarations
  are imported and used rather than copied.

No source correction or statement dispute was needed. The new definition nodes
below package the normalized open representative and native evaluation data in
separate modules, so all three files compile within the per-file limit. No replacement dependency
module is introduced. Existing one-K-flat tensor comparisons are reused.

## Second reading by Q155

This is the dispatcher's single-worker author rereading; no independent reviewer
is claimed. The maintainer performs the independent delivery review. The node and
file were reread clause by clause in the mapping above. The checks specifically
retain arbitrary `K,U,L`, the actual lifting composite rather than an arbitrary
existential tower, every quotient-semilinear arrow, the signed total complex, a
K-flat condition on only the second representative, and R-linear point sections
without a limit. Canonical unit equations and finite gamma evaluation equations
were made explicit during this rereading.

## New nodes

`def-coef-support-point-sections-data` defines the actual section functors and
unit-normalized `SectionsModel` in `Sheaf.Paper.CoefSupportPointSectionsData`.
It extracts the unchanged point-sections data from the returned item; the source,
searches, clause mapping and edge cases are detailed under the compilation repair
below. It asserts no existence theorem and introduces no postponed proof.

`def-sf-open-tensor-representative-data` defines `OpenTensorModel` in
`Sheaf.SixFunctors.OpenTensorRepresentativeData`. It packages the ordinary pure-tensor,
open-unit, signed total-summand, arbitrary-first-representative and derived
normalizations used in proof steps 5–6 of the item. It makes no existence assertion
for arbitrary exact adjoint functors. Its existence for the actual native open
functors is part of the item's conclusion, including all finite evaluations.
The source is the same blueprint paragraph 2 and its agent-extracted subargument,
with Stacks 0E8I, 0GL1, 07A4 and 06YT. The new node cites the existing ordinary
module tensor and `RingedDerivedTensorComparison` definitions, including their
naturality and agreement conditions, rather than introducing duplicate tensors.

LeanFinder and LeanSearch returned eight elementary flat-module tensor results each;
Mathlib grep returned no matching representative-data package. DAG/blueprint and
project searches found the existing general one-K-flat tensor comparison, which is
now reused directly, and the existing open-normalization theorem, which is also
reused. None packages the whole ordinary/chain/derived normalized representative
clauses needed here. Exact tool output is retained in the new node's
`mathlib_searches`. The definition's fields correspond to clauses (i)–(v) of the
new node statement. Its edge case of arbitrary exact adjunctions is handled by
making this a data definition without claiming inhabitation; the main theorem
only asserts its existence for the specified geometric open adjunction.

The author rereading also checked this new definition against its Lean fields:
restriction and pure generators, inverse adjoint-unit equation, each signed total
summand, reused natural one-K-flat comparisons, flat-term pullback, natural gamma,
and its exact one-K-flat chain-representative equation are all explicit.

`def-coef-native-open-tensor-evaluation-data` defines the native system and finite
specializations, their actual gamma projections, and `GammaEvaluation` in
`Sheaf.Paper.CoefOpenTensorEvaluationData`. Its first clauses are `SystemOpenModel`
and `FiniteOpenModel`, supplied the real native functors, exactness instances,
ordinary adjunction and inverse-image section units (`pullSection`,
`finitePullSection`). `systemGamma` and `finiteGamma` extract the gamma field with
all site universes and exact-functor instances specified. `GammaEvaluation` is the
explicit equality through tensor evaluation, `evalJ` and `evalG`, for all `n,U,L`.
It makes no existence assertion; that remains the item's theorem. This missing
compatibility-data interface is separated so each file remains within the compile
limit, without altering any ring, site, functor or hypothesis. Its source is the
same blueprint paragraph and item steps 5–6, Stacks 0GL1 and 07A4.

LeanFinder and LeanSearch searches for finite evaluation of the canonical native
open tensor comparison, Mathlib grep of its model/predicate names, both project
source trees, the DAG and blueprint search found no existing definition of this
interface. Their exact outputs are recorded in the new node. The general tensor,
open normalization, native geometric and finite evaluation declarations are all
reused. The author rereading checked the two actual sites and ring actions, the
positive `n + 1` indexing, the unit on actual sections, the two gamma projections,
and every arrow in the finite-evaluation equation. Empty and identity opens,
unbounded inputs and all finite levels are retained.

Original validation: `scompile.py Q155 lem-coef-support-open-tensor-model` compiled all three
delivery modules separately in dependency order, including their final library
names, with no errors or warnings. Final-name times were 36.9 s for generic
representative data, 13.1 s for native evaluation data, and 49.1 s for the item.
Only the expected stage-2 named theorem is left with `sorry`.

The first delivery preflight found only combined citation brackets in the two new
node statements. Each dependency now has its own literal `[id]` citation. The Lean
sources and mathematical statements were unchanged by this metadata correction.


The third new node, `def-coef-constant-scalar-tower-sections`, reuses the existing
constant-integral-scalar restriction, quotient-system restriction and tower-valued
sections definitions from `Sheaf.SixFunctors.CoefTowerTraceRectification`. Its
source, exact searches and clause mapping are documented in the repair below.
It writes no module and asserts no theorem.

## Repair of immutable head 771bdcbd7e70

Compared the saved packet with the current read-only main tree: the item on main
has no Lean record, and the two original new nodes have not landed. Retained the
accepted mathematics and all declaration signatures. The initial required dry run
compiled the first two files but timed out on the main file, including the server
confirmation. Removed the theorem-only native-transition import and the main
normalization-theorem import, and imported its Data module in the generic model.
The next prescribed `scompile.py` compiled all three files with no errors or
warnings: final library names took 18.5 s, 11.9 s and 43.5 s respectively.

1. Replaced the two theorem citations used only for structure types with
   `def-coef-derived-system-calculus-data` (item and native evaluation data) and
   `def-zl-ringed-derived-closed-symmetric-monoidal-data` (item and representative
   data). The former owns `CoefficientDerivedSystemCalculus` and its tensor
   interface; the latter owns `RingedDerivedTensorComparison`,
   `RingedDerivedTensorBothModel` and `RingedDerivedTensorNaturality`.
   Dropped `lem-weil-compact-support-native-system-transition` from the item's
   statement dependencies and removed its unused import; its original proof
   dependency and six-step proof plan are retained. Added
   `def-weil-exact-derived-adjunction` as the owner of `exactDerivedAdjunction`,
   including in the representative-data node's statement and dependencies.
2. Added the requested missing statement dependencies:
   `def-weil-pbc-bounded-constructible-tower` for `pbcTowerEvaluation` and
   `pbcTowerTransition`, `def-coef-tower-trace-constructions` for `coefTraceRing`,
   `coefTraceEvaluation` and `coefTraceTransition`,
   `def-sf-scalar-reduction-categories-restriction` for `scalarReductionSource`
   and `scalarReductionDerivedRestriction`, and
   `prop-pur-kinjective-resolutions-exist` for `sequenceGrothendieck`.
   Added the existing-definition node `def-coef-constant-scalar-tower-sections`
   described below, directly cited by the item.
3. Read `Mode.systems`, `Operations`, `Assertion.gamma`, `gamma_inverse`, and
   the underlying `ProjectionRestriction.TensorModel`/`TensorComparison` types.
   The older `TensorModel` gives a bifunctor, comparison on simultaneous
   flat-term K-flat resolving pairs, and descent. It does not give the
   `CoefficientClosedStructure` for the fixed internal Hom or a conversion to
   `CoefficientTensorModels`; those are the actual tensors supplied by
   `CoefficientDerivedSystemTensors`. Nor does it provide the arbitrary-first,
   one-K-flat representative clause. The older open functors also use localized
   ringed-site restriction and chosen extension, whereas this statement uses
   the native varying-ring pullback and extension. Consequently its gamma cannot
   be inserted directly into `SystemOpenModel` or `FiniteOpenModel` at these
   fixed interfaces. This precise reason is now in the item's and generic
   representative-data node's `lean.note`, as the return permits.

The relationship of the normalizations is explicit: the old
`Assertion.gamma_inverse` and `OpenTensorModel.gamma_inverse` both transpose the
inverse gamma under the localized open adjunction to tensor of the open unit
with identity followed by the inverse restriction/tensor comparison. The latter
uses the existing `exactDerivedAdjunction`. Its `restrictionPure`,
`ordinary_inverse`, `summand` and `derived_model` fix the ordinary and signed-chain
representatives, then their localization, for the supplied closed tensor models.
After representative-preserving comparisons of the tensor presentations and the
native/localized open adjunctions, these inverse transposes coincide; injectivity
of the adjunction Hom equivalence identifies gamma. The delivery records the
interface diagnosis, rather than adding an unproved comparison theorem or an
extra hypothesis to the item. The older theorem stays cited in the item as the
source of this canonical normalization; its theorem module is not imported just
to access data owned by a separate node.

The repair rereading opened the item, both new-data nodes and their Lean fields.
It checked that the tower is still the actual lifting composite, every comparable
pair including equal indices is present, the point-sections comparisons still
satisfy their unit equations, and the gamma representative uses an arbitrary
first complex and a flat-term K-flat second complex. Empty opens, identity opens,
nonflat quotient transitions, arbitrary unbounded inputs, positive n+1 indexing,
and sections before limits are unchanged. No statement correction is made.

Additional new node: `def-coef-constant-scalar-tower-sections` records the exact
existing `coefTraceScalar`, `coefTraceConstantScalars`, `coefTraceSheafTowers`,
`coefTraceSystemRestriction` and `coefTraceSections` in
`Sheaf.SixFunctors.CoefTowerTraceRectification`. Its source is blueprint
`prop-coef-integral-dualizing.proof.md` paragraph 2, the scalar/point-sections
square before limits. The scalar is the actual final-object constant section
into the completed ring; restriction preserves the underlying sheaf and actual
quotient arrows; sections evaluate at the final object level by level with
strict R-module tower values. It asserts no exactness or trace theorem.
LeanFinder returned eight generic scalar-restriction hits; LeanSearch returned
`SheafOfModules.restrictScalars` and related generic module facts; Mathlib grep
found no specialized helper names. Project grep found these exact definitions
(lines 65–91, 121–143 and 183–191); DAG grep found ownership only in the theorem
`lem-coef-tower-trace-rectification`, not in a definition node. The blueprint
search for "constant scalar" found only the general derived-category definition.
The exact outputs are recorded in its `mathlib_searches`. Reusing these definitions
adds no module and no duplicate definition. Empty schemes and zero towers are
allowed; the section functor retains all indices and does not take a limit.


## New nodes (compilation repair)

`def-coef-support-point-sections-data` owns `SectionsModel` and its concrete
ordinary and derived section functors, now in
`Sheaf.Paper.CoefSupportPointSectionsData`. These are the same definitions and
three unit/evaluation/transition equations from the returned module. The three
equations are factored into named Prop definitions `sectionsComparisonUnit`,
`sectionsEvaluationUnit` and `sectionsEvaluationTransitions`; unfolding yields
exactly the former structure-field types. This avoids expensive elaboration of
those equations as dependent structure fields. Its source is blueprint paragraph
2, item proof step 4, Stacks 0D6E and 0941. It asserts no existence theorem.

The searches for this extraction ran with LeanFinder (derived point sections
and exact scalar restriction with unit-normalized evaluation), LeanSearch
(strict module tower values and derived-unit-normalized evaluation), Mathlib,
upstream, project and DAG grep for `SectionsModel|ordinaryQuotientSections|integralSections`,
and blueprint search for "point sections". Exact results are in the node.
The generic internal-Hom sections models, specialized Frobenius sections and
finite-Tor coefficient sections found in the project do not give this data type;
the blueprint hit is exactness at torsion stalk points. Every constituent is reused.

Clause mapping: `ordinarySections` applies the actual constant scalar restriction
then point sections; `ordinaryQuotientSections` first applies actual quotient-system
restriction; `ordinaryLevelSections` evaluates at the final object.
`integralSections`, `quotientSections`, `levelSections` take their total right
derived functors. `sequenceGrothendieck` applies the recorded ringed-site resolution
theorem. The three named Prop definitions state respectively the point-square
derived-unit equation, the derived-unit equation after finite evaluation, and
the all-pair transition square. `SectionsModel` consists of its two natural
isomorphisms and these three exact predicates. The original main theorem still
existentially supplies this data and uses the same `pointComparison` and
`pointEvaluation`. Empty and identity sites, zero objects, equal indices and
unbounded complexes remain allowed; no limit or extra hypothesis appears.


Final author self-check: all four delivered module signatures match their JSON
records verbatim. The main item differs from current main only in `lean` and
`stmt_deps`. Its original statement and proof are unchanged. The three new data
nodes use their source constructions, have no existence theorem, and contain no
`sorry`; the only new postponed assertion is still `supportOpenTensorModel`.
The new existing-definition node introduces no Lean declaration. All module
lines fit 100 characters and every binder remains explicitly bound.
After factoring the equations, the prescribed four-file compilation returned
success with no errors or warnings; the main module's final library compilation
took 16.5 s. The delivery dry run additionally checks the existing declarations.
