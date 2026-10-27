## Worker report

This delivery states `lem-pur-compact-support-strict-scalar-mate`. It constructs the
map itself, in the derived category of strict constant-integral towers, and leaves
all mathematical assertions as named `sorry` theorems. Definitions contain real
functor compositions, adjunction mates, or choices from uniquely normalized
universal properties. No arbitrary isomorphism is chosen from mere existence.

The main declaration is
`WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate` in
`Sheaf.Paper.CompactSupportStrictScalarMate`. The remaining clauses of the same
node are its listed helper declarations, notably `factors_isIso`,
`proper_biproduct`, `strictProper_biproduct`, `proper_geometric_transpose`,
`strictProper_geometric_transpose`, `openTensor_ordinary`, `open_base_ordinary`,
`arrow_transition`, and `comparison_pasted`.

Hypothesis and clause correspondence:

- The finite-field datum is `D : FiniteFieldDatum.{u}`; its algebraic closure is
  `D.k`, its characteristic is `D.p`. The prime is `l` with `[Fact l.Prime]`, and
  `hl : l ≠ D.p`. The final section explicitly includes all these section binders.
- Finite extensions are `E`, `F`, with fields, `Algebra ℚ_[l]`, finite-dimensional
  instances, and their inclusion `i : E →ₐ[ℚ_[l]] F`. Such a map is injective.
  The actual integer rings are `Padic.coefficientExtensionIntegers`; no second
  coefficient ring is introduced. `constantMap` is the constant sheaf of the
  actual integral inclusion, with the necessary `ULift` for section universes.
- `e : ℕ`, `he : PurCompactSupport.Ramification l E F i e`, and `hepos : 1 ≤ e`
  render precisely the uniformizer-ideal equality and positive ramification.
  `finiteChange` uses the corresponding quotient inclusion, not an arbitrary map.
- Schemes have `X.Over (Spec (.of D.k))`, `Y.Over ...`; their structure maps have
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`. The morphism `f` has
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`.
  `c : Compactification f` supplies its actual open `c.i` and proper `c.g`.
- The completed modules are the existing `scalarReductionSource l E X` and its
  F analogue. `pbcDerivedExtend (completedCoefficientMap l E F i X)` is the
  actual `C_X`, retaining its universal cochain tensor counit.
- `finiteTorConstructibleIntegral l E X` is the existing full-domain predicate:
  derived complete, bounded constructible and one uniform Tor interval over all
  reductions. The main map is natural on its full subcategory; each displayed
  evaluated equation is quantified over an ambient M with this very predicate.
- `S`, `S' : CoefficientDerivedSystemCalculus.{u,u}` explicitly expose the
  recorded normalized reduction/limit constructions. They are presentation data
  for the already defined reduction lift, not an extra flatness assumption on M
  or a selectable unrelated functor. The statement holds for each such calculus.
- `support l E c S` is literally native reduction, native exact open extension,
  separately right-derived native proper image, then exact restriction to
  discrete constant integral coefficients. This is the reduction tower used in
  `exists_compactSupportReductionTower`, before its total derived inverse limit.
  The F target applies the same construction to `C_X M`.
- `T` is exact localization of ordinary tensor by constant B on the whole
  strict-tower category. The source and target are derived categories of complexes
  in `ℕᵒᵖ ⥤ Modules ...`; they are not towers in separately formed derived
  categories. B-linearity is the morphism type in that actual B-module category.
- Index `n : ℕ` denotes exponent `n+1`. `subsequence` is the existing strict
  arithmetic restriction, retaining `e*(n+1)` and its composite transitions.
  `reindexProper` derives the ordinary identity square using preservation of
  K-injectives by selection; `reindexOpen` is its exact open counterpart.
- `arrow` is an actual natural transformation: `supportModel`, then the ordered
  `comparison`, then the whole-system `reductionBalancing`, arithmetic reindexing,
  and the inverse target `supportModel`. The middle `comparison` is explicitly
  proper scalar mate followed by proper image of open tensor balancing.
- `strictScalarPull` and `strictProper_geometric_transpose` give the strict
  geometric transpose: canonical balancing followed by scalar extension of the
  proper counit. `proper_geometric_transpose` gives precisely the same formula
  for the finite `PurCompactSupport.properComparison`. Thus the finite first
  arrow is the specified geometric mate, not an unnamed arrow of the right type.
- `PurCompactSupport.finiteTensorMap` is the existing explicit ordered
  `properComparison` followed by proper image of `openComparison`. The first
  conjunct after the M hypothesis in the main theorem says evaluation of `arrow`
  is exactly its restriction to the constant B-module category.
- `sourceEvaluation` is exact tensor evaluation, the normalized native support
  evaluation, then finite ordinary tensor balancing. `targetEvaluation` is
  arithmetic evaluation, native support evaluation at the positive retained
  exponent, and the canonical completed/finite tensor square. The equation in
  the theorem compares actual arrows under these specified identifications.
- All reduction and balancing identifications are fixed on every whole cochain
  counit and on ordinary local pure tensors. In particular
  `reductionBalancing_existsUnique` is not characterized merely after separate
  finite evaluations, which would not rule out phantom diagram morphisms.
- `factors_isIso` states invertibility of strict proper and open mates and of
  every finite proper and open mate as natural transformations. The main theorem
  states invertibility of the natural strict-support map on the full finite-Tor
  domain and of every `finiteTensorMap` component.
- `proper_biproduct` and `strictProper_biproduct` say that, for every finite sheaf basis, restricting the
  proper mate and conjugating by its fixed tensor coordinates gives the canonical
  `piComparison` (finite products are finite biproducts here). Coordinates are
  uniquely fixed by their local tensor formula and their universal cochain
  counits. `pulledBasis` is uniquely transported by the actual ring direct-image
  maps. This applies in particular to every finite A_n-basis of B_n.
- `ordinaryOpenTensor`, `openTensor_ordinary`, `ordinaryBaseOpenTensor`, and
  `open_base_ordinary` identify the strict and finite open maps with exact descent
  of ordinary extension-by-zero tensor balancing. The scalar comparison used
  there is the unique left-adjoint comparison with common normalized restriction.
- Basis independence is built into `arrow`, `proper`, `openTensor` and their
  finite counterparts: none takes a basis. `proper_biproduct` and
  `open_base_ordinary` quantify over every basis and identify those same fixed
  maps in its coordinates; changing coordinates never changes the defined map.
- `diagramTransition` localizes an entire family of index transitions as a natural
  transformation of exact endofunctors on the ordinary derived strict-tower
  category. `arrow_transition` states its commuting square there, for every
  index natural transformation, including constant indices and successor
  transitions. This precedes all finite evaluation and all inverse limits.
  The final main-theorem conjunct is the evaluated quotient square for every
  `a ≤ b`, using the actual `pbcTowerTransition`, and the morphism `arrow` in the
  derived strict-tower category. Its construction and these squares precede any
  derived inverse limit. No detection of derived morphisms by evaluation is used.
- `pastedRestriction` is open restriction followed by the inverse proper
  restriction square. `comparison_pasted` identifies its scalar adjunction mate
  with the ordered proper/open composite, using the canonical composite units.
  It does not regard `j_!` as a right adjoint.

Dependencies used (publicly imported, directly or transitively):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`; its underlying
  `FiniteFieldDatum` is used for the fixed field conventions.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing`, together with the recorded integer and
  uniformizer constructions.
- Mathlib scheme-morphism property classes, `Scheme.Over`, and
  `AlgebraicGeometry.Compactification` (the recorded compactification/refinement
  interface is the upstream `WeilConjectures.Compactification.RefinementCategory`).
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`:
  `Towers`, `Derived`, `G`, `R`, `adj`, `ev`; and
  `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `J`, `moduleJAdj`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; completed coefficient sheaves and
  their actual quotient maps are the recorded ones.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; the existing
  `pbcExtend`, `pbcDerivedExtend`, `pbcComplexCounit` expose its specified tensor.
- `Sheaf.Paper.SfIntegralConstructible`, `Sheaf.Paper.FiniteTorAmplitudeSites`
  and `Sheaf.Paper.FiniteTorAmplitude`: existing constructible/finite-Tor domains.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`; `Sheaf.Paper.CompactSupportReductionTower`:
  `exists_compactSupportReductionTower`, `compactSupportSystemEvaluation`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`; `Sheaf.Paper.CompactSupportNativeSystemEvaluation`
  fixes the actual native separately derived finite support evaluation.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `SheafOfModules.strictSystemSequenceEquivalence`; the native system module and
  strict-diagram categories are retained rather than copied.
- Mathlib `Functor.ofOpSequence`, `DerivedCategory`, and
  `SheafOfModules.restrictScalars`; `Sheaf.CategoryTheory.RingedSiteModules`:
  `ringedSiteModules`; existing `SfIntegralDirectImage` and
  `sfIntrinsicExtensionByZero` are reached through their recorded modules.
- `Sheaf.Paper.IntegralCompactSupportCoefficientData`: `Coefficients`, `Change`,
  `completed`, `finite`, `projection`, `openExtension`, `openRestrictionMap`.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`: the existing `Ramification`,
  `finiteChange`, `properComparison`, `openComparison`, `scalarPull`, `tensorSquare`,
  `finiteImageIso`, `finiteReductionIso`, `ramified_reduction_square`, and
  `finiteTensorMap`, with its explicit source and target. The definition node cited in `stmt_deps` records these
  declarations with `existing: true`; this delivery imports their existing owner.
- `Sheaf.Paper.FiniteScalarCoordinateData`: `ordinaryCoordinates`,
  `derivedCoordinates`, `ordinaryTowerCoordinates`, `derivedTowerCoordinates`,
  `finiteScalar_exact`, `finiteScalarTower`, and `finiteScalarTowerCounit`.
- `CategoryTheory.mateEquiv`, ordinary and derived normalized adjunctions,
  `mapDerivedCategorySquareIso`, and the existing right-derived composite units.

Edge cases checked: the zero module and zero complex; empty scheme/site objects;
all unbounded ambient complexes in normalization statements; the first positive
quotient (`n=0` in Lean); identity coefficient inclusion and `e=1`; arbitrary
positive ramification; all nonconsecutive quotient transitions. No smoothness,
properness of f, K-flatness of M, chosen basis, or new bound on Tor amplitude is
assumed. The coefficient/site conventions retain pro-etale object universe u+1
and morphism universe u. The dependency basis formula includes rank zero.

Searches: the launcher's `msearch.py` ran LeanSearch, LeanFinder/Loogle and grep.
The exact queries, hit counts and returned declaration lists are retained in the
new node records. For the item, Loogle on `CategoryTheory.mateEquiv,
SheafOfModules.restrictScalars` returned 0; LeanFinder on finite scalar extension
commuting with proper/open maps of derived strict towers returned 8 scalar-ring
and base-change component hits; grep on `mateEquiv_vcomp|ringedSlice_extension_tensor`
found mate APIs, not this statement. The item-specific upstream grep found no
occurrence. Searches of both project Lean trees and the DAG found no exact new
notion. `blueprint_refs.py search` returned 0 for each of `constant scalar mates`,
`native constant support`, `ramified reduction balancing`.

Existing `RamifiedPullbackTowerData`/`RamifiedPullbackTowerIdentification` concern
completed scalar pullback quotient systems, not the native compact-support lift
restricted to discrete constants. `CompleteProetaleStrictTowerRealization` concerns
geometric base change with one coefficient ring. Neither supplies these maps.
The finite-free direct-image column theorem permits unspecified coordinate
isomorphisms; here the tensor and whole-cochain normalizations are retained.

No correction to the item's mathematical statement is made. No
STATEMENT-DISPUTED finding. Compilation is performed only with `scompile.py`;
all theorem proofs remain `sorry`, as required for stage 2. Final compiler and
preflight results are recorded by the delivery wrapper.

## New nodes

`def-pur-constant-scalar-tower-adjunction`, module
`Sheaf.Paper.ConstantScalarTowerAdjunction`, defines the constant integral scalar
adjunction and compatible coefficient data on whole strict towers. It is separated
from the mate module to keep kernel checking within the per-file limit. Its source
and searches are those of the constant scalar mate construction below; the scalar
adjunction searches found only ordinary single-module APIs, not this diagram
adjunction with its specified tensor-unit normalization.

`def-pur-constant-scalar-tower-mates`, module
`Sheaf.Paper.ConstantScalarTowerMates`, defines the specified proper/open scalar
mates on strict towers. Source: Stacks 07A6, 0D6E,
0B56, 0940 and 0E8I, item proof Steps 3--5. The three kinds of searches returned
ordinary scalar/module adjunction APIs, not these actual derived tower mates.
The generic helper `unitCompatible` writes out the same resolution-unit equation
with abstract abelian categories, keeping its specialization inexpensive to check.

`def-pur-native-constant-support-model`, module
`Sheaf.Paper.NativeConstantSupportModel`, defines restriction of the native
varying-ring quotient system to discrete constant integral towers, its normalized
proper/open identifications, the actual restricted native support lift, and the
ordinary/derived whole-system counit. Source: Stacks 03DA, 0D6E, 0E8I, 0940 and
0941, item proof Steps 2 and 6. Searches found restriction APIs and geometric
system comparisons but no such constant-restricted native support model.

`def-pur-strict-scalar-reduction-balancing`, module
`Sheaf.Paper.ScalarReductionTowerBalancing`, defines the ramified balancing of
whole strict reduction systems and its cochain-counit normalization. Source:
ordinary tensor balancing (03EK, 06YY) and derived diagram systems (0940), item
proof Step 2. Searches found ordinary tensor complexes and the different
ramified-pullback tower comparison, but no such whole-system scalar balancing.

`def-pur-finite-scalar-coordinate-data`, module
`Sheaf.Paper.FiniteScalarCoordinateData`, owns the ordinary and derived coordinate
comparisons for modules and entire strict towers, their unique tensor/counit
normalizations, exactness and exact tower localization. The node states the
rank-zero case too. Source: Stacks 03CY, 03DB, 03EK, 06YY, 0940 and
Bhatt--Scholze 3.4.12. LeanSearch returned basis-coordinate APIs, LeanFinder
returned ordinary tensor universal properties, and Mathlib grep returned no
coordinate construction. Project/DAG searches found no owner for this normalized
construction. It is not a replacement of the proved theorem on complexes.

`def-pur-finite-compact-support-scalar-data` now records the existing declarations
in `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`, with `existing: true`
and no module delivered for this node. Its primary declaration is the existing
`WeilConjectures.PurCompactSupport.finiteTensorMap`; its 21-declaration list records
the canonical coefficient maps and presentation isomorphisms used here. Reading the
existing signatures and bodies confirms the same ramification ideal, quotient lift,
scalar mates, ordered proper/open composite and presentation normalizations. The
retained searches above found those constructions in precisely this module. Their
existing proofs remain there and are reused.

## Return repair

H13/H2, coordinate ownership: removed the sandbox copy of
`lem-pur-finite-free-scalar-extension.json` entirely. Its landed S1 stage-3 record
and proved `Sheaf.Paper.FiniteFreeScalarExtension` module are untouched. Removed
`finiteFreeScalarExtensionOfUniverses`, its unused sorry statement, and its module.
The item drops that theorem from `stmt_deps`, retains its proof import, and cites
the new coordinate-definition node used by `proper_biproduct` and
`strictProper_biproduct`. All moved coordinate declarations carry their new owner
in their docstrings and are listed in its `lean.declarations`.

L, duplicate ownership at immutable head 3e8ec8aa6135: removed the entire sandbox
`FiniteCompactSupportScalarData.lean`, including all 21 duplicate declarations.
`ConstantScalarTowerAdjunction` now publicly imports the existing
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`. The finite coefficient
node's Lean record points to that module with `existing: true`, no `file`, and a
repair note. No declaration is renamed or restated, and no maintainer relocation
is requested. The current main module does not import this item, so the imports
are acyclic. Since this item now uses its existing coefficient constructions,
adding an import of this item to that owner would create a cycle; omit that proof
import under stages/2-statements.md section 3 rule 7. The mathematical interfaces,
item statement, and all six remaining modules' declarations are unchanged.

## Self-check by N6

Re-read the definition-node records and six modules against the returned
points. The arrow composite, evaluated finite equality, geometric transposes,
proper/open factorization, independence of basis, and transition equations are
unchanged. Every theorem remains a named sorry with a proof docstring, and all
definitions contain actual data or choice from a uniquely normalized theorem.

For the S/S' binders, opened `CoefficientDerivedSystemReductionModel`,
`CoefficientDerivedSystemReduction`, and `CoefficientDerivedSystemCalculus` in
`CoefDerivedSystemEvaluationCalculus`: they include the actual adjunction to
`coefficientSequenceLimit`, K-flat strict representative computation,
`reductionEvaluation`, and the `unit_projection` normalization. Thus the statement
quantifies over presentations of that fixed reduction, and the displayed maps use
those presentations' fixed adjunction units. No arbitrary extra functor, flatness
assumption, or equality of the small site's object and arrow universes was added.
Rank zero, zero complex, first positive quotient, identity extension/e=1,
ramified e>1, and nonconsecutive transitions remain included.

The source text and item signature have not changed. The sandbox has no copy of
the landed finite-free theorem node. Signature, line-width, explicit-variable,
sorry-only, declaration-ownership and import-cycle checks accompany the required
server compilation and dry run below.

## Continued repair validation

The resumed dry run exposed instance dependencies formerly supplied by the removed
cyclic imports. `NativeConstantSupportModel` now explicitly fixes all four categories
of `unitCompatible` to the existing native sequence and strict constant tower
categories. Its `nativeSequence_kInjective` instance uses the already proved
`ProEtale.VaryingRing.modules_kInjective` for the actual native coefficient rings;
it appears before its first use. It introduces no new resolution assumption and no
new postponed theorem. The declaration is listed under the native support node.
The existing `systemRestriction_additive` instance is retained unchanged.

The source-only self-check passed for all six modules: every recorded
signature occurs verbatim, every top-level declaration has its owning node record,
all lines respect the width limit, and theorem proofs remain sorry-only. The item
changes only `lean` and adds upstream definitions in `stmt_deps` relative to the
current main node. The proved finite-free scalar-extension node is absent from the
sandbox, and its landed declaration and node record remain untouched.

The final elaboration repair explicitly supplies the recorded
`coefficientSequenceEvaluation_additiveInstance` and the matching upstream
finite-limit/finite-colimit instances in `evaluationRestriction`.
`systemRestriction` and `systemU` use the identical native sequence-category
presentation in their result annotations, avoiding repeated expansion of quotient
ring sheaves. The generic normalization predicate and cochain unit are locally
irreducible during specialization; their definitions and normalization equations
are unchanged. No hypothesis or conclusion was changed by these repairs.

In the earlier saved-packet validation, all seven original modules compiled. Preflight found only
two dependency citations grouped into a single bracket in the new coordinate node;
these now appear as separate `[id]` citations, matching its unchanged `stmt_deps`.

## Current return validation (2026-10-23)

The initial saved-packet dry run returned OK at commit 9821e6ea322. The explicit
return still required removing the 21 duplicate declarations, so this repair was
made before delivery. The six remaining modules reuse the existing owner without
renaming, copying or weakening any statement. The current imports are acyclic;
the earlier proposed relocation is withdrawn. The required six-file `scompile.py` run completed successfully with no errors
or unexpected warnings. All recorded signatures occur verbatim in their respective
source files, including the existing finite-data declaration. All six delivered
files explicitly disable auto-bound implicits and satisfy the line-width check.
The recursive import scan inspected 9405 project modules and found no cycle.
None of the 21 returned names is declared in any remaining delivered module.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
