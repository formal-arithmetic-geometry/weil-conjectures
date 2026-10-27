## Worker report

The delivery states the complete scalar/projection comparison in
`Sheaf.Paper.CompactSupportScalarProjectionIdentification`, namespace
`WeilConjectures.PurScalarProjection`. The principal theorem is
`compactSupportScalarProjectionIdentification`. It uses `PurScalarArrow.completedArrow`,
the published completed-linear realization of `r_e⁻¹ R(q) τ`, explicitly in both
routes. `ordinaryCompletedSquare` is its ordinary proper/open presentation.
Every theorem has proof `by sorry`. Definitions have actual compositional data;
`scalarCompletion`, `properProjection`, and `realization` use uniquely normalized
existence theorems, rather than a choice of an unconstrained isomorphism.

Source read: the item's statement, source, all nine proof steps, every statement
dependency and its recorded declaration/docstring; the current blueprint route
`sk-thm-sf-compatibility` and `sk-thm-purity-transport` through
`thm-pur-rational-and-qbar-purity`; Stacks `sites-cohomology.tex` Tags 0E48 and
0B56, and `sites-modules.tex` Tag 0E8I. The assembly is the node's auxiliary,
not an assertion that one Stacks tag states this whole theorem.

Hypotheses and clauses, in source order:

1. The finite-field conventions are `D : FiniteFieldDatum.{u}` and `hl : l ≠ D.p`;
   `Fact l.Prime` makes l prime. `E`, `F` are fields with the specified finite
   dimensional Q_l algebra structures and `i : E →ₐ[ℚ_[l]] F` is the inclusion.
   Its injectivity follows from being a field algebra hom; no arbitrary ring map
   is substituted. `Ramification l E F i e`, `hepos : 1 ≤ e` retain the ideal
   equality t B = v^e B, including ramification and the full F-uniformizer tower.
2. `X`, `Y : Scheme.{u}` carry `Over (Spec (.of D.k))`, locally finite type,
   quasi-compact, separated structural maps. `f` is over this field, separated,
   locally finite type and quasi-compact. These are precisely finite type and
   separatedness. `c : Compactification f` is the recorded compactification;
   its `i`, `g`, and `Z` give j, p_c and X-bar, with their open/proper instances.
3. All module categories are on the actual small pro-etale sites. The ring sheaves
   are `(completed l E).ring W` and `(completed l F).ring W`;
   `pbcDerivedExtend (completedCoefficientMap l E F i W)` is ordinary derived
   extension over these sheaves. No completed scalar extension replaces C_W.
4. `M`, `K` are ambient derived objects with
   `finiteTorConstructibleIntegral l E X M` and its Y analogue. This is the
   recorded complete bounded constructible condition and one uniform finite
   Tor interval for all positive reductions, not just levelwise boundedness.
   The main existential `hCM`, `hCK` asserts preservation of this domain; these
   are conclusions, not additional hypotheses. `inner_domain` supplies exactly
   the domain for gamma at the completed inner tensor.
5. `PurStrictScalar.scalarSupport` is the actual total right-derived limit of
   `scalarSupportNative`, the separately derived varying-coefficient open and
   proper functors. The finite exponents are n+1; arithmetic selection retains
   e(n+1). Thus n=0 in Lean is exponent one, not the zero quotient. The quotient
   scalar structures and their derived adjunctions are the published ones.
6. `IntegralOnSlice.completion` after `ordinarySource` and `ordinaryInner` is the
   completed tensor. The latter presents tensor with completed pullback by the
   published completed-tensor unit-insertion comparison. All tensor models are
   the existing representative-normalized `ProEtaleTensorModel` (the abbreviation
   `PurProjectionData.TensorModel`). Quantifying such a presentation does not
   assume a projection formula or choose a new tensor. Likewise `SE`, `SF` are
   the existing normalized coefficient-system calculi.
7. `supportProjection` conjugates the actual
   `PurProjectionData.integralMap` by normalized support realization, so it
   is the actual completed proper/open projection PF_H on total-limit support.
   `scalarInner` is the canonical scalar tensor/pullback identification at the
   target. `scalarTensorCompleted` is the source scalar tensor comparison,
   normalized by the completion unit. The main theorem's left route is
   C(PF_E), then the specified gamma at the completed inner tensor, then the
   canonical inner identification. The right route is scalar tensor balancing,
   completed tensor of gamma_M with identity, then PF_F. This is the exact two
   composites in the node, with a common target made explicit.
8. `native_scalar_identification` identifies the reduced ordinary mate with the
   specified strict scalar mate on the whole ringed sequence category, with
   `reductionBalancing`, before any evaluation or total limit.
   `diagram_projection` is equality in the native derived ringed diagram category:
   reduction of ordinary projection/scalar composites followed by the native
   support adjunct. The reduction-tensor and support comparisons present these
   as the finite quotient projection arrows. The statement is an equality of
   whole diagram morphisms; it is not a family of equalities of homology groups.
9. `realization_existsUnique` and `realization` identify actual proper/open image
   with total-limit support, retaining every actual finite scalar-adjunction
   counit. `nativeRealization` is its whole-system adjunct under the actual
   reduction/limit adjunction. The proof docstring uses the canonical open and
   direct-image/limit comparisons for existence. Uniqueness of this auxiliary
   characterization is justified on the bounded constructible finite-Tor domain
   by the derived Hom inverse-limit sequence: finite Hom groups give the
   Mittag--Leffler condition and kill lim-one. It does not assert faithfulness
   of reduction on arbitrary derived categories. In particular finite equations
   alone are not claimed to imply uniqueness for arbitrary objects.
10. `properProjectionOrdinary` is explicitly the transpose of tensor-pullback
    followed by the actual proper counit.
    `properProjection_existsUnique` states precisely
    eta_source ≫ pi_complete = pi_ordinary ≫ P.map eta_inner
    for complete V,L, without constructibility restrictions. `properProjection`
    selects this unique unit-normalized map. Since E is arbitrary, this applies
    to each of OE and OF. `openProjection_existsUnique` gives the identical
    completion-unit normalization for quasi-compact open extension, using the
    actual `openProjectionIso`. `projection_unit` states the equation for the
    published actual compact-support projection and uniqueness from the equation
    alone. Thus the unit and counit normalization is not replaced by invertibility
    or an arbitrary projection map.
11. `gamma_identification` identifies the very normalized strict scalar limit with
    `comparison (completedChange l E F i) c` under the canonical realizations.
    Together with `native_scalar_identification` this retains compatibility of
    the completed proper/open/limit identifications with the finite-free scalar
    mate. `ordinaryCompletedSquare`, followed by this identification, yields
    the main integral square by the completion-reflector Hom bijection. No
    faithfulness of reductions is assumed in the main theorem or any hypothesis.

Statement dependency declarations:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-scheme-morphism-properties`: convention node; its actual Mathlib properties are the scheme instances in the signature.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `lem-pur-compact-support-strict-scalar-mate`: `Sheaf.Paper.CompactSupportStrictScalarMate`, `WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `lem-pur-compact-support-scalar-limit-reduction`: `Sheaf.Paper.CompactSupportScalarLimitReduction`, `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `lem-pur-compact-support-completed-projection-coherence`: `Sheaf.Paper.CompletedProjectionCoherence`, `CategoryTheory.AdicSites.ProjectionCoherence.completedProjectionCoherence`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-pur-integral-compact-support-coefficient-data`: `Sheaf.Paper.IntegralCompactSupportCoefficientData`, `WeilConjectures.PurCompactSupport.completed`. The module is publicly imported; its established constructions are used through the named interfaces below.
- `def-pur-compact-support-completed-scalar-arrow`: `Sheaf.Paper.CompactSupportCompletedScalarArrow`, `WeilConjectures.PurScalarArrow.completedArrow`, with `completedArrow_existsUnique`.
- `def-pur-compact-support-completed-projection-data`: `Sheaf.Paper.CompactSupportCompletedProjectionData`, `WeilConjectures.PurProjectionData.integralMap`, and `TensorModel`, `ordinarySource`, `ordinaryInner`, `completedSource`, `completedTarget`, `integralDomains`.

Concrete interfaces used within those modules are `PurCompactSupport.completed`,
`completedChange`, `image`, `comparison`, `scalarPull`, `scalarTensor`,
`projectionMap`, `completedPull_comp`, `openProjectionIso`,
`PurStrictScalar.scalarSupport`, `scalarSupportNative`, `scalarSupportCounit`,
`arrow`, `systemU`, `T`, `reductionBalancing`, `completedArrow`,
`CoefficientDerivedSystemCalculus.reduction` and `.adjunction`,
`IntegralOnSlice.completion` and `.completionUnit`, and
`PurProjectionData.integralMap`. All are reused rather than redefined.
The added landed definition dependency `def-pur-integral-compact-support-coefficient-data`
is retained. The returned theorem dependencies for scalar composition and the
projection formula are removed; the two new definition nodes below own transparent
re-exports of completedArrow/uniqueness and projection data/typing. No conclusion
of either enclosing theorem is used. The aliases have the same complete signatures
and universes as the originals.

Proof dependency interfaces:

- `lem-pur-compact-support-coefficient-models`: no Lean record; the supplied mathematical proof step is retained in the main docstring.
- `lem-weil-proetale-countable-products-exact`: `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact` (plain proof import unless already a statement import).
- `lem-pur-completed-operation-tower-substitution`: `Sheaf.Paper.CompletedOperationTowerSubstitution`, `WeilConjectures.CompletedOperations.completedOperationTowerSubstitution` (plain proof import unless already a statement import).
- `lem-sf-pullback-tor-amplitude`: `Sheaf.Paper.PullbackTorAmplitude`, `WeilConjectures.sf_pullback_torAmplitude` (plain proof import unless already a statement import).
- `lem-sf-tensor-ctf`: `Sheaf.Paper.FiniteCoefficientTensorCtf`, `AlgebraicGeometry.Scheme.finiteCoefficient_tensor_ctf` (plain proof import unless already a statement import).
- `lem-weil-pbc-ringed-exchange-tensor-coherence`: `Sheaf.Paper.RingedExchangeTensorCoherence`, `SheafOfModules.ringedExchangeTensorCoherence` (plain proof import unless already a statement import).
- `lem-pur-compact-support-strict-scalar-mate`: `Sheaf.Paper.CompactSupportStrictScalarMate`, `WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate` (plain proof import unless already a statement import).
- `lem-sf-open-tensor-normalization`: `Sheaf.SixFunctors.OpenTensorNormalization`, `SheafOfModules.openTensorNormalization` (plain proof import unless already a statement import).
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` (plain proof import unless already a statement import).
- `lem-weil-l-adic-extension-integers-dvr`: `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, `Padic.extension_integers_dvr` (plain proof import unless already a statement import).
- `lem-pur-compact-support-completed-projection-coherence`: `Sheaf.Paper.CompletedProjectionCoherence`, `CategoryTheory.AdicSites.ProjectionCoherence.completedProjectionCoherence` (plain proof import unless already a statement import).
- `lem-pur-completed-coefficient-pushforward-comparison`: `Sheaf.Paper.CompletedCoefficientPushforwardComparison`, `WeilConjectures.CompletedCoefficientPushforward.comparison` (plain proof import unless already a statement import).
- `lem-cbc-completed-extension-zero-comparison`: `Sheaf.Paper.CompletedOpenExchangeTransport`, `AlgebraicGeometry.Scheme.completedOpenExchangeComparison` (plain proof import unless already a statement import).
- `lem-pur-completed-open-tensor-system-realization`: `Sheaf.Paper.CompletedOpenTensorSystemRealization`, `WeilConjectures.CompletedOpenTensor.completedOpenTensorSystemRealization` (plain proof import unless already a statement import).
- `lem-pur-perfect-quotient-exchange-normalization`: `Sheaf.Paper.PerfectQuotientExchangeNormalization`, `CategoryTheory.AdicSites.PerfectQuotientExchange.perfectQuotientExchangeNormalization` (plain proof import unless already a statement import).
- `lem-weil-pbc-mate-pasting`: Mathlib `CategoryTheory.mateEquiv_vcomp`, `mateEquiv_hcomp`, and conjugate-equivalence mate identities.
- `lem-pur-tower-limit-transpose-normalization`: `Sheaf.CategoryTheory.TowerLimitTransposeNormalization`, `CategoryTheory.TowerLimitTransposeNormalization.tower_limit_transpose_normalization` (plain proof import unless already a statement import).
- `lem-pur-compact-support-roos-cofinality`: `Sheaf.CategoryTheory.CompactSupportRoosCofinality`, `CategoryTheory.compactSupportRoosCofinality` (plain proof import unless already a statement import).
- `lem-pur-compact-support-scalar-limit-reduction`: `Sheaf.Paper.CompactSupportScalarLimitReduction`, `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction` (plain proof import unless already a statement import).
- `lem-pur-finite-free-completion-exchange`: `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange`, `CategoryTheory.PrincipalQuotientCompletion.finiteFreeCompletionExchange` (plain proof import unless already a statement import).
- `lem-pur-integral-operations-scalar-extension`: `Sheaf.Paper.IntegralOperationsScalarComparisons`, `WeilConjectures.scalarOperationsOrdinary_tower` (plain proof import unless already a statement import).
- `lem-pur-completed-tensor-unit-insertion`: `Sheaf.Paper.CompletedTensorUnitInsertion`, `CategoryTheory.ConstantCompletion.completedTensorUnitInsertion` (plain proof import unless already a statement import).
- `lem-sp-completed-pullback-adjunction`: `Sheaf.Paper.CompletedPullbackAdjunction`, `CategoryTheory.ConstantCompletion.completedPullbackAdjunction` (plain proof import unless already a statement import).

Edge cases checked: E=F and i=identity; e=1 and arbitrarily ramified e>1;
positive exponent one (Lean n=0); empty schemes and zero complexes; identity
compactification; arbitrary shifts, with signed total-complex tensor models;
complete proper/open inputs not assumed constructible in the unit lemmas.
No dimension, smoothness, properness of f, non-emptiness, flat quotient, or
faithful-reduction hypothesis has been added. The actual proper arrow is c.g.
The small pro-etale site retains object universe u+1 and morphism universe u;
no equality of those universes is imposed to use the generic adic-site API.

Searches performed (the wrapper logs are in sandbox searches.jsonl):

- LeanFinder: `Finite free scalar extension compact support projection formula
  squares compatible with derived completion and finite quotient diagram units
  counits`: eight results, concerning condensed projectivity and unrelated adic
  projections; no exact statement.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.NatTrans, DerivedCategory`:
  zero hits.
- msearch grep: `projection.*scalar|scalar.*projection`, subdirectory
  `CategoryTheory`: zero hits.
- LeanSearch: `Scalar extension compatibility with compact support projection
  formula and completion`: eight unrelated continuous compact-support and
  topological-completion results; no exact statement.
- `rg`/`grep` of `lean/WeilConjectures` for the item id and scalar/projection/
  compact-support patterns found no exact item statement. `rg` of `lean/Sheaf`
  found the existing coefficient, strict scalar, completed projection and tensor
  interfaces listed above; these are imported and reused. The exact item id
  appeared only in the new sandbox module, not a published matching theorem.

Two definition nodes now record the existing helper interfaces, as requested in
the return. No dependency module or statement correction is needed. No node
statement is disputed.

Validation: incremental server compiles through scompile.py passed for the
import set, the helper/unit statements, the ordinary completed square, and the
native scalar and diagram statements. Final whole-file server compile passed in sandbox and library mode, with no
errors or unexpected warnings. The prescribed delivery preflight is run before
pushing.


## Repair of returned head 6d87b91f58bc

H2 is repaired by adding `def-pur-compact-support-completed-scalar-arrow` and
`def-pur-compact-support-completed-projection-data` in sec-smooth-purity. The
former re-exports the exact `PurStrictScalar.completedArrow_existsUnique` and
`PurStrictScalar.completedArrow`; the latter re-exports the exact seven
`SfProEtaleProjection` interfaces named in the return, including the typing
helper `integralDomains`. Each re-export is `abbrev := @ExistingDeclaration.{u}`,
so every parameter, instance, premise, endpoint and universe is retained. The
item imports these modules and uses their alias names throughout. It drops
`lem-pur-compact-support-strict-scalar-composition` and `sk-thm-sf-pf-proetale`
from stmt_deps. Those modules are imported only by the corresponding re-export
module; neither enclosing theorem's conclusion is cited or applied. The helper
lemmas are aliases of existing named proofs, not newly postponed proofs.

The reviewed item statement, all geometric and coefficient hypotheses, all
projection/scalar routes and all finite-diagram and completion-unit clauses
remain unchanged up to these transparent aliases. Compared with the returned
head, the Lean main signature changes only these names and the two imports;
the helper mathematical assertions themselves are unchanged. The item node's
non-Lean fields retain the current main version except for the authorized
stmt_deps changes; deliver2 builds the repaired commit on current main.

Advisory H4: these similarly named scalar comparisons have different types.
`PurStrictScalar.scalarCompletion` in CompactSupportScalarLimitReduction is
`Res_E ⋙ baseTensor ≅ C ⋙ Res_F`: it changes from constant to completed
coefficient restriction and does not apply the adic completion reflector to its
input. `WeilConjectures.scalarCompletion` in IntegralOperationsScalarComparisons
is a natural transformation from ordinary derived scalar extension to the
strict-tower scalar functor; `scalarCompletionIso` assumes its input is complete.
That module's `scalarTensorCompleted` likewise uses strict scalar extension
on complete inputs and its fixed `integralCompletedTensor` presentation.

The item's `PurScalarProjection.scalarCompletion` instead has type
`C(hat Q) ≅ hat(C Q)` for every ordinary derived Q, with no completeness
hypothesis, and is fixed by `C(eta_Q) ≫ chi = eta_(C Q)`. It is needed at the
possibly incomplete ordinary tensors in the completion-unit calculation.
The item's `scalarTensorCompleted` then has endpoints
`C(hat(a.tensor(Q,T)))` and `hat(b.tensor(C Q,C T))`, for the supplied
representative-normalized tensor models a,b and arbitrary Q,T. Its body already
reuses the existing `PurCompactSupport.scalarTensor`; it merely composes that
ordinary scalar balancing with the preceding all-input completion exchange.
Thus the definitions do not replace either of the existing differently typed
maps. Both are determined by the same canonical unit/representative
normalizations when transported to a common presentation. No extra axiom or
arbitrary isomorphism was introduced to handle the advisory.

## New nodes

`def-pur-compact-support-completed-scalar-arrow` records the completed-linear
lift of the normalized total-limit arrow together with the exact uniqueness
helper that determines the selected map. Its source is the auxiliary Step 7,
Stacks 0941 and 07A6, and the existing interface immediately before the
completed scalar-composition theorem. Its module is
`Sheaf.Paper.CompactSupportCompletedScalarArrow`, namespace
`WeilConjectures.PurScalarArrow`. The LeanFinder and LeanSearch searches each
returned eight unrelated scalar/completion/continuous-map hits; Mathlib grep
for `completedArrow|completedArrow_existsUnique` returned zero. The project
search found the exact existing declarations, which are re-exported; the DAG
scan found no definition-node owner. The landed
`def-pur-compact-support-scalar-limit-maps` owns earlier constant-coefficient
limit maps and does not own this completed-linear lift. The new statement cites
that existing node rather than duplicating its definitions.

`def-pur-compact-support-completed-projection-data` records the existing
ordinary tensor model, four projection endpoints, endpoint typing/source-unit
helper, and the actual integral projection composite. Its sources are Stacks
0B56, 0E8I and 099N and the explicit construction preceding
`sf_proetale_projection_formula`; it asserts no projection invertibility.
Its module is `Sheaf.Paper.CompactSupportCompletedProjectionData`, namespace
`WeilConjectures.PurProjectionData`. LeanFinder and LeanSearch each returned
eight unrelated counit/topological-completion/continuous-map hits; Mathlib grep
for `integralDomains|ordinaryInner|completedSource|completedTarget` returned
zero. The project search found the existing seven declarations; the complete
DAG definition-node Lean-record scan found no owner. This is the maintainer's
requested re-export, not a second construction. The broad domain clauses in
the definition node preserve the original declarations: the endpoint definitions
allow arbitrary schemes and compactifications, and integralDomains/integralMap
need finite-type schemes over the finite-field datum but do not assume absolute
separatedness. The item retains its own stronger separatedness hypotheses.

For both nodes, searches are recorded verbatim from the actual wrapper search
log, with dates and results. Searches of the complete blueprint via
`blueprint_refs.py search scalar limit` and `search completed projection`
found related statements but no identical standalone definition; the prescribed
ancestor command returned `thm-pur-rational-and-qbar-purity`. The blueprint route
and unit metadata are copied from the item with this item prepended to via.
No other existing node was edited. Every delivered module has exactly one
owning node. Both new modules contain only transparent aliases, without sorry
data or additional axioms.

Repair validation: scompile.py compiled all three delivered modules separately in
dependency order, including the private overlay, sandbox, and library checks.
No errors or unexpected warnings were reported. The two new modules are exact
abbreviation re-exports; the main theorem compiles through their public imports.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
