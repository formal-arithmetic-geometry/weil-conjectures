## Worker report

The module `Sheaf.Paper.FdNormalizedIntegralCompletionComparison` states
`WeilConjectures.fdNormalizedIntegralCompletionComparison` with one `sorry` and
provides two actual definitions, `fdIntegralOrdinaryRestriction` and
`fdIntegralStrictRestriction`. These are the existing
`ObjectProperty.liftFullSubcategory` applied to the recorded ordinary derived
extension and strict quotient-tower extension. Their membership arguments are
proofs; neither replaces the underlying functor, morphism, or coefficient sheaf.
No definition contains postponed data, and no theorem is proved in this delivery.

Hypothesis and clause correspondence:

- The global finite-field tuple is `D : FiniteFieldDatum.{d}`. Its existing
  fields record p, a, q, the finite field, and its algebraic closure. `l`,
  `[Fact l.Prime]`, and `hl : l ≠ D.p` give the coefficient prime restriction.
  `Ω`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, and `[IsAlgClosure ℚ_[l] Ω]` give the
  fixed coefficient algebraic closure. Its universe `w` is independent of the
  finite-field datum's `d` and the scheme's `u`.
- The geometric hypotheses are `[IsNoetherian T]`,
  `[dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]`, and
  `[iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`. No finite type,
  separatedness, nonemptiness, or smoothness hypothesis is imposed on T.
- `E`, `L` are finite-dimensional extensions of `ℚ_[l]`, and
  `ι : E →ₐ[ℚ_[l]] L` is the coefficient inclusion (automatically injective).
  This is the usual abstract presentation of E ⊆ L. For the actual finite
  subfields of Ω the final clause uses `A B : Padic.FiniteCoefficientFields l Ω`,
  `h : A ≤ B`, their recorded `pbcFiniteField` small representatives and the
  exact recorded `pbcFiniteFieldInclusion`. Thus both arbitrary and identity
  inclusions are covered; no auxiliary splitting or basis is assumed.
- The common integral category is exactly `sfIntegralConstructibleCategory`.
  The PBC category is identified through the already recorded
  `integralDetailedTransport` of the stratified-perfect characterization.
  Rationalization is used only to specify which integral categories underlie
  the two named rational categories; no rational conclusion is substituted here.
- `hC` and `hU` assert preservation of that predicate by the actual ordinary and
  strict functors. `b` is a natural isomorphism of their full-subcategory
  restrictions. The first equality fixes `(b.hom.app K).hom` to
  `(completedScalarComparison ...).app K.obj`. Hence b is the actual χ, and
  its inverse is the inverse of χ by the isomorphism identities. Natural
  isomorphisms include both naturality and the two inverse equations.
- `sC` and `sU` are coherent integer `CommShift` structures on these restricted
  functors. Their two `IsTriangulated` conjuncts state exactness for precisely
  those structures. Both `NatTrans.CommShift b.hom ℤ` and
  `NatTrans.CommShift b.inv ℤ` state the two displayed shift squares for every
  integer, including the inverse equation. The subsequent two `HEq` equations
  identify their images under the full inclusions with the ambient `eOrd` and
  `eStrict` shift maps, including the inclusion's own shift comparison. These
  are identifications of the existing coefficient presentation, not freely
  transported shift structures.
- `completedScalarShiftRepresentativeProperty ι T eChain eOrd eStrict` retains
  all the recorded normalizations: the signed cone formula on its two
  inclusions, the chain shift equation, ordinary counit-normalized shift,
  strict shift descent through its resolving comparison, and χ's ambient
  shift square. Its `completedScalarShiftConeFormula` is exactly coefficient
  one on the first cone summand and `m.negOnePow` on the second, using the
  fixed product reindexing. The chain equation says that `(c(z),0)` is sent
  to `(c(z),0)` under these shifts.
- The next localization equation is the actual equality
  `χ.app (Q.obj P.obj) ≫ integralScalarExtensionComparisonOfUniverses.hom.app P =
  completedScalarCounit P.obj ≫ Q.map (completedScalarChainComparison.app P.obj)`.
  It quantifies over every recorded flat-term K-flat representative, with
  no chosen resolution or auxiliary map. The comparison's naturality and
  its existing unique-descent specification supply representative independence.
- The following two conjuncts spell out every quotient coordinate and the zero
  shifted-product coordinate on such a representative. `n : ℕ` denotes positive
  quotient exponent n+1, as throughout the recorded tower API. The first equation
  applies the actual `completedIntegralCommRingProjectionUnrestricted`; it is
  precisely p tensor s mapping to p tensor the image of s, written scalar first
  by the existing sheafified tensor API. The second equation uses
  `mappingCocone.snd` and says its composition is zero in every degree.
- The identity-inclusion conjunct is the exact canonical equation with
  `completedScalarIdentityMultiplication` followed by
  `completedScalarIdentityUnit`, using the same counit and strict comparison.
  It identifies χ for E=E with the completeness unit under tensor multiplication.
- The final clause supplies `o : FdOrdinaryScalarTransport ... h`; its `generators`
  field states the generator identity under the recorded coefficient isomorphism.
  It supplies the integral scalar isomorphism `a` and exactly the `chi` equation
  required by `FdCoefficientComparison`: the two coefficient-transport factors,
  actual PBC derived counit, and localized `o.completion` all remain visible.
  `o.completion` is the ordinary tensor transport followed by the actual χ chain
  map. This final clause asserts the integral lift, without assuming a full
  coefficient-comparison datum or any downstream coherence theorem.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`; its integral category is the recorded
  `sfIntegralConstructibleCategory`, not a new definition.
- `Sheaf.Paper.PbcRationalCategory`: `Scheme.PbcRationalDerivedCategory`,
  specializing `PbcBoundedConstructibleComplete` with unchanged objects.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralDetailedCoefficientComparison`, `integralDetailedTransport`,
  `integralStratifiedPerfectDetailed`, and their finite-projection normalization.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedDerivedScalarExtension`, `completedScalarComparison`, its unique
  descent specification, `completedScalarChainComparison`, its unique quotient
  specification, the actual tensor sections and Roos endomorphism,
  `completedScalarIdentityMultiplication`, `completedScalarIdentityUnit`, and
  `finiteFreeCompletedScalarComparison`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`. The representative class
  `integralOperationsGoodComplex` uses this notion and flat terms.
- `Sheaf.Paper.QuotientScalarComparisonDescent`:
  `SheafOfModules.quotient_scalar_comparison_descent`, including its universal
  representative equation and unit specialization. The specialization here uses
  the already recorded `completedScalarComparison`, never a second chosen descent.
- `Sheaf.Paper.FdCoefficientComparison`: `FdOrdinaryScalarTransport`, its
  `.complex` and `.completion`, `fdCoefficientTransportFactors`, and the
  `FdCoefficientComparison.chi` signature copied as the final conclusion.
- `Sheaf.Paper.CompletedScalarShift`:
  `completedScalarShiftRepresentativeProperty`, `completedScalarShiftChainEquation`,
  `completedScalarShiftOrdinaryNormalization`, and
  `completedScalarShiftRepresentativeProperty` (the main predicate). These reuse
  `Sheaf.Paper.CompletedScalarShiftCoordinates`'s
  `completedScalarShiftConeFormula`, `completedScalarShiftProductIso`, and
  `completedScalarShiftIntegralNormalization`.
- `Sheaf.Paper.CompletedScalarChainShift`: `completedScalarChainShift`;
  `Sheaf.Paper.CompletedScalarShiftDescent`: `completedScalarShiftDescent`.
- `Sheaf.Paper.CompletedCoefficientPresentationTransport`: the existing
  `purCoefficientIso`, exact restriction round trip, `purCoefficientModel`,
  `purOrdinaryScalarModel`, `purScalarModel`, and their generator/counit
  normalization. These are proof inputs, not new parallel coefficient models.
- The remaining recorded proof dependencies are directly imported: intrinsic
  integral triangulation, intrinsic completeness/constructibility, constructible
  scalar extension, integral coefficient presentation comparison, countable
  product exactness, and ordinary derived change of rings. The last module
  publicly retains the generic sheaf interface despite its record's main name
  being the ordinary-module specialization.
- Mathlib `CategoryTheory.Functor.CommShift`, `NatTrans.CommShift`,
  `Functor.IsTriangulated`, full-subcategory inclusion and inherited triangulation
  give exact natural isomorphisms in their standard senses. The upstream
  `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
  gives the existing literal `liftFullSubcategory`.

The item's stmt_deps cite the new existing-declaration definition node
`def-fd-completed-scalar-shift-representative-property` for the three plain
predicates in `CompletedScalarShift`, plus the already-landed definition nodes
`def-pur-completed-scalar-shift-coordinates` and
`def-pur-completed-coefficient-presentation-transport`. The theorem node
`lem-weil-point-completed-scalar-shift` is removed from stmt_deps: the statement
uses none of its conclusion or choices. Its theorem is not used in the retained
proof plan, which uses the chain-shift and shift-descent lemmas directly, so no
proof_deps change is needed. No mathematical statement correction is needed.

Edge cases checked before and during writing: E=L is included by the explicit
identity specialization and by reflexive subfield inclusions; m=0 and negative m
are included by ℤ-valued `CommShift` and `negOnePow`; there is no nonemptiness
condition on T, no nonzero-object condition on K, no unramifiedness condition on
L/E and no condition on the relative uniformizers beyond the existing coefficient
conventions. Quotients include exponent one; exponent zero is not introduced.
The scheme's small pro-etale site retains object universe u+1, morphism universe u,
and module/coefficients universe u+1; these are not forced equal. All variables
and universes are explicitly bound, with `autoImplicit false`.

Searches (2026-10-23):

- msearch LeanFinder, query: “The quotient normalized comparison from ordinary
  derived coefficient extension to completed scalar extension restricts to an exact
  natural isomorphism on integral constructible sheaves”. Eight hits concerned
  scheme normalization; none state this comparison.
- msearch Loogle, query `CategoryTheory.NatTrans.CommShift,
  CategoryTheory.Functor.IsTriangulated`. Eight hits were generic exactness transfer
  under an isomorphism; none fix this χ or state the quotient normalization.
- msearch grep, `completed.*[Ss]calar|[Ss]calar.*[Cc]ompletion` in CategoryTheory:
  zero hits. A second grep for `def lift|liftCompι|CommShift|IsTriangulated` in
  CategoryTheory/Triangulated/Subcategory.lean found the generic object-property
  triangulation API, not the coefficient comparison.
- msearch LeanSearch, query “Canonical quotient comparison ordinary derived scalar
  extension completed tensor constructible sheaves exact shifts”. Eight generic
  shift/localization hits, including the derived quotient's CommShift instances;
  no match for the theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `normalizedIntegral|NormalizedIntegral|lem-fd-normalized-integral-completion-comparison`
  found only unrelated normalized-integral fractions and integrations, not this
  node or a declaration of its statement. The mandated node-id search likewise
  found no upstream copy. Concept searches found the canonical completed scalar,
  signed shift and coefficient datum modules used here. In particular
  `FdCompletionInverseScalarCoherence` supplies downstream coherence with integral
  inputs; it does not already state this normalized exact restriction theorem.

Compilation: every probe and delivered file uses module mode. scompile.py accepted
both the sandbox and real module name; no diagnostics beyond allowed sorry usage.
No disputed mathematical statement or node fault was found.

## Second reading by Q88

I reopened the item, the complete module, the coefficient datum's `chi` field,
the unique quotient/descent specifications, and the shift-coordinate definitions.
The initial draft supplied restriction and abstract exactness but left the quotient
coordinates and datum lift implicit. I added both explicit coordinate conjuncts
and the full transported localization equation. I also tied both restricted shifts
to their prescribed ambient shifts through the inclusion comparisons, preventing
an arbitrary shift obtained merely by transporting along b. The coordinate
conjuncts now quantify precisely over flat-term K-flat representatives, matching
the node rather than unnecessarily strengthening it to all complexes.

Clause-by-clause, the characteristic, prime, coefficient algebraic closure, scheme
bounds, two actual scalar functors, χ equality, natural inverse, two exactness
claims, forward and inverse shift squares, generator normalization, quotient
coordinate, zero coordinate, canonical derived descent, coefficient-datum lift,
signed cone formula and equal-field completeness unit are all present as described
above. Only inherited full-category/presentation identifications are represented
by HEq; no arbitrary map or unnormalized isomorphism is substituted. The statement
has one sorry, the two helper definitions are real full-subcategory restrictions,
and all required dependency interfaces are reused. No further mismatch found.
This is a self rereading: the dispatcher expressly forbids starting another agent;
the maintainer provides the independent delivery review.

## New nodes

`def-fd-completed-scalar-shift-representative-property` registers the existing
`completedScalarShiftChainEquation`, `completedScalarShiftOrdinaryNormalization`,
and `completedScalarShiftRepresentativeProperty` in
`Sheaf.Paper.CompletedScalarShift` with `existing: true`. Its signature is copied
verbatim from that file. Its statement gives the chain equation with canonical
tensor reindexing, the ordinary derived counit normalization on every good
representative, and the conjunction with the already-owned cone formula, strict
normalization, and actual χ shift square. It defines no existence theorem.
The coefficient and scheme universes remain independent, and there is no
Noetherian, completeness, or constructibility assumption in these predicates.
The source is the final coefficient-category sentence of the current trace
blueprint, through the item's signed-shift clauses; I reopened that blueprint
and Stacks' integer cochain convention in homology.tex, definition-shift-cochain.

Searches run in this repair: msearch LeanSearch with “Completed scalar shift
chain equation ordinary counit normalization representative property” gave eight
unrelated/generic counit results, including adjunction CommShift compatibility;
msearch LeanFinder with “Predicates specifying the signed cone shift chain
comparison and counit normalized ordinary derived shift for completed scalar
extension” gave eight generic derived shift/t-structure results. Mathlib grep
`completedScalarShift(ChainEquation|OrdinaryNormalization|RepresentativeProperty)`
gave zero hits. The same rg query in WeilConjectures gave zero and in Sheaf found
exactly these existing definitions at lines 47, 58, 78, plus their uses. The DAG
name/concept search found only their record on the shift theorem. The coordinate
definition node owns four distinct definitions, as its declaration list and full
statement confirm. blueprint_refs search “completed scalar shift” gave zero
matches and its ancestor query named `def-fd-trace-function`. These actual search
results are recorded in the new node. No duplicate Lean definitions are created.

## Return repair and second reading by Q88

The immutable head 4eb8f99f1b5a was returned for H2/H13: a theorem was a statement
dependency solely to access three plain definitions in its module. I compared
the saved node with the current main node: the retained changes were the Lean
record and three added statement dependencies. The initial saved-packet dry run
passed as commit 6b8c0970aee without pushing. I then replaced the offending
statement dependency by the definition node above and updated this report and
the Lean note. The item's Lean source, theorem signature, mathematical statement,
proof, proof_deps and all other fields are retained. The prescribed delivery
wrapper rebases the repaired packet onto current main.

I reread all three existing predicate bodies and the new TeX side by side. The
chain equation composes a tensor shift then shifted c on one side and c then
the specified strict shift on the other. The ordinary normalization composes
the specified derived shift then shifted counit on one side and the inverse
localization shift, counit of the shifted complex, localized tensor reindexing,
and forward localization shift on the other. The representative predicate is
exactly five conjuncts: cone formula for every complex and integer, chain
equation, ordinary normalization, strict normalization, and NatTrans.CommShift
for actual χ and the two supplied derived shifts. No existential compatibility
claim or new arbitrary comparison appears in the new definition node. Its
statement names its five recorded dependencies and has empty proof/proof_deps.
Zero and negative shifts, identity coefficient embeddings, empty schemes, and
independent scheme/coefficient universes remain included. The original
clause-by-clause theorem self-check above still applies unchanged. The theorem
node removed from stmt_deps is not needed to define any of these predicates.
