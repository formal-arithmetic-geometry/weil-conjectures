## Worker report

The module `Sheaf.Paper.ZlOpenCompactSupportRestriction` states the node as
`WeilConjectures.ZlOpenComplement.restrictionIdentities`. Its structures are packages
of this node's clauses, on the dependency declarations, rather than new geometric
or coefficient notions. Every theorem has only `sorry`; definitions have actual data.
The closed-domain helper theorems are elementary consequences needed to avoid imposing
extra finite-type assumptions on the complement. Their proof plans are documented.

Hypotheses and clauses:

- The finite-field datum is `D : FiniteFieldDatum.{u}`; the prime and distinctness
  are `[Fact l.Prime]` and `hl : l ≠ D.p`.
- U₀ and X₀ are objects of `Over (Spec (.of D.k₀))`, with
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on their structure maps.
  These express separated finite-type schemes. `j₀` is an Over morphism with
  `IsOpenImmersion j₀.left` and `QuasiCompact j₀.left`.
- `i₀ : Z₀ ⟶ X₀` has `IsClosedImmersion i₀.left`; `hcomp` identifies its
  topological image with the complement of the image of j₀. No reducedness or
  chosen scheme structure is imposed on Z₀. The theorem's two local instances
  derive its finite-type properties via `closedDomainFT` and `closedDomainQC`.
- `map D` is literally `Over.pullback` along k₀ → k. The geometric schemes are
  the dependency's `D.geometricFiber`, not separately chosen copies.
- Finite coefficient fields are `[Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The integer ring, uniformizer, positive
  quotient rings and quotient maps are the existing `Padic.coefficientExtension*`
  and `pbcIntegralDatum` constructions. Quantification over arbitrary finite models
  includes every finite subfield of Ω; common-stage fields use the dependency's
  `Coefficient.{u} l Ω F` small models. No coefficient/scheme universe equality
  is imposed on the algebraic closure `Ω : Type v`.
- `integral`, `rational`, and `common` are exactly Li* Rj! in the three stages.
  They use `Compactification.ofIsOpenImmersion (map D j₀)`, hence (j,id), and the
  recorded completed, rationalized and common-stage pullbacks.
- `StageComparison.integralIso`, `.rationalIso`, and `FieldDescent.commonIso`
  are natural isomorphisms to the constant chosen zero object, in Dᵇc itself.
  Naturality is part of `≅`, not just a collection of object isomorphisms.
- Integral canonicity is `.integral_zero`. The empty pullback square is the actual
  `square`; `CompletedNormalization.empty` states its emptiness. `.openReduction`
  retains the recorded `IntegralOpenReduction.Comparison`, including d, r, their
  completion-unit formulas and strictModel. `.pullbackComparison` retains the
  normalized integral/completed comparison, including finite projections.
- `.ordinary_zero`, `.completed_zero`, and `.completed_target_zero` assert zero
  for the actual specified exchanges and empty-open extension. `.comparison_equation`
  identifies z with the completed exchange followed by the zero-target identification
  after coefficient transport. It quantifies every endpoint identification, so in
  particular it includes the prescribed d_j and completed-pullback identifications.
  This is equivalent to the canonical equation because a zero target admits exactly
  one arrow: no arbitrary map or Nonempty functor is substituted for an operation.
- `.strict_zero` is an equation of natural transformations in the full coherent
  system category, before evaluation or realization. `.finite_zero` additionally
  states all finite evaluations. The map is the actual reduction of z, not a map
  chosen from finite evaluations. The dependency's r/strictModel retains transitions.
- `.rational_localization` identifies the rational map with the image of the integral
  one under `sfRationalConstructibleLocalization`, with only equality transport at
  its prescribed object carrier. `.common_normalization` does the same under
  `GeneralAlgebraicallyClosedCoefficients.inclusion` for every finite-stage object.
- `.scalar_compatibility` uses `scalarRestriction`, constructed from the actual
  `integralPullbackScalarComparison` and `sfCompactSupportScalarSystemMap`.
  Its final zero arrow is the unique arrow from scalar(0) to 0.
  `.scalar_associator` writes both composites using `sfIntegralScalarComp` on
  the actual source and target, including both scalar-restriction mates.
- `GeometricVanishing` quantifies every algebraically closed field F in the ambient
  arbitrary scheme universe and every g : Spec F → X disjoint from the open image.
  It produces f : Spec F → Z with f ≫ i = g, and states zero after the recorded
  integral, rational, and common-stage pullbacks, for every input K. The source
  invertibility of l is derived by `pointInvertible` from the residue-field map
  of g. There is no closed-point, rational-point, finite-extension, or prescribed
  residue-field condition on g.

Dependency declarations used (all existing; added landed nodes are recorded in
stmt_deps and were checked not to create a dependency cycle):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `FiniteFieldDatum.geometricFiber`.
- Mathlib open/closed-immersion and morphism-properties modules:
  `IsOpenImmersion`, `IsClosedImmersion`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, and `MorphismProperty.overPullbackMap`.
- `Sheaf.Paper.QcqsCompactSupportRealization` and its public imports:
  `sfCompactSupportFiniteIntegralFunctor`, `sfCompactSupportFiniteFunctor`,
  `sfQcqsCompactSupportRealization`, and `Compactification.ofIsOpenImmersion`.
- `Sheaf.NumberTheory.Padics.CoefficientExtension`: the actual integer rings,
  uniformizer and finite quotient system. The adic presentation is `pbcIntegralDatum`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `commonStageDerivedPullback`,
  `integralPullbackScalarComparison`; the integral point clause uses its ambient
  `integralDerivedPullback`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`: `cbcDatumOrdinaryExchange`,
  `cbcDatumCompletedExchange`, `cbcDerivedOpenShriek`, `cbcCompleteProperty`.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`:
  `IntegralOpenReduction.Operations`, `.TensorComparison`, `.Comparison`.
- `Sheaf.Paper.IntegralPullbackCompletedComparison`:
  `IntegralCompletedComparison.Comparison` and `.derived`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilPrimeInvertible`,
  `FiniteFieldDatum.geometricFiber_coefficientPrimeInvertible`.
- `Sheaf.Paper.CompactSupportCoefficientAction`: `SfCompactSupportCoefficientAction`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `inclusion`,
  `generalAlgebraicallyClosedConstructibleCategory`, with `Coefficient` small models.
- `Sheaf.Paper.IntegralSystemReductionFullyFaithful`: `integralSystemReduction`,
  `integralSystemRings`, `integralSystemTransition`, `finiteSystemDerivedEvaluation`.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`: inherited zero objects.
- `Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms`:
  `sfCompactSupportScalarSystemMap`; `Sheaf.Paper.SfScalarExtensionComposition`:
  `sfIntegralScalarComp`; `sfConstructibleIntegralScalarExtension` is the existing
  completed scalar functor, not a replacement.

Edge cases checked: U empty; U = X (then Z empty); X empty; arbitrary nonreduced
scheme structure on the closed complement; zero input complexes; E = Q_l;
identity and composite finite coefficient extensions; every positive reduction,
including n = 0 indexing O_E/t; geometric points over nonclosed points; independent
universe for the coefficient algebraic closure. None is excluded by the theorem.
The two closed-domain properties in helper structure declarations are derived locally
in the main theorem, so they do not add assumptions to the item.

Searches (before writing):

- `msearch.py ... leanfinder "Completed adic compact support extension by zero
  restricted to the closed complement is canonically zero"`: eight unrelated
  support/topology hits, no existing statement of this node.
- `msearch.py ... loogle "CategoryTheory.Functor, CategoryTheory.IsZero"`:
  no match (the IsZero name is in the Limits namespace).
- `msearch.py ... grep "completedOpen|openCompactSupport|shriek.*[Zz]ero"`:
  no Mathlib match for the required adic/common-stage result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `openCompactSupport|OpenCompactSupport|complementaryRestriction`: no existing
  item declaration; nearby OpenCompactSupportFiniteTor and immersion-local-behavior
  modules have different statements. Narrowed reads of recorded dependency modules
  found all operations and normalization interfaces used above.
- Read the latest blueprint's full `lem-zl-quasi-finite.proof.md`, especially (1),
  and the item's five proof steps. No statement fault or disputed assertion found.

## Second reading by Q33

The dispatcher expressly forbids starting other agents; this is the same worker's
separate rereading with the node JSON and final module open, not an independent
agent review. The maintainer's independent review remains required.

I matched the hypotheses and clauses above. The reread found and fixed these issues:
(1) initially the complement's finite-type instances could have been extra binders;
the final theorem derives them locally from the closed immersion; (2) finite
vanishing must hold in the full coherent system, not only each evaluation, so both
`strict_zero` and `finite_zero` are included; (3) the redundant separate finite-exchange field was removed in the returned repair; (4) scalar associators are the dependency's normalized
`sfIntegralScalarComp`, not an unnamed isomorphism; (5) the point clause now ranges
over all algebraically closed test fields and explicitly factors through Z, with
all three coefficient stages; (6) the completed comparison equation is explicit
and universal over endpoint identifications, including the canonical d_j route.
No node statement correction or replacement dependency module is needed. The returned
repair adds definition ownership for the existing scalar-system map, as detailed below.


## Repair of returned head 6d642613c893

Compared the sandbox's returned files against the current main node and current
published dependency sources. The original item differs from main only in `lean`
and `stmt_deps`; the repaired node is based on that current main JSON. Delivery
wrappers handle refresh/rebase in their private worktree; no Git commands or writes
were made in the shared repository.

Every numbered H2 request is repaired:

1. Removed `lem-pod-integral-system-reduction-fully-faithful` from added statement
   dependencies. Added the existing definition owners `def-sf-integral-system-reduction`
   for integralSystemReduction/Rings/Transition and
   `def-sf-finite-system-derived-pullback` for finiteSystemDerivedEvaluation.
   The Lean import stays the published module because that is where the definitions
   live; its full-faithfulness theorem is not used.
2. Removed `lem-a1-integral-pullback-completed-comparison` from added statement
   dependencies. Added `def-pod-integral-completed-comparison-data`, which owns
   IntegralCompletedComparison.Comparison and .derived. The statement mentions
   the Comparison data type, not the theorem asserting its inhabitation as a tool.
3. Removed `lem-weil-compact-support-normalized-scalar-isomorphisms` from added
   statement dependencies. Added `def-zl-compact-support-scalar-system-map` with
   `existing: true`, owning exactly sfCompactSupportScalarSystemMap and its
   residue-unit helper. The existing map and its import remain; no Lean declaration
   was copied or changed, and no scalar-isomorphism theorem conclusion is used here.
4. Removed `finite_exchange_zero` and the unused public import of
   Sheaf.AlgebraicGeometry.SfFiniteOpenExtensionBaseChange. Removed the unrelated
   added theorem dependency lem-cbc-proetale-extension-zero-base-change. The required
   strict_zero/finite_zero equations still cover the node's strict finite-reduction
   maps, and the canonical completed/ordinary exchange equations remain.

The two approved theorem dependencies remain: lem-weil-scalar-extension-composition
supplies the uniquely normalized sfIntegralScalarComp, and
lem-weil-integral-constructible-triangulated supplies inherited zero objects.

Advisories repaired: moved the helper declarations requiring finite-type Z₀ into
`section ComplementFiniteType`, and closed this section before the main theorem.
Its variable context now contains no LocallyOfFiniteType/QuasiCompact Z₀ binders;
those instances are introduced only by the two displayed letI terms. Removed the
unused Noetherian and Abelian.FunctorCategory imports and both unused private proof
imports. The revised module compiles in both sandbox and library mode without
errors or warnings. The additional structure field removed above is redundant,
so neither the informal statement nor its proof/dependency history was corrected.

## New nodes

`def-zl-compact-support-scalar-system-map` records the existing definition
WeilConjectures.sfCompactSupportScalarSystemMap in
Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms and its existing
sfCompactSupportScalarResidueUnit helper. It defines the arrow obtained by the
proper/open whole-system coefficient mate, realized with its reduction counits
and normalized limit, and conjugated by the projection-normalized compact
realizations. Its source is the compact-support and final paragraphs of the latest
blueprint's lem-fix-operation-reduction proof. Its dependency
`def-weil-system-operation-exchange-realization` already owns all three underlying
realization/mate definitions; the other cited definitions own compactifications,
finite integral actions, scalar extension and geometric hypotheses. No existence,
invertibility or coherence result is stated by this new node.

Searches for this owner: LeanSearch returned eight support/test-function hits;
LeanFinder returned eight condensed/profinite/local-cohomology hits; Mathlib grep
returned zero hits. Queries and exact tool results are in the node's mathlib_searches.
Project rg found the exact existing definition only in the published module.
DAG rg found it only in the theorem-node record; no definition node owns it.
`blueprint_refs.py search 'compact support scalar'` returned zero nodes. The
existing declaration's complete signature and formula were read, as were the
complete signatures/formulas of compactRealization, coefficientExchange and
systemCompactScalar. The new node uses existing:true and introduces no Lean file.

The repair rereading confirms that removing the separate finite-exchange assertion
preserves the source's content through strict_zero/finite_zero; all mathematical
clauses accepted by the independent review otherwise retain their original Lean.
The new owner makes the dependency accounting explicit without changing that map.
