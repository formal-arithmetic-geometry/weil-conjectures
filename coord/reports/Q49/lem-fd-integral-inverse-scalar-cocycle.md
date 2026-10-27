## Worker report

The module `Sheaf.Paper.FdIntegralInverseScalarCocycle` states the node using the actual
ordinary completed-ring tensor functors, strict quotient-tower functors, quotient-cocone
completion map, and specified normalized associators. Every theorem has proof `sorry`;
the two definitions have real data. No statement correction and no disputed statement.

Hypothesis and clause correspondence:

- The global finite-field datum is `_D : FiniteFieldDatum.{d}`, the coefficient prime
  is `(l : ℕ) [Fact l.Prime]`, and its difference from the characteristic is `_hl`.
- The fixed algebraic closure is `Ω`, with `Field`, `Algebra ℚ_[l]` and `IsAlgClosure`.
  In the cocycle, E→L→M and `_e : M →ₐ[ℚ_[l]] Ω` represent the three embedded fields;
  the embeddings of E and L into Ω are the composites. In the unit theorem the final
  field is L. Injectivity of field algebra maps imposes exactly inclusions, without
  any strictness condition. The presentation theorem uses actual finite subfields of Ω
  and their canonical `pbcFiniteField` models, allowing Ω an independent universe w.
- T is `Scheme.{u}`, `[IsNoetherian T]`, with `Fact` of a finite bound on
  `topologicalKrullDim` and of invertibility in every stalk. No finite-type structure
  over the finite field, nonemptiness or dimension lower bound is assumed.
- `K : sfIntegralConstructibleCategory l E T` is precisely the full integral framework
  category underlying the recorded raw rationalization. Its image under
  `integralDetailedTransport` is the PBC integral category, by the recorded
  `integralStratifiedPerfectDetailed`. It is the coefficient-normalized identity I_F;
  no new integral category or equivalence is defined here.
- C is `completedDerivedScalarExtension`, ordinary derived completed-ring tensor.
  U is `integralScalarExtensionOfUniverses`, the published strict quotient cone.
  b is `completedScalarComparison`; `CompletedLineTensor.chi` is the very same
  component viewed as an isomorphism using finite-free completeness, with its inverse.
  Its construction, not an arbitrary map/isomorphism hypothesis, fixes the actual
  quotient cocones and zero shifted coordinate. The hypothesis that these maps restrict
  to isomorphisms is already provided on these integral inputs by the recorded theorem.
- A is `ScalarCompletionAssociatorData`. Its `ordinary` is fixed by balanced tensor
  generators and K-flat counits (`ordinary_model`); its `associator` is exactly the
  quotient-normalized A^U (`normalization`). Quantification over A retains the specified
  associator; it never replaces it by a newly chosen one. The recorded `independent`
  field expresses representative/cofinal-exponent independence for this same map.
- `fdIntegralInverseScalarCocycle` first conjunct is the node's forward equation,
  in Lean's left-to-right composition order. Its second conjunct is the inverse
  equation, with b_2 inverse at U_1 K, C_2 applied to b_1 inverse, then A^C on the left;
  the right is A^U followed by b_3 inverse. Completeness arguments are existing proofs
  (`intrinsic_complete`, `A.preserves`), not extra hypotheses on K.
- `fdIntegralInverseScalarUnits` first conjunct is b_EE = μ followed by η, where
  μ=`A.ordinaryUnit.hom` and η=`A.unit.inv`. The second is b_EE inverse followed by
  μ = η inverse. The next two conjuncts are respectively the L=E naturality square
  and the M=L multiplication/completeness square, with all functors explicit.
  The next four conjuncts record both ordinary and both completed associator unit laws;
  HEq only handles the identity algebra-map composition presentation for ordinary maps.
  The final conjunct is η followed by b_EE inverse followed by μ = identity: the
  all-equal identity square after multiplication/completeness identifications.
- Ordinary coefficient-presentation transport fixing tensor generators is the existing
  `FdOrdinaryScalarTransport`. The owning-node helper
  `fdIntegralOrdinaryPresentation_existsUnique` descends precisely its termwise
  comparison, normalized by both universal derived counits. Its unique witness
  determines `fdIntegralOrdinaryPresentation`; no arbitrary existential data is chosen.
- `fdIntegralCoefficientMap_eq` identifies the already constructed finite-stage
  coefficient map with the ordinary PBC map by every quotient projection.
  `fdIntegralCoefficientInclusion_comp` identifies direct and composite small-model
  inclusions. Both are named presentation equalities, used by `eqToHom` casts only.
  These are helper assertions of this node, not independent new mathematical notions.
- `fdIntegralOrdinaryBalancingMap` is the explicit conjugate of A^C by these uniquely
  normalized presentation transports. `fdIntegralOrdinaryBalancing` first asserts it is
  precisely `pbcAmbientScalarComp`. Its second conjunct applies actual
  `pbcRationalization.map` to that same integral arrow and equates it with the specified
  `pbcRationalScalarCompComponent.hom`. J and hJ only name the same integral image in
  its full subcategory, allowing the full-subcategory inclusion to type the localization;
  this is not a preservation or extra constructibility assumption. Such a J exists by
  integralStratifiedPerfectDetailed. No Karoubi completion or abstract rational arrow
  substitutes for the raw localization.

Dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and its
  integral category `sfIntegralConstructibleCategory` (in the imported owning module).
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory`,
  `PbcRationalCategory`, `pbcRationalization`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectCharacterization`, `integralStratifiedPerfectDetailed`,
  `integralDetailedTransport` and its normalized coefficient comparison.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedDerivedScalarExtension`,
  `completedScalarComparison`, `finiteFreeCompletedScalarComparison`, the quotient
  chain comparison and identity multiplication/completeness normalization.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `integralPullbackComparisonRealization`, `integralComparisonScalarAssociator`;
  the stated convention is conjugation by the same actual completion maps.
- `Sheaf.Paper.ScalarCompletionAssociator`: `ScalarCompletionAssociatorData`,
  `scalarCompletionAssociator`; read full structure, normalization, ordinary model,
  independence, and unit equations.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension`,
  `pbcEmbeddingAmbientTensor`, `pbcAmbientScalarComp`, `pbcEmbeddingIntegralTensor`,
  `pbcRationalScalarCompComponent`, ordinary tensor units and raw scalar localization.
- Added already-landed notion node `def-fd-coefficient-comparison-datum` uses
  `Sheaf.Paper.FdCoefficientComparison`: `FdOrdinaryScalarTransport`, its
  `.complex`, and `fdCoefficientTransportFactors`. This avoids restating transport.
- New existing-definition node `def-fd-complete-input-comparison` records
  `Sheaf.Paper.CompletedLineTensorCoherence`: `WeilConjectures.CompletedLineTensor.chi`
  and `WeilConjectures.CompletedLineTensor.intrinsic_complete`. The statement uses
  these helpers; it does not need the line-tensor coherence theorem.
- Direct owner `def-weil-pbc-finite-completed-coefficient-map` uses
  `Sheaf.Paper.PbcFiniteCompletedCoefficientMap`:
  `AlgebraicGeometry.Scheme.pbcCompletedScalarMap` (and its canonical small-field
  coefficient presentation helpers).

Edge cases checked: E=L, L=M, E=L=M, repetitions adjacent to a strict inclusion;
identity algebra homomorphisms; zero integral objects; the empty scheme; arbitrary
finite dimension bounds; ramified extensions. Nothing assumes distinct fields,
nonzero objects, nonempty schemes, unramified extensions, finite Tor amplitude of
quotient reductions, or a chain-level inverse to the completion map. Coefficient
fields are modeled in the scheme universe (finite extensions are small there), while
Ω and the finite-field datum have independent universe parameters. The pro-etale
site keeps its original object universe u+1 and morphism universe u.

Searches made (msearch Q49, this item):

- leanfinder: `Inverse completion comparison cocycle ordinary derived tensor associator
  strict quotient tower scalar extension normalized units`: eight hits, including
  tensor right-exactness inverse lemmas and
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of`; none states this node.
- loogle: `CategoryTheory.NatIso.naturality_2`: one hit, the generic naturality identity;
  it does not supply any of the actual completed sheaf functors, associators or units.
- grep: `inverse.*cocycle|completion.*associator|associator.*completion` in Mathlib
  CategoryTheory: zero hits.
- leansearch: `Inverse completion comparison between derived tensor scalar extension
  and strict quotient tower respects associators and completeness units`: eight hits,
  including `ModuleCat.extendScalars_assoc`, `extendScalars_assoc'`,
  `extendScalars_assoc_assoc` and bimodule associators; none concerns the actual
  completed derived sheaf quotient maps and the specified integral comparisons.
- rg in both live `lean/WeilConjectures` and `lean/Sheaf` for inverse cocycles,
  completion associators, the exact node id and every proposed declaration name.
  No exact existing statement. Existing `FdCompletionInverseScalarCoherence` is the
  downstream rational stage-system comparison; it does not state this integral theorem.
  Existing `ScalarCompletionAssociatorData.normalization` supplies the forward law but
  not this inverse equation, explicit two unit squares or rational presentation clause.
  The existing chi, completeness and generator transport were reused.

Sources: node's extraction proof steps 1--6, and the current blueprint at
`literature/blueprint/latest/blueprint/sec-fourier-transform/sk-cor-plancherel/def-fd-trace-function.md`.
The latest blueprint moved the trace definition to sk-cor-plancherel; the node's older
extracted coefficient-category auxiliary statement remains the assignment and is
recorded unchanged. The listed helper theorem docstrings contain their full
natural-language proofs for later implementation, all under this owning DAG node.

Validation: scompile.py against the live published build, sandbox and library-name
compilation, clean within the 60-second limit. Only the expected postponed proofs remain.

## New nodes

`def-fd-complete-input-comparison` is an `existing: true` definition node, with no
new module. Its primary declaration is `WeilConjectures.CompletedLineTensor.chi`
in `Sheaf.Paper.CompletedLineTensorCoherence` (line 378), defined by `asIso` of the
actual comparison. Its second recorded declaration,
`WeilConjectures.CompletedLineTensor.intrinsic_complete` (line 928), supplies the
augmented-tower completeness proof for intrinsic integral constructible objects.
The new node states the finite coefficient embedding, arbitrary scheme, completed
coefficient sheaves, complete input, exact forward comparison and its inverse.
The completeness helper covers intrinsic inputs without a new hypothesis.
Its signature and universe scope were read from the existing module, including
the intrinsic category’s common coefficient/scheme universe. Identity embeddings,
repeated fields, the zero object and empty schemes remain allowed. Source:
Bhatt–Scholze Proposition 3.5.1 and Definition 3.5.2 (read locally in the PDF).

New-node searches: LeanSearch returned eight ordinary adic-completion hits;
LeanFinder returned eight generic derived-isomorphism hits; Mathlib CategoryTheory
grep returned zero hits. Upstream WeilConjectures grep found none; Sheaf grep
found the exact existing helpers. DAG grep found them only in the line-tensor
theorem’s declaration list. `blueprint_refs.py search 'completed comparison'`
found only `def-weil-pbc-completed-pullback`; the exact-name search found zero
blueprint nodes. Thus this records existing data rather than defining it again.
All queries, result names and dates are in the new node’s `mathlib_searches`.

## Returned delivery repair

Repair of the independent review of immutable head `35dbc2f85d32`, point H2:
replaced statement dependency `lem-pur-completed-line-tensor-coherence` with
`def-fd-complete-input-comparison`, the requested existing-definition interface
for chi and intrinsic completeness. Also followed the advisory by directly citing
`def-weil-pbc-finite-completed-coefficient-map`, owner of `pbcCompletedScalarMap`.
The Lean file and `lean.statement` are unchanged, as requested. Compared the
sandbox item against current main: all fields except `lean` and the authorized
`stmt_deps` changes are identical. There is no mathematical statement correction.
Repair validation: `scompile.py` compiled the unchanged module in sandbox mode
(28.6 s) and library mode (28.8 s), with no errors or unexpected warnings.
The delivery dry run checks the repaired node records against the live server.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
