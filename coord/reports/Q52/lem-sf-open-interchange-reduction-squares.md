## Worker report

The module `lean/Sheaf/SixFunctors/OpenInterchangeReductionSquares.lean` states
`WeilConjectures.OpenInterchangeReduction.openInterchangeReductionSquares`.
Its only postponed proof is this theorem, with `sorry`. Every helper definition
contains real data. The module docstring identifies the blueprint source and the
main theorem docstring carries all nine proof steps of the node.

I read the item's complete statement, proof, source and statement dependencies,
including the signatures/docstrings of their recorded declarations. I read the
maps-used paragraph in
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`.
The expanded open-adjunction and four-factor argument is the item's own proof.

### Hypotheses and clauses

- The fixed finite field and algebraic closure are `D : FiniteFieldDatum`.
  `C : D.CoefficientDatum` supplies the prime `C.l` and `C.l ≠ D.p`.
  `E`, `Field E`, `Algebra (Padic C.l) E` and `FiniteDimensional` specify the finite
  coefficient extension. The existing coefficient rings use the chosen uniformizer
  and positive exponents `n+1`, so no level zero is substituted.
- `W : S → Scheme` and `FiniteTypeFamily W D.k` specify the finite-type schemes.
  `scalarReductionSource`, `coefficientSequenceDerived` and
  `IntegralSystemRealization.calculus` are the actual completed-ring category,
  strict-system derived category, and reduction/total-limit adjunction on the
  small pro-etale sites. Their units and counits are reused literally.
- `o : GeneratorReduction.Operations` retains the actual system operations,
  section-normalized compositors, normalized open comparisons, ordinary ringed
  models, normalized integral open comparisons, and actual realization model.
  `Word.integralValue` uses completed pullback/tensor, the strict proper-image
  tower and localized ringed open extension. No arbitrary comparison map is a
  theorem parameter.
- `Word` has variables, coefficient unit, tensor, separated finite-type pull,
  proper push and quasi-compact open constructors. It has no compact-support
  constructor. `Word.r` is the literal recursive coefficient comparison required
  by the statement: identity on variables, scalar-unit map on units, primitive
  comparison followed by the functor of the child map, with both tensor slots.
  This published interface is reused rather than defined again.
- `Admissible` says each input is derived complete, constructible and of finite
  Tor amplitude, and `SystemAdmissible` checks its actual reduction. The latter
  includes normalization, compatible `Origins`, constructibility, and the common
  cohomological and Tor bounds `lo hi torLo torHi` at every positive level.
- `_hIntermediate` checks those same bounds at every vertex of both endpoint
  words. `_hGenerator : g.admissible ...` checks all six additional systems in
  the four-factor lambda: restriction of J_k, J_s, S_s, and their S_q images.
  These checks are unbounded in word length. `_hB` and `_hC` impose the source's
  length-three restriction on generator endpoints alone.
- `_hStructural : StructuralSquares ...` is the uniform family of coefficient
  squares for tensor associator/unitors, pull and push composition, geometric
  adjunction unit/counit, and open adjunction unit/counit on admissible input and
  intermediate systems. Its quantification has no length-three restriction,
  hence includes the internal length-four structural words.
- `OpenGenerator` selects exactly canonical beta, gamma, lambda_Q and Gamma_Q.
  For beta, `GeneratorKind.openBaseChange` carries `IsPullback` and the geometric
  hypotheses. For gamma, `openTensor` has both independently typed inputs.
- For lambda_Q and Gamma_Q the existing generator constructors carry
  `k ≫ p = r ≫ i`, both quasi-compact open hypotheses and both properness
  hypotheses. They do NOT carry `IsPullback`. `GeneratorKind.systemMap` uses
  `IntegralSystemRealization.properOpenLambda`, which is precisely cartesian
  conjugation, restriction factor, clopen comparison, and push compositor.
  Its Gamma case is the open-adjunction transpose of inverse lambda. The ringed
  map uses the independently fixed `ringedProperOpenLambda` and its own open
  adjunction; `integralMap` transports it through the actual completion maps.
  The clopen comparison is normalized by the inverse open unit, rather than an
  arbitrary isomorphism.
- `Assertion ... g` expands to
  `B.r ≫ g.systemMap = reduction.map g.integralMap ≫ Cw.r`.
  This is exactly each displayed coefficient square, in Lean's left-to-right
  composition order. It is in the derived category of whole strict systems.
- `OpenIsomorphism` selects beta, gamma and lambda. The next conjunct explicitly
  states invertibility of the system and integral maps and `InverseAssertion`,
  the inverse coefficient square. Thus `inverseOrZero` in that square is the
  genuine inverse on this domain; its off-domain zero branch has no role.
  Gamma_Q is excluded from the inverse claim.
- The final conjunct quantifies over input-family maps `f : ∀ k, K k ⟶ L k`,
  with both families in the same stated domain. `SquareNaturality` gives the
  naturality of both vertical coefficient maps and of both horizontal arrows.
  `systemInputMap` and `integralInputMap` supply the functorial action of the
  already specified word in each independent input slot. No finite evaluation
  or faithfulness assumption appears.

### Dependency declarations used

The recorded module/declaration interfaces are reused as follows:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the original
  `Padic.coefficientExtensionRing` and transitions reexported by its imports.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus` and
  `CoefficientDerivedSystemCalculus`, accessed through the published calculus.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearSections.semilinearDerivedSections`, the simultaneous-system model.
- `def-weil-scheme-morphism-properties` is a convention record, not a missing
  declaration. Its named Mathlib classes are `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsProper`, `IsOpenImmersion` and `IsClosedImmersion`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `IntegralOnSlice.completedTensor`; completed operations use the published
  global `integralCompletedTensor` / `integralDerivedPullback` presentations.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage` (recorded Roos
  datum); the existing generator interface's `integralSystemDerivedDirectImage`
  supplies the simultaneous strict-tower specialization.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`:
  `IntegralOpenReduction.integralOpenReductionComparison`; the actual mate is
  used by the existing `RealizationModel.openReduction` / `GeneratorReduction.openR`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`; the system version is
  `IsNormalizedCoefficientSequence`, used in the published `SystemAdmissible`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness`, retained inside `IntegralSystemRealization.Origins`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`, with the
  same integral and pro-etale Tor predicates through `Admissible`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`:
  `basicOperationsCoefficientReduction` and the fixed coefficient comparisons.
- `Sheaf.SixFunctors.IntegralSystemOperations`: `Operations`, `Compositors`,
  `OpenComparisons`, `properOpenLambda`.
- `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`: `CanonicalBridge`,
  `RealizationModel`, `RingedModels`, `RingedOpenComparisons`,
  `ringedProperOpenLambda`.
- `Sheaf.SixFunctors.IntegralSystemExpressionDomain`: `Expression.domain`,
  `Origins`, `Good`; the unit-containing basic-word specialization is the existing
  `GeneratorReduction.Word` and its admissibility predicates.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:
  `ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting`, and its actual
  section-normalized operation and lambda definitions.

Proof imports additionally supply the immersion comparison, tensor completion
model and site tensor descent. The generic adjunction dependency matches are
`CategoryTheory.mateEquiv`, `conjugateEquiv` in `Adjunction.Mates` and
`Adjunction.comp` in `Adjunction.Basic` (full signatures and formulas read).

### Existing interface and import direction

`GeneratorReductionStatement` was already published before this new proof node
was split out. This delivery imports its definitions (`Word`, `GeneratorKind`,
recursive comparisons, admissibility, and `Assertion`), and does not invoke its
`generatorReductionCoherence` theorem or either other postponed theorem. No
second definitions of these notions are introduced. The sole current DAG citer
is `lem-sf-generator-reduction-coherence`. A reciprocal proof import into that
current module would make a Lean import cycle and must be skipped under
stages/2-statements §3(7); a later data-only module extraction can expose these
shared existing declarations to its proof. No upstream file is changed here.

### Edge cases and checks

I checked identity maps, the empty open, zero inputs, coefficient unit leaves,
positive level n=1, repeated variables and independent tensor slots. None is
excluded. There is no `Nonempty I` or `Finite I` assumption; each word has finitely
many vertices even when the ambient input family is arbitrary or empty. Internal
length-four words are allowed by the structural hypothesis and lambda checks.
A noncartesian square with an extra component of V times_Z W is allowed: its lift
selects one clopen component, and Gamma is not asserted invertible.

No statement correction and no new or repaired dependency node are needed. The
node's statement and all other fields besides `lean` are preserved. The theorem
uses a uniform structural-square family on the admissible domain; it does not
assume the open squares it concludes.

### Searches

All searches below were actually run with the prescribed msearch wrapper or rg.

- LeanFinder: `Integral reduction preserves canonical open base change tensor
  isomorphisms and proper open adjunction mates`: eight hits, including integral
  base-change properties and `Scheme.Modules.conjugateEquiv_pullbackComp_inv`;
  no exact coefficient-system theorem.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`: twelve hits on
  generic mates/conjugates and pasting. These do not state the geometric theorem.
- Mathlib grep: `mateEquiv|conjugateEquiv` in `CategoryTheory/Adjunction`:
  twelve displayed hits, chiefly `Mates.lean` and `CompositionIso.lean`.
- LeanSearch: `coefficient reduction commutes with open base change and
  adjunction mates`: eight hits on scheme restrictions and unrelated open/topology
  adjunctions; no exact coefficient-system theorem.
- Project/upstream rg: item ID in `lean/WeilConjectures`, and
  `openInterchangeReductionSquares|OpenInterchangeReduction|coefficient.*(open|Open).*(mate|Mate)`
  in `lean/WeilConjectures` and `lean/Sheaf`: no exact theorem. Related supported
  coefficient mate modules concern a different assertion. Broader searches found
  the existing `GeneratorReductionStatement` helpers, which are reused.
- The upstream-name index search for open reduction / proper-open coefficients
  produced unrelated older nodes, not this item.

Compilation: the final module is checked with scompile.py, in both sandbox and
library module modes, with the default 60-second limit. An initial import typo
(`Adjunction.Comp`) was corrected to the recorded `Adjunction.Basic`; no library
or tool repair was needed. The final module compiled cleanly in both modes (9.0 s and 6.9 s).
The required deliver2.py --no-push dry run passed preflight and compilation
with OK, producing review commit 3dd863c6660; nothing was pushed by that run.

## Second reading by Q52

I reread the finished module against the complete node and the recorded formulas.
This is a self-check; the dispatcher's maintainer supplies the independent review.
The beta and gamma cases use the published open-unit-normalized maps. The lambda
case is the four-factor composite, and Gamma is its open transpose. The proper/open
constructors contain no cartesianness hypothesis. I verified the direction of
`Assertion` and `InverseAssertion` against both displayed equations. The additional
lambda systems retain the same integer intervals independently of endpoint length.
I added explicit invertibility to the inverse clause, removed a needless `Finite I`
restriction, and made input naturality an explicit conclusion (all four edges of
the square). I also checked that every helper is documented with the source/node,
all variables and universes are explicitly bound, every line is at most 100
characters, and the only theorem proof is `sorry`.
