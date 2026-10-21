## Worker report

The theorem `WeilConjectures.TensorComparisonDescent.tensor_comparison_localization_descent`
states the conditional descent lemma. The integral hypotheses are explicit data plus a validity
predicate; the conclusion existentially constructs the rational structures, normalized rational
system, common-stage structures and normalized common-stage descent data. No theorem is proved.
The quotient categories, module derived tensors and scalar localizations are the recorded ones.
No Karoubi completion or faithfulness hypothesis on the integral functors is introduced.

Hypothesis-by-hypothesis correspondence:

- `l`, `Fact l.Prime`, `Ω`, `Field Ω`, `Algebra (Padic l) Ω`, and `IsAlgClosure` give the
  specified prime and algebraic closure. `Index` is `Padic.FiniteCoefficientFields`; `integerRing`
  is the actual `Padic.coefficientExtensionIntegers`, `FieldOf` is definitionally the actual field.
- `C`, `Category`, `Preadditive`, `Linear`, `MonoidalCategory`, `SymmetricCategory`,
  `MonoidalPreadditive`, `MonoidalLinear`, and `IntegralData.Valid.finiteBiproducts` express the
  arbitrary additive linear symmetric monoidal categories and bilinear tensor.
- `IntegralData.F`, `.perfect`, `.tensor` specify the functors, perfect values, inverse strong
  tensor comparison and inverse strong unit comparison. Conditions 2 and 3 are additivity and
  linearity; condition 4 is the square with the actual Koszul derived symmetry. CoreMonoidal
  includes tensor naturality, associativity and both unit constraints.
- `.S` is the actual StageSystem (its associator includes the tower cocycle); `.transitionTensor`
  and `.identity` give the coherent strong transition data. Conditions 5--7 are additivity,
  semilinearity and symmetry. Conditions 8--9 are the two tower identity equations; 10--13
  make identities and towers monoidal for tensor and unit.
- `.phi` supplies all components; condition 1 is their naturality, 14--15 their identity and
  tower equations, and 16--17 their balanced tensor and coefficient-unit squares. `scalarTensor`,
  `scalarUnit`, `scalarComp`, `scalarIdentity` are projections of uniquely normalized scalar
  coherence data, using the recorded derived B, not arbitrary comparison maps.

Conclusion clause-by-clause correspondence:

- `Rat` is the existing raw ScalarLocalization: unchanged objects, scalar-first tensor Hom
  modules. The canonical coefficient equivalence identifies its localization ring with E;
  this is the symmetric convention for the node's Hom tensor E notation.
- `RationalData.Valid.tensorObject`, `.unitObject`, `.tensorArrow` specify the literal objects
  and scalar-product pure-tensor formula. `.associator`, `.symmetry`, `.leftUnitor`, `.rightUnitor`
  specify localization by one of every integral constraint. The strong monoidal structures
  supply every coherence equation.
- `RationalData.object` and validity `.arrow` give exactly B(F(X)) and a times B(F(f)).
  `.tensorFormula` and `.unitFormula` give B(tau) followed by the balanced tensorator, and
  B(unit) followed by the balanced coefficient unit. `.symmetric` uses signed symmetry.
  `.perfect` and `.finite` place the image in bounded finite-dimensional complexes.
- Rational `.transitionObject`, `.transitionArrow`, `.transitionTensor`, `.transitionUnit`,
  `.identity`, `.tower` prescribe rationalization of all integral transition data. Additivity,
  symmetry, both tower identities and all four monoidal identity/tower equations are explicit.
- `.kappaModel` fixes derived-versus-termwise field extension on EVERY complex by its actual
  localization comparison. `.phiFormula` is the integral-to-rational scalar square;
  `.phiIdentity`, `.phiTower`, `.scalarTensorSquare`, `.scalarUnitSquare` retain all normalized
  scalar equations, including identity field inclusions.
- `CommonData.G` is a genuine functor on the actual quotient PairCategory, with `.object`
  giving the pair (E,F_EX); validity `.arrow` is the conjugated representative formula using
  phi inverse at the source and phi at the target. Thus it is independent of representatives.
- `tensorAt` is U_L. `tensorMove` is precisely d_{L,K}: inverse transition tensorator followed
  by both tower comparisons. `gamma` is tau_L followed by the two phi maps. `targetMove`
  is e_{L,K}, with the balanced scalar tensorator and both field tower maps.
- Common validity `.tensorStage` and `.tensorObject` use the compositum. `.sourceAtClass`
  specifies its comparison at every common extension as an actual quotient representative;
  `.tensorArrow` fixes tensors of morphism classes. `.sourceAtFormula`, `.sourceAtTransport`
  retain the canonical source tensor and its d transport. `.unitObject`, `.unitAtClass`,
  `.unitAtTransport` fix the base-field unit and its scalar transport.
- `.stageComparisonFormula` fixes stage restriction by the prescribed object equality.
  `.omegaModel` fixes field-to-Ω comparison on every complex. `.targetAtFormula` fixes the
  canonical balanced target tensor under the existing faithful realization, and
  `.targetUnitFormula` fixes its normalized coefficient unit. `.realizationSymmetric` fixes
  its Koszul symmetry.
- `.tensorFormula` is the tensor comparison class at EVERY common L; `.transportEquation`
  is gamma_L F_L(d) phi^{-1} = e B(gamma_K), with the required source transport retained.
  `.unitFormula` gives the unit from EVERY finite base field. CoreMonoidal plus `.symmetric`
  express naturality, associativity, symmetry and both unit equations. Taking a further
  compositum handles incomparable common fields, with no ordering restriction in the formulas.

Dependency declarations used: `DerivedCategory.IsPerfectRingComplex` in PerfectRingComplexGeneral;
`WeilConjectures.ScalarLocalization` and its localization functor in CategoryTheory.ScalarLocalization;
`sfRationalCoefficientEquiv` in SfRationalizationKaroubi; actual StageSystem, PairCategory, mkHom,
iota and transIso in upstream StageSystem.Basic; the finite-field index in FiniteCoefficientFields;
`DerivedCategory.PerfectScalar.B`, modelMap, symmetry in PerfectScalarTensorCoherence;
`fieldDerivedScalarExtension` and pointFdScalarExtension in FieldComplexScalarExtension;
fieldScalarTower and fieldScalarUnit in FieldDerivedScalarTower; PointFdQbar,
pointFdQbarStage, pointFdQbarStageComp and pointFdQbarRealization in PointFdQbarCategory.
GeneralAlgebraicallyClosedCoefficients is imported by CommonTensorComparisonRepresentatives
for its recorded common-stage dependency;
its geometric specialized category is not used as a replacement for arbitrary C_E.

Edge cases checked: zero objects and zero Hom modules; zero and arbitrary localized scalars;
repeated fields and identity inclusions, with specified non-strict identity comparisons;
nonfaithful and zero integral functors; arbitrary perfect models and their shifts (signed symmetry);
common fields not containing the initially chosen tensor field (pass to a further compositum);
nontrivial source associators and both unit constraints. No flatness assumption is added to
integral scalar maps. The target field comparisons are fixed on all complexes, not just cohomology.

Searches: msearch LeanFinder and LeanSearch queries for descent of monoidal functors through
rationalized Hom modules and common finite fields found general monoidal localization and ordinary
filtered-colimit APIs, not this statement. Loogle for Linear, Monoidal, LinearScalarExtension found
no exact interface (the last identifier does not exist). Mathlib grep for ScalarExtension,
LinearLocalization, LocalizedCategory and for TensorComparison/IntegralData/RationalData/CommonData
found no matching record. Exact msearch responses are recorded in the new nodes' mathlib_searches.
Project/upstream rg found specialized geometric point-fibre records and general StageSystem,
but no arbitrary integral system with these scalar tensor/unit squares. DAG and blueprint searches
for tensor comparison and rationalization were read: specialized point-fibre systems and
FdCoefficientComparison do not supply the generic data of this conditional lemma.

No STATEMENT-DISPUTED or correction of the item's mathematical statement is needed.

## New nodes

`def-sf-integral-tensor-comparison-system` packages the arbitrary integral hypotheses, using
existing perfect complexes, scalar B and normalized balanced coherence. It does not construct a
point fibre or assume the geometric point-fibre system. Its source is the conditional hypotheses
extracted from the blueprint's final coefficient paragraph. The searches above found no such
arbitrary system. Its validity predicate is a definition with complete data.

`def-sf-rational-tensor-comparison-system` packages the precise raw-localization conclusion,
including the pure-tensor formula, prescribed tensorator, localized transitions and normalized
field comparisons. Existing raw ScalarLocalization is reused. The source is the rationalization
paragraph and DAG steps 1--5. It asserts no existence and duplicates no scalar-localization notion.

`def-sf-common-tensor-comparison-descent` packages the common-stage representative formulas and
explicit source/target transport, using existing PairCategory and PointFdQbar. The source is the
common-stage paragraph and DAG steps 6--11. It asserts no existence. It is separate from generic
StageSystem descent because it includes the normalized tensor, signed symmetry and coefficient unit.

`def-sf-common-tensor-comparison-representatives` defines the actual stagewise maps U, d,
gamma and e and image transport before assembling the common-stage monoidal descent record.
Its module CommonTensorComparisonRepresentatives has complete data and no theorem. It is the
explicit representative part of the source's common-stage construction, not an extra hypothesis.
The same searches found general StageSystem transport but no tensor representative with this
given phi and both scalar towers. CommonTensorComparisonDescent imports this definition node.

## Dependency modules

`lem-sf-perfect-scalar-tensor-coherence`: the original nested existential interface has no
named projections for normalized comparisons. The repair appends `CoherenceData`,
`CoherenceData.Normalized`, `perfect_scalar_tensor_coherence_data` (unique existence, sorry),
and `coherenceData` to the existing `PerfectScalarTensorCoherence.lean`. All original source
bytes, all eight recorded declarations, the primary declaration `perfect_scalar_tensor_coherence`,
its signature, and all original mathematical lean-record values are retained. The declaration list gains
four names, `lean.note` explains the extension, and mandatory `lean.by` identifies NN as
the author of this extension. The auxiliary theorem packages
the same normalized comparisons: finite-projective model equations and naturality determine
the tensor, unit, composition and identity maps uniquely. `IntegralTensorComparisonSystem`
imports the extended owning module directly. The replacement Data module is removed.

Delivery is by this dispatcher worker as instructed; independent mathematical review is the
maintainer's subsequent review. No independent second reading is claimed here.


## Returned-delivery repair

H13 is repaired by extending the original owning module and record in place. The original
`perfect_scalar_tensor_coherence : Coherence` theorem remains owned by its node; the additional
unique-existence theorem is recorded under that same node. The original source was checked
against the current server using `scompile.py --source`. The original live node and the
retained saved packet were compared without git commands. The original eight declarations
remain the unchanged prefix of `lean.declarations`, with four names appended.

The two advisory text slips belonged to the removed module header; neither occurs in the
merged source. The GeneralAlgebraicallyClosedCoefficients import is removed from the integral module and
placed in CommonTensorComparisonRepresentatives, whose node explicitly cites the common-stage
construction. Arbitrary integral categories remain those supplied by C_E.

Repair validation: all six delivered modules compiled separately with the prescribed
`scompile.py` wrapper against the live published library. Every compile finished within
60 seconds, with no diagnostics. In particular, the extended owning module, its direct
integral consumer, and every downstream consumer compile. A sandbox self-check confirms
that the live source is a byte-identical prefix of the extended module, non-lean dependency
fields are unchanged, all original lean-record values except the required delivery-author
field are retained, and the declaration
list consists of the original eight names followed by exactly the four requested names.
The initial saved-packet dry run passed mechanically; the H13 content repair above is
substantive and is validated by a fresh dry run before pushing.

The repaired-packet dry run required `lean.by = NN` for the dependency extension.
This metadata field was updated from NG to NN as required by the delivery schema;
the original module header still credits NG. The module, primary declaration and statement,
branch, date, existing flag, and eight original declaration names remain unchanged.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
