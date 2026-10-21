## Worker report

The delivery states `WeilConjectures.CounitRealization.counitRealizationSubstitution`
in `Sheaf.TraceFormula.CounitRealizationSubstitution`. Its conclusion is the
conjunction `WordLaws M ∧ ScalarLaws M`. There is one postponed theorem, with
`by sorry`; its docstring records all eleven steps of the node's proof. All other
declarations are explicit syntax, actual functor/comparison constructions, or
Prop-valued records packaging the clauses of this same node. No definition selects
data from a new existence assertion. The original node statement is unchanged.

Hypothesis and clause correspondence:

* Prime ell is `(l : ℕ) [Fact l.Prime]`. `Coefficient l` packages a carrier field,
  its `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]` instances. This is only binder
  packaging, not a new definition of a coefficient extension or its valuation ring.
  The coefficient rings, spectral absolute value, uniformizer and quotient maps are
  the imported `Padic.coefficientExtension*` constructions. Inclusions of coefficient
  fields are their `AlgHom` embeddings; identity and composite embeddings are allowed.
  As in the existing realization-model dependency, these encode the finite
  subextensions of a fixed algebraic closure by their field structures and inclusions;
  no chosen closure appears in any operation or equality being asserted.
* `Location l` packages a coefficient and a `Scheme.{u}` with
  `∀ x, Invertible (l : X.residueField x)`. The empty scheme is allowed. The
  pro-etale site is the imported `Scheme.ProEt`; its objects have universe u+1
  and morphisms universe u. No equality between these site universes is imposed.
  The completed sheaf and positive quotients are exactly the dependency's
  `completedIntegralCoefficientSheafUnrestricted` and `integralCoefficientSheaf`.
* The category of entire strict systems is `coefficientSequenceDerived` (the
  derived category of `coefficientSequenceModules` on the ringed sequence site).
  Reduction and the adjunction are `(M.system a).reduction` and
  `(M.system a).adjunction`; realization is `coefficientSequenceLimit`. The
  normalized predicate is the dependency's `IsNormalizedCoefficientSequence`,
  which uses the specified transition-adjoint isomorphisms, not an unrelated tower.
* Supplied normalized models are `Models`: each `system` is the existing
  `CoefficientDerivedSystemCalculus`; `roos` is `IntegralComparisonRoosModel`;
  `pullback` and `scalar` are the existing `IntegralComparisonPullbackModel` and
  `IntegralComparisonScalarModel`, including their representative normalization.
  It assumes none of the invertibility or substitution conclusions. The existing
  `integralComparisonReductionCounit_formula` identifies the actual adjunction
  counit with coefficient change of the K-injective-normalized tower counit.
* A primitive `Primitive.pullback E f` evaluates by
  `integralComparisonDerivedSequencePullback` / `integralDerivedPullback`;
  `Primitive.scalar E L ι X` evaluates by
  `integralComparisonDerivedSequenceScalar` / `integralScalarExtensionOfUniverses`.
  `Primitive.model` is the supplied model's `realization` isomorphism, exactly b.
* `Primitive.comparison` is the displayed formula r: `b.hom.app (L.obj C)`
  followed by `L.map (O.system.map (adjunction.counit.app C))`. This uses the
  entire counit and makes no independent finite-level choices.
* Normalization of C and D is `IsNormalizedCoefficientSequence`. Their bounded
  constructible complete realizations are `sfIntegralConstructible (L.obj C)`.
  `Word.Allowed` recursively requires that predicate at each intermediate system,
  including source and target. Intermediate normalization is a conclusion of
  `WordLaws.invertible`, not an additional domain assumption.
* `WordLaws.counit` records canonical effectivity of the whole-system counit.
  `WordLaws.invertible` says every recursively defined word comparison, including
  a one-letter word, is an isomorphism and its output is normalized.
* `WordLaws.naturality` states exactly
  `w.completed.map (L.map φ) ≫ r_D = r_C ≫ L.map (w.system.map φ)` for any
  whole-system derived morphism `φ : C ⟶ D` on the stated domain. This includes
  inverse morphisms; no finite-evaluation equality or faithfulness is assumed.
* `Word.nil`, `Word.atom`, `Word.comp` represent arbitrary finite words with
  their parentheses. `Word.comparison` is identity at the empty word, the
  primitive formula at a letter, and `v.completed.map r_w ≫ r_v` at a cut.
  `WordLaws.cut` states this formula; `parenthesization` states the three-block
  reassociation equality, applicable at every subtree. `wholeCounit` identifies
  the coherent reduction of a primitive word comparison with primitive insertion
  followed by `O(e_C)`. Together with recursion this gives entire-counit
  substitution at every intermediate object.
* `Comparison` contains the specified pullback compositor, pullback identity,
  scalar/pullback comparison, scalar associator, scalar multiplication unitor,
  functor associator/action unitors, identities, inverses, composites and both
  whiskerings. `Comparison.system` evaluates these by the recorded canonical
  maps of entire systems. `Word.transport` is literally
  `r_w ≫ L.map (t.app C) ≫ inv r_v` (Lean composition order).
  `WordLaws.comparison` states the unique isomorphism characterized by that square;
  combined with invertibility this is precisely the displayed conjugation formula,
  and never an identification with an arbitrary completed isomorphism.
* `WordLaws.composition`, `inverse`, `leftWhisker` and `rightWhisker` give the
  explicit cancellation and context identities. The right-whisker equation includes
  `w.completed.map (r_z)` and `v.completed.map (r_z)`, so it retains the actual
  comparison at the inserted input instead of silently identifying unequal objects.
* `ScalarLaws.associator` compares the realization of the existing whole-system
  scalar associator with `CompletedLineTensor.associator`. Its definition is
  `chi_ML.symm ≪≫ ordinary_ML.mapIso chi_LE.symm ≪≫ alphaTensor ≪≫ chi_ME`.
  `CompletedLineTensor.chi` is `asIso (completedScalarComparison.app K)` with
  invertibility supplied by the recorded finite-free comparison; thus this is
  exactly the node's quotient/zero-shifted-product-normalized chi, not a new
  completion map. `associatorData.derived` is fixed by the ordinary balanced
  tensor formula and universal K-flat counits. The equation is cross-multiplied
  by r_direct to state the identical conjugation without a new chosen inverse.
  `intrinsic_complete` converts the very same constructible-complete input into
  the existing unrestricted completeness encoding; no completeness assumption is added.
* `ScalarLaws.unit` realizes the actual system multiplication unit as
  `CompletedLineTensor.unit`, defined by `chi_EE.symm ≪≫ ordinaryUnit.app K`.
  Its dependency's identity normalization identifies this with multiplication
  and the inverse canonical completeness unit, precisely as required.
* No finite Tor-amplitude, separate finite-reduction faithfulness, finite-field
  base, nonempty scheme, or bound beyond the stated constructible-complete domain
  appears in the statement.

Dependency declarations read and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported real
  `Padic.coefficientExtensionRing`/transition/uniformizer constructions.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology`. `def-weil-scheme-morphism-properties` is a convention node
  with no declaration; the relevant condition is the explicit residue-field
  invertibility in `Location`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, and the actual completed sheaves
  and projections it publicly retains (used by every sequence module below).
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientSequenceLimit`,
  `IsNormalizedCoefficientSequence`, `coefficientDerivedSystemEvaluationCalculus`.
* `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, the quotient/restriction
  maps underlying the already defined normalized sequence predicate. We use the
  actual sequence predicate and do not introduce a private tower interface.
* `Sheaf.Paper.IntegralComparisonSequenceSystems`:
  `integralComparisonDerivedSequencePullback`, `integralComparisonDerivedSequenceScalar`,
  `integralComparisonSystemComposition`, `integralComparisonSystemUnit`,
  `integralComparisonSystemScalarPullback`; all generator-normalized before localization.
* `Sheaf.Paper.IntegralComparisonRealizationModels`:
  `IntegralComparisonRoosModel`, `IntegralComparisonPullbackModel`,
  `IntegralComparisonScalarModel`, `integralComparisonReductionCounit_formula`.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: the recorded operations module,
  retaining the global `integralDerivedPullback` used by the existing model.
* `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` (same canonical global scalar operation).
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedScalarComparison`, `finiteFreeCompletedScalarComparison` and its
  actual quotient/zero-shifted-product representative construction.
* Two already landed statement nodes are added to stmt_deps, with no other
  node edits: `lem-trf-quotient-system-mixed-coherence` supplies the canonical
  `integralComparisonSystemScalarComposition` and `integralComparisonSystemScalarUnit`
  in `Sheaf.Paper.QuotientSystemMixedCoherence`; `lem-pur-completed-line-tensor-coherence`
  supplies `CompletedLineTensor.associator`, `chi`, `unit`, `associatorData.derived`,
  `ordinaryUnit` and `intrinsic_complete` in `Sheaf.Paper.CompletedLineTensorCoherence`.
  These avoid duplicating either scalar associator or scalar multiplication data.
  Neither node reaches this item in the existing DAG/imports.
* All recorded proof-dependency modules are imported, including
  `EffectiveComparisonRealizationModels`, `NormalizedDVREffectivity`,
  `KFlatResolutionIndependentCoefficients`, `DerivedChangeOfRingsCochainModel`,
  `QuotientScalarComparisonDescent`, `ChangeOfRingsKFlat`,
  and `Sheaf.TraceFormula.IntegralConeCounitRealization`.

Edge cases checked: empty word, empty first/second/third blocks, all binary
parentheses, identity pullback and scalar changes, E=L, L=M and E=L=M, inverses
and composites of comparison maps, zero systems, empty schemes, arbitrary derived
morphisms, ramified coefficient maps, and site object/morphism sizes u+1/u.
No n=0 quotient is inserted: the dependencies index n+1 by n : ℕ. Uniform
cohomological support is imposed only by `sfIntegralConstructible`. The comparison
maps themselves are explicit on the ambient derived system categories.

Searches made (2026-10-21):

* msearch.py leanfinder: "Naturality and substitution of a reduction realization
  adjunction counit for words of pullback and scalar extension functors" returned
  eight generic adjunction/scalar-counit hits, including
  `PullbackShift.adjunction_counit` and ModuleCat change-of-rings counits; no match.
* msearch.py loogle: "CategoryTheory.Adjunction.counit_naturality,
  CategoryTheory.whiskerLeft, CategoryTheory.NatIso" returned no match, with
  unknown identifier `CategoryTheory.whiskerLeft` (the implementation uses
  `Functor.whiskerLeft`/`Functor.isoWhiskerLeft`).
* msearch.py grep: "counit.*substitution|realization.*word|scalar.*associator"
  in Mathlib CategoryTheory returned zero hits.
* msearch.py leansearch: "Whole-system counit substitution of normalized derived
  quotient systems and compatibility with scalar associativity" returned eight
  unrelated quotient/scalar and ModuleCat counit results; no match.
* rg of `lean/WeilConjectures` and `lean/Sheaf` for counit/substitution,
  realizationWord, and scalar-associator names found the existing separate
  `CompletedOperationTowerSubstitution` (tensor/pullback only),
  `IntegralPullbackComparisonRealization` (the downstream consumer), and the
  canonical scalar-comparison helpers above. None states this item. Searching
  the exact item id in `lean/WeilConjectures` gave no hits.
* Additional searches for coefficient packages found
  `ConstructibleExceptionalCoefficients.FieldStage` with identical binder data.
  Its owning node is downstream of this item (transitive DAG path), and its
  module imports the later exceptional-adjunction framework. `Coefficient` here
  is explicitly only syntax packaging of the existing Field/Algebra/finite
  hypotheses; no coefficient object, valuation ring or mathematical notion is
  redefined. Reusing that downstream convenience record would introduce a cycle.
  The fixed-closure interface `Padic.FiniteCoefficientFields` and the canonical
  small models in `AlgebraicallyClosedCoefficients` were also inspected; they
  use the same finite-dimensional fields and AlgHom inclusions, with extra
  closure/index machinery absent from the model dependencies and this equality.

Source checked directly: local Stacks sites-cohomology.tex,
`lemma-derived-limit-is-ok` (K-injective whole-sequence limit); current blueprint
main-20261015 `prop-trf-karoubi-independence.proof.md`, final transport sentence;
all eleven agent-expanded proof steps in the item's node. No statement correction,
new independent definition node, or unusable dependency record was needed.

Validation: the complete module passed scompile.py on the server with no errors
and no warnings, both sandbox and final library namespace checks, under the
unchanged 60-second limit. Final dry-run and delivery results follow the wrapper.

## Second reading by NC

The dispatcher explicitly forbids starting another agent and assigns the
maintainer's independent review after delivery. This section records the worker's
second clause-by-clause pass, not a claimed independent reviewer.

I reopened the item and the whole module, checked both directions and order of
all comparison composites, and expanded the imported scalar associator and unit
rather than relying on their names. The source uses usual right-to-left function
composition; Lean uses `≫`, so r_w first, then L(t), then r_v inverse is the
correct direction. The unit has no residual r_empty since that is identity.
The right-whisker square includes the inserted word comparison, and parentheses
are retained in Word and compared by explicit associator constructors.

This pass added the generic functor associator and both action unitors to
Comparison, and added the direct scalar word's Allowed condition to the scalar
associator law so every expression obeys the node's domain restriction. Removed
the only two line-width warnings and recompiled cleanly. Every actual mathematical
operation, model, counit, quotient-normalized chi, associator and scalar unit is
imported from the dependency declaration, with only binder/syntax packaging local.
The only sorry is the theorem matching this node. No STATEMENT-DISPUTED issue was found.
