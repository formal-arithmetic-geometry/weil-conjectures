## Worker report

Item: lem-sf-package-field-operation-realization. Module:
`Sheaf.Paper.SfPackageFieldOperationRealization`. The declarations jointly state the
item, with all theorem proofs `sorry`. No source statement is corrected, no new DAG
node is introduced, and the existing closed-data definition record is extended lean-only as requested in return H2.

The current source read is `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/prop-functor-package.proof.md`, with the item's six explicit DAG
proof steps. The current blueprint reorganizes the opening coefficient references;
the node spells out the field-passage assertion being formalized.

Hypothesis and conclusion correspondence:

* The finite-field algebraic closure and characteristic are `D : FiniteFieldDatum.{u}`.
  `C : D.CoefficientDatum` supplies a prime `C.l`, `C.different : C.l ≠ D.p`, and the
  chosen algebraic closure `C.Qbar` of `Padic C.l`. `E`, `Field E`, `Algebra`, and
  `FiniteDimensional` express a finite coefficient field. Fields contained in the
  closure are `Index C.l C.Qbar`, with their recorded small models `Coefficient.{u}`.
* Separated finite-type k-schemes are `X Y : SixFunctorSpace D` and the two
  `IsSeparated ...obj.hom` instances. The map `f : X ⟶ Y` is already over k;
  `IsSeparated f.hom.left`, `LocallyOfFiniteType`, and `QuasiCompact` are precisely
  separated finite type. `S : SixFunctorOperationDatum` is the specified operation
  datum, not arbitrary maps. Its auxiliary positive exponent is `n+1`; every
  positive exponent is represented. The result is independent of this finite-level
  index. Residue-field invertibility is supplied by the inlined base-field unit
  mapped through each geometric residue-field algebra map; it is not an added hypothesis.
* The integral category is exactly `sfIntegralConstructibleCategory`: derived complete,
  every positive constructible reduction, and one interval independent of exponent.
  `sfRationalConstructibleLocalization` is Q, and the rational category is the raw
  scalar localization, not its Karoubi envelope. The common category is literally
  `generalAlgebraicallyClosedConstructibleCategory`.
* `SfFieldIntegralPreservation` renders the stated conditional preservation assumption:
  its five conjuncts refer to `integralDerivedPullback`, `integralCompletedTensor`,
  `sfCompletedDerivedDirectImage`, every actual compact-support tower derived limit,
  and `constructibleIntegralHomPairs` (which unfolds to ambient Hom preservation).
  The support condition quantifies over each limit realization rather than replacing
  the specified construction by an arbitrary functor. `preserves` is assumed at E for
  the first theorem and at every finite stage for common-stage descent.
* `sfPackageFieldOperationRealization` gives the five displayed identifications as
  functor equalities in the dependency's normalized unchanged-object models. The
  first equality is Q then rational pullback = integral pullback then Q; the second
  is (Q,Q) then tensor = completed integral tensor then Q; the third is integral
  Hom then Q = pair rationalization then rational Hom; the fourth and fifth are
  Q then specified direct/support = specified integral direct/support then Q.
  Equality is the normalized natural identification here, not equality of arbitrary
  model choices. `S.higher.rationalModelNormalization` prescribes the identity
  components for direct/support comparisons. The pullback/tensor/Hom definitions
  prescribe their objects and pure-tensor actions uniquely.
* `sfFieldRationalHomPairs` is only the actual pair-rationalization functor between
  the two recorded permitted-pair categories. It makes no new copy of internal Hom.
  Its proof field is the input pair's existing property. Hom preservation makes
  every pair permitted; the last conjunct explicitly states that at rational level.
* The evaluation conjunct identifies `podRationalClosed.evaluation` with Q applied to
  `podIntegralClosed.evaluation`, retaining the completed tensor normalization.
  This API places Hom before its input; the signed tensor symmetry gives the
  argument-first convention used in the node's displayed explanatory equation.
* The inline lambda `(fun {α : Sort _} {P : α → Prop}
  (_ : ∃! x : α, P x) (x : α) ↦ P x)` applies the predicate of each owning-node
  rational operation uniqueness theorem to the published functor. This is exactly
  its published object and pure-tensor map specification,
  including separate linearity for tensor and contravariant/covariant Hom.
  `SfFieldUnaryLocalization` states additivity, the unchanged object formula, and
  c tensor a mapped to c tensor F(a) for direct/support. Pure tensors span all
  localized Homs, so these clauses cover arbitrary denominators and sums.
* `sfPackageFieldScalarRealization` fixes the pullback, tensor and Hom comparisons as
  the rationalizations of their recorded integral comparisons. Its
  `PodPartialHomCompatibility` states invertibility, naturality on arbitrary localized
  arrows, evaluation preservation and its transpose equation. The last HEq identifies
  that transpose map with the specified `rationalHomScalarComparison`, so the
  evaluation assertion is about the given comparison, not another isomorphism.
* `sfPackageFieldHomScalarCoherence` spells out the Hom identity and tower equations
  using `sfRationalScalarUnit` and `sfRationalScalarComp`, including the inverse
  associator in the contravariant argument. `sfPackageFieldScalarTower` states the
  corresponding actual pullback and tensor associator equations.
* `sfPackageFieldUnaryDescent` gives stage-system morphisms with finite functors equal
  to the datum's rational direct/support functors and beta equal to its specified
  coefficient comparison. Their `coh` field is the scalar-associator tower equation;
  equality of their induced `functor` with the datum's common-stage operation retains
  its conjugation formula on all representatives. The existing `mapAt`,
  `tr_mapAt`, `functor_map_mkHom`, and quotient construction ensure independence of
  common field and eventual equality. Objects and arrows are those of the pair category.
* `sfPackageFieldCommonStageRealization` inlines the three owning-node `_existsUnique`
  predicates at the published common-stage functors, hence both the literal object and all arrow formulas at every common
  field. `commonStageHomPairs` holds for all pairs. `PodCommonTransposeNormalization`
  specifies inverse transpose at every common field with the recorded tensor/Hom
  comparison maps. Specializing to the identity gives precisely the finite-stage
  evaluation representation. The last displayed equation is naturality in the
  second variable and dinaturality in the first on arbitrary common-stage arrows.
  It identifies evaluations under isomorphic input representatives, while the
  representative laws identify operations under every enlargement.

Dependency declarations read and used:

* `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, its higher and
  closure fields; the publicly imported `SixFunctorOperationDatumStages` supplies
  `SixFunctorSpace`, `SixFunctorHigherOperations`, `SixFunctorCommonStages`,
  `SixFunctorCoefficientComparison`, `SixFunctorCoefficientModelNormalization`,
  and the specified scalar comparisons and coherence.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `stageSystem`,
  `inclusion`, `ofHom`, `representatives`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded rational/common-stage
  operation declarations and their `existsUnique` characterizations, permitted-pair
  categories, and normalized scalar and common-stage comparisons.
* `Sheaf.Paper.BasicOperationsCoefficientReduction` is retained as a plain proof
  import. No plain definition from this theorem module occurs in the statement:
  the predicate projection and common-stage laws are inlined from the owning-node
  `DerivedPullbackTensorHom` `_existsUnique` characterizations.
* `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `podIntegralClosed`,
  `podRationalClosed`, `podCommonClosed`, `PodPartialHomCompatibility`,
  `podPartialHomComparison`, `PodCommonTransposeNormalization`.
* `Sheaf.Paper.CompletedTensorHomTranspose` is a plain proof import only. The
  residue-unit term is inlined; no definition from this theorem module is used
  in the statement.
* `WeilConjectures.CategoryTheory.StageSystem.Functor`: `StageSystem.Morphism`,
  `Morphism.functor`, its beta conjugation formula and transport compatibility.

The additional statement dependencies are the already landed definition nodes
`def-weil-derived-pullback-tensor-hom` and `def-sf-adic-closed-reindexing-maps`.
Their statements, lean records, and full declaration docstrings/signatures were read.
The closed-reindexing owner already lists `PodPartialHomCompatibility`,
`podPartialHomComparison`, `PodCommonTransposeNormalization`, `podCommonClosed`, and
`podRationalClosed`; its lean-only extension now also owns `podIntegralClosed` and
its unique ordinary-completion-unit characterization. No theorem node is added to
stmt_deps merely for a plain definition in its module. Proof imports retain every recorded proof dependency:
SemilinearScalarLocalization (`existsUnique_semilinear_extension`),
QcqsCompactSupportRealization (`sfQcqsCompactSupportRealization`), RationalOperations
(`coef_rational_operations`), IntegralOperationsScalarComparisons
(`scalarOperationsOrdinary_tower`), SpecifiedHomScalarEvaluation
(`specifiedHomScalarEvaluation`), SfStrictDirectImageScalarComparison
(`strictDirectImageScalarComparison`), SfScalarExtensionComposition
(`sfRationalScalarComp`), BasicOperationsCoefficientReduction
(`basicOperationsCoefficientReduction`), and CompactSupportFiniteFieldIndependence
(`sfCompactSupportFiniteFieldIndependence`). No import cycle back to this item was
found when traversing the additional statement nodes' DAG dependencies.

Edge cases read against the interfaces: empty schemes and zero objects are allowed;
no nonempty scheme, perfect first input, torsion-free Hom or faithful localization is
assumed. Identity extensions, repeated stages and arbitrary sums of fractions are
included. Ramified extensions use the actual normalized coefficient embeddings.
Two different input fields use their finite compositum; arbitrary larger common
fields and equal representatives are covered by the same formulas. All variables
and universes are explicit, with autoImplicit and relaxedAutoImplicit disabled.
The same u for the global datum and coefficient closure follows the recorded
operation datum; common-stage construction uses its existing small coefficient models.

Searches (the wrapper also saved its search log in the sandbox):

* LeanFinder via msearch.py: “Rationalizing completed constructible derived sheaf
  operations and descending internal Hom evaluation to common finite coefficient
  fields” returned eight hits on light condensed internal Hom and normalization of
  rational sections, none this statement.
* LeanSearch via msearch.py, same query: eight hits on ordinary sheafHom and light
  condensed Hom, none on these derived-complete constructible coefficient categories.
* Loogle via msearch.py: `CategoryTheory.Functor.IsTriangulated` returned twelve
  generic triangulated-functor results; none gives field passage and evaluation.
* Mathlib grep via msearch.py: `rationaliz.*(internalHom|internal.hom|evaluation)|common.?stage`
  in CategoryTheory returned zero hits.
* rg in lean/WeilConjectures for fieldOperationRealization variants and rational
  evaluation found only an unrelated rational representation comment. The requested
  blueprint-id grep there returned no matches. rg in lean/Sheaf found the downstream
  SfPackageCoefficientDomains reference and existing partial operation APIs; its
  sfPackageFieldValues lacks arbitrary localized arrows, scalar coherence and
  representative/evaluation descent, so is not the whole assigned statement.
* rg of dag/lean_names_upstream.json and Mathlib CategoryTheory found no collision
  for the new declaration names.

Validation: the prescribed scompile.py compiled the module in both sandbox and
library module modes, with no errors or unexpected warnings. The subsequent final
compile and deliver2.py preflight results are recorded by the delivery tool.

## Second reading by Q13

Performed an in-thread second reading with the node and module reopened; the
dispatcher explicitly forbids starting another agent. This is not claimed as an
independent maintainer review.

Checked all five displayed formulas in the order pullback, tensor, direct image,
support, internal Hom against the functor equalities in the first theorem. Hom
appears third in Lean because its evaluation clause uses the pair functor; its
variance and direction agree. Checked that evaluation uses completed integral
rather than ordinary tensor evaluation, that scalar Hom is the specified transpose,
and that arbitrary arrows enter both bilinear characterizations and the final
naturality equation. Added scalar Hom identity/tower equations and the pullback/tensor
associator equations after this reading so scalar compatibility is explicit.
Checked direct/support beta normalization and equality with the actual induced
pair functor. Confirmed common-stage Hom uses the compositum and every larger
field, and specializing inverse transpose to identity gives its evaluation.
No source-statement correction or unused mathematical hypothesis was found. The
returned ownership issue is repaired below by a lean-only dependency-record extension. The maintainer supplies the independent review.


## Dependency modules

`def-sf-adic-closed-reindexing-maps`: section 1(B), existing:true lean-only extension,
explicitly required by return H2 for immutable head 617cf0161e28. The current main
record in `dag/nodes/sec-six-functors/def-sf-adic-closed-reindexing-maps.json` already
owns `podRationalClosed` and its unique pure-tensor characterization, in addition
to the common-stage closed datum and comparison interfaces. It omits the integral
closed datum needed for the integral evaluation in this item's rationalization
formula. Add the exact existing `WeilConjectures.podIntegralClosed` and
`WeilConjectures.podIntegralClosed_existsUnique`, both in the same published
`Sheaf.Paper.DerivedAutomorphismHomEvaluation` module. Read their full docstrings
and signatures: integral closed transposition is uniquely normalized by ordinary
evaluation preceded by the actual completion unit; the rational closed datum is
its additive localization. The owner retains every existing declaration and its
existing primary declaration/signature; only `lean` changes. No Lean dependency
module is copied or modified, and no mathematical statement changes.

## Repair of immutable head 617cf0161e28

H2, addressed clause by clause:

1. Replace the three theorem stmt_deps `lem-fix-operation-reduction`,
   `lem-pod-derived-automorphism-hom-evaluation`, and
   `lem-coef-completed-tensor-hom-transpose` by actual definition ownership.
   They are not statement dependencies in the repaired packet. Their modules
   remain proof imports where they supplied the proof plan; the published
   `proof_deps` field is preserved (it already includes lem-fix-operation-reduction).
2. Cite `def-sf-adic-closed-reindexing-maps` for the compatibility, transpose
   comparison, common-stage normalization, and common-stage closed datum. Its
   latest record already owns `podRationalClosed`; extend only its lean record
   with `podIntegralClosed` and its unique characterization, under section 1(B).
3. Inline `operationUniqueSpecification` as the anonymous predicate projection,
   and inline each `commonStage...RepresentativeLaws` as that projection applied
   to the owning `def-weil-derived-pullback-tensor-hom` `_existsUnique` theorem and
   its published functor. No new named definition, proof, or notion is introduced.
   These replacements unfold literally to the predicates accepted by the reviewer.
4. Inline every use of `coefficientTransposeUnits`: map
   `finiteFieldDatumPrimeUnit D C.l C.different` through the geometric structure
   map's `residueFieldAlgebraMap`, then take its `IsUnit.invertible`. This is the
   original definition's body and supplies exactly the same residue-field inverse.
5. Rebased node data on current main by rereading the current node and preserving
   all non-delivery fields. The current main item's lean record is absent;
   its statement and proof remain identical to the returned version. Preserved
   the latest closed-owner record, including Q115's rational-closed ownership,
   and extended only its lean field. The delivery wrapper rebases on live main.

Second repair reading (in-thread, no agents as instructed): searched the delivered
Lean for all four rejected helper names and confirmed they are absent. Checked
that the predicate projection still returns `P x`, so all original object, arrow,
scalar, and representative conditions remain. Compared the inlined residue term
with the published coefficientTransposeUnits body; it is identical. Confirmed
that the closed owner retains its existing rational and common closed data and
adds exactly the missing integral datum/characterization. All five formulas,
completed evaluation, scalar and representative clauses checked by L are retained.
The source statement has not changed and no `statement_change` is needed.
