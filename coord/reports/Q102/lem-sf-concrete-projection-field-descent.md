## Worker report

The item module `Sheaf.Paper.ConcreteProjectionFieldDescent` states
`WeilConjectures.ProjectionCoefficient.concreteProjectionFieldDescent` with a `sorry`
proof. All auxiliary definitions have actual data. The operation-datum dependency is
left byte-identical to live. A new definition node records tensor cocycles and is the
only addition to the item statement-dependency list.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md` (the sentence transporting the integral map to field
stages), and `sec-six-functors-basics/sk-thm-sf-pf-field/thm-sf-pf-field.proof.md`,
Compatibility and the finite-field-of-definition paragraph. The item is the compatibility
part, rather than the invertibility assertion of thm-sf-pf-field. Its ten-step accepted
proof is reproduced in the theorem docstring.

Hypotheses and clauses:

* The fixed finite-field and coefficient data are `{D : FiniteFieldDatum.{u}}`,
  `{C : D.CoefficientDatum}`, and finite-dimensional `E` over `Padic C.l`.
  These retain p prime, q=p^a, a>=1, k the algebraic closure, l prime and l != p,
  and the fixed algebraic closure C.Qbar. The coefficient integer ring, uniformizer and
  positive quotients are the imported `Padic.coefficientExtension*` constructions;
  `{n : Nat} {hn : 1 <= n}` parameterize the operation datum at a positive finite level.
* `S : SixFunctorOperationDatum D C E n hn` is the unchanged landed operation datum.
  No stronger replacement structure is used, and no projection invertibility is assumed.
  `tensorCoherence : TensorCoherence S.closure` makes the source's supplied tensor
  identity/tower/inclusion normalization explicit, using the new definition node. It
  carries exactly these cocycles, not Primitive mu/gamma or rationalTensorIdentity.
  The parent already records the PF equation in SixFunctorExchangeComparison.projection.
* `Q : SixFunctorCompactifiedSquare D` selects an arbitrary compactification. Its X,Y,Z
  are finite-type schemes over D.k. The fields include the open and proper factors,
  factorization and identity/base-change coordinates; taking the identity square gives
  any chosen compactification, as in the existing `FixProjectionCompactification.identitySquare`.
  `[IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
  [QuasiCompact Q.f.hom.left]` are precisely separated and finite type for f.
  There is no separated structure-morphism binder on X, Y or Z.
* The integral inputs are `K,N : sfIntegralConstructibleCategory ...`, the actual complete,
  bounded constructible full subcategories. Only `S.integralFiniteTorDomain Q.Y N` is
  required; there is no extra finite-Tor assumption on K.
* The first conjunct is the typed equality
  `transported (S.higher.rationalExchangeComparison Q) K N = PF_rat(QK,QN)`.
  Its source and target are conjugated by the canonical operation comparisons, as the
  node says. This removes the returned literal HEq assertion, which incorrectly needed
  an identity tensorator assumption. No rationalTensorIdentity is present.
* The second conjunct quantifies over every `E0 <= F` in the actual finite coefficient
  fields inside C.Qbar and all rational inputs, not just integral morphisms.
  `transported (S.closure.coefficientExchangeComparison h Q) K N = PF_F` is the ordered
  comparison square. `sourceIso` is tensor followed by support; `targetIso` is support
  followed by tensor and pullback. All are composites of the recorded isomorphisms.
* `EndpointCocycles` writes both identity and two-step tower equations at both endpoint
  bifunctors, using the actual stage-system associator and `sixFunctorStageUnitor`.
  It quantifies over repeated fields, not just strict inclusions.
* `InclusionCoherence` states the analogous equation relating the common-stage inclusion
  to a field enlargement at both endpoints. `EnlargementLaw` explicitly equates the
  conjugated common-stage components before and after enlargement.
* The inclusion conjunct is `transported (S.closure.commonStageExchangeComparison E0 Q)
  K N = PF_common`. The inclusion is the existing literal pair-category inclusion,
  whose morphism is its Hom-colimit class. This is exactly the representative definition;
  inclusion coherence and the enlargement equation give independence of enlargement.
* `InverseLaw` quantifies over an inverse arrow a with both inverse equations and asserts
  that `transportedInverse`, constructed by the reverse endpoint comparisons, is an
  inverse of the component at the target stage. The integral clause also explicitly
  states both equations for Q(a) and Q(PF). The final conjunct gives these inverse laws
  after scalar extension and after common-stage inclusion, for any inverse representative.
* `Natural` is the actual bifunctor naturality equation for arbitrary morphisms in both
  variables. It is asserted at rational, finite field and common stages.
  `EqualityLaw` is forward transport of any equality with these specified endpoints,
  so it applies in particular to any equality of the displayed specified composites.
  It never reflects equality through rationalization or extension.
* There is no rational-to-finite reduction map or hypothesis requiring a rational arrow
  to admit an integral arrow lift or a rational isomorphism to lift integrally.

Dependency declarations read and reused:

* `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `.CoefficientDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with its imported integer-ring/uniformizer/quotients.
* `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum` and its imported
  `SixFunctorHigherOperations`, `SixFunctorCommonStages`, `SixFunctorCoefficientComparison`,
  `SixFunctorExchangeData.projectionComponent`, `SixFunctorExchangeComparison`,
  `SixFunctorCommonStageCoherence` and `sixFunctorStageUnitor`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage.projection`,
  `ExchangeProjectionAdjunctionComparison` and `ExchangeProjectionScalarCocycle`.
  The former is the proper right-adjoint projection mate followed by gamma and conjugated
  by the supplied compact-support realization. The parent already retains units/counits
  for ordinary, support and open adjunctions, as well as pullback-composition compatibility.
* `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`,
  normalized against the actual quotient-tower projections; the parent's supportConstruction
  uses the corresponding total-limit model. No separatedness of a base structure map.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageSystem`,
  `inclusion`, `Pair`, `ofHom`, `transport`, and `representatives`. The pair category is
  intrinsic and uses actual common-stage Hom colimits, without Karoubi completion.

Every currently recorded proof-dependency module is imported privately: ConcreteIntegralProjectionCone,
CompactificationCompletedRealization, FiniteFreeCompletedScalarComparison,
IntegralScalarExtensionConstructibleIntrinsic, IntegralOperationsScalarComparisons,
ScalarExtensionTowerCoherence, OrdinaryAdjunctionScalarCompatibility, OpenTensorNormalization,
CompletedOpenTensorSystemRealization, CoefficientRealizationTransport,
SfScalarExtensionComposition, and PbcScalarExtension. These retain the accepted proof plan.

Edge cases checked on the signatures: zero K or N and integral torsion objects killed by Q;
identity field inclusion E=F, repeated fields in a tower, ramified extensions, and arbitrary
rational arrows (including nonintegrally liftable rational isomorphisms). The finite-field
index includes composita, so two common representatives have a common further field.
Empty schemes are not excluded. Finite-type structure maps need not be separated.
The coefficient categories and the schemes share the universe convention of the recorded
operation datum; no extra equality of site object and morphism universes is imposed.

Searches actually made (wrapper logs are in searches.jsonl):

* msearch leanfinder: “Specified compactification projection formula components commute
  with rationalization scalar extension and common finite coefficient field descent”.
  Eight hits, concerning galLift and homogeneous localization/Proj, no exact match.
* msearch loogle: “Functor.map_inv, NatTrans.naturality”. Zero hits; the service reports
  unknown identifier Functor.map_inv. This is not recorded as evidence of nonexistence.
* msearch grep: “map_inv|map_isIso”, Mathlib CategoryTheory. Found the generic
  `Functor.map_inv` in Mathlib/CategoryTheory/Iso.lean:497 and preservation of isomorphisms;
  these do not state the geometric component or its endpoint comparison cocycles.
* rg of WeilConjectures and Sheaf for projection/scalar/rational and the proposed names;
  grep of WeilConjectures for the item id. No exact item declaration. The upstream
  CoefficientReduction and ProjectionFormula/Rational modules discuss the compatibility;
  the latter explicitly says scalar-field compatibility is not stated. They do not
  implement the raw-localization and common-stage component theorem of this item.
* The existing `CoefficientRealizationTransport` is conditional generic transport;
  it does not assert this concrete field-stage statement. Its framework is imported
  as a proof dependency, without duplicating its definitions.

No statement correction or STATEMENT-DISPUTED flag. The source-supplied cocycle
condition is explicit; the item asserts no tensor cocycle for arbitrary unnormalized
choices of comparison isomorphisms.

## New nodes

`def-sf-projection-tensor-coefficient-cocycles`, in
`Sheaf.Paper.ProjectionTensorCoefficientCocycles`, defines `TensorCoherence` on the
existing SixFunctorCommonStages. Its three conjuncts are the identity equation with
sixFunctorStageUnitor, the tower equation with stageSystem.assoc, and the inclusion
equation with stageSystem.transIso. All three quantify over every compactified square,
scheme and finite-stage objects; no finite-Tor or projection invertibility condition
is added to this predicate. Source: the current thm-sf-pf-field proof's Compatibility
and common-field paragraphs, and fix-prop-projection-formula's field-stage sentence.
The new node is cited in the item's stmt_deps. Its module defines real Prop data;
there is no new sorry.

Searches for this new notion were actually run through msearch.py: LeanSearch
“Tensor comparison isomorphisms for coefficient extension satisfy identity tower and
inclusion cocycles” gave eight generic tensor/localization results, including
IsLocalization.algebraTensorEquiv and MonoidalCategory.tensorIso; LeanFinder
“Identity, tower and inclusion cocycles for tensor comparison isomorphisms of finite
coefficient field extension in a six functor datum” gave eight generic tensor-congruence
and cotangent results. Neither is the predicate on the recorded six-functor datum.
Loogle “SixFunctorExchangeComparison, SixFunctorCommonStages, tensor” gave an unknown
identifier, recorded as such rather than evidence of nonexistence. Mathlib grep
“TensorCoherence|SixFunctorExchangeComparison|SixFunctorCommonStages” returned no hits.
Direct rg of WeilConjectures and Sheaf found other cochain and monoidal coherence
structures, but no exact predicate. blueprint_refs.py search “tensor cocycles” found
only rem-trf-classical-framework, and its ancestor command returned
fix-prop-projection-formula. Nearby DAG nodes about projection tensor coefficient
comparison, common-stage inclusion tensor comparison, common tensor comparison descent,
and open-total tensor coefficient coherence were read: they concern different data,
not the recorded SixFunctorCommonStages comparisons. The new node's mathlib_searches
records the actual wrapper search results, and searches.jsonl retains their logs.

## Returned-delivery repair

The immutable returned head was d962bd53d070. Each requested correction is made:

1. `def-fix-six-functor-datum.json` is copied byte-for-byte from current live. Its
   SixFunctorOperationDatum declaration and all twelve recorded declarations are
   untouched. The replacement ProjectionNormalizedOperationDatum module is removed.
2. TensorCoherence is owned by the new definition node and module above, cited by
   the item. The theorem uses its explicit cocycle hypothesis instead of rebinding
   the parent record to a narrower operation datum. The four concrete endpoint
   helpers source, target, sourceIso and targetIso now belong to the item module.
3. Primitive, mu, gamma and rationalTensorIdentity declarations/fields are removed.
   The rational clause is the transported rationalExchangeComparison equation.
   All other accepted clauses, hypotheses, universes, docstrings and the single
   theorem sorry are retained.

The initial preparation compile captured the old import before the file edit and
reported ProjectionNormalizedOperationDatum missing. That stale-import check was
superseded by compilation of both repaired files; it was not delivered unchanged.

## Second reading by Q102

I reread the node, current source, new definition and theorem signatures after repair.
No other agent was started, per the dispatcher instruction; the maintainer provides
independent review. This reading identified and removed the narrower parent rebind
and literal HEq, and checked that the three new tensor equations are exactly the
previous tensor predicate, with no primitive fields. Tensor coherence is supplied as
an explicit hypothesis: arbitrary tensor comparison choices in the parent do not
imply these equations. Its node defines that hypothesis without modifying the parent.
I also checked each accepted clause above, the source/target directions in inverse
transport, identity and ramified inclusions, zero objects, rational isomorphisms without
integral lifts, and the absence of separated structure-morphism assumptions. The
common-stage comparison d_h is directed from T_h followed by i_F to i_E, matching
stageSystem.transIso in the actual inclusion equation.

Validation: scompile.py compiled both final delivered files in dependency order,
including the explicit tensorCoherence binder. No errors or warnings were reported.
The only postponed proof is concreteProjectionFieldDescent. The final deliver2.py --no-push check printed
`OK (dry run): commit ab0ee8f404b passes the preflight and compiles; nothing pushed`.
Its staged packet contains exactly the report, item/new-node records and the two Lean
modules; the byte-identical parent node is not staged. No global build was run.
