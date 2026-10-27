## Worker report

The module `Sheaf.AlgebraicGeometry.FieldRingedScalarAdjunctionTransport` states
`AlgebraicGeometry.ProEtale.FieldActionTransport.field_ringed_scalar_adjunction_transport`.
Its only postponed proof is that theorem. All helper specifications have actual data or
proposition bodies; none selects data from an unproved bare existence statement.

Hypothesis and clause correspondence:

- `k ks : Type u`, `Field`, `Algebra k ks`, and `IsSepClosure k ks` give the field and
  specified separable closure. The group is always `ks ≃ₐ[k] ks`, with the imported Krull
  topology; continuous generalized elements are those in `CondensedActionModule`.
- The compatible size convention is explicit: schemes and profinite tests have universe
  `u`, section groups have `u+1`, module categories and their ordinary unbounded
  localizations have `u+2`. No site object/morphism universe identification is imposed.
- `Coefficients` is the existing commutative ring object category, not merely coefficients
  coming from topological rings. `Modules R.toMon Y` uses precisely `coefficientRing`.
- `FieldData k ks R` and `e'` are the recorded normalized field presentation: exact additive
  equivalences with sections on `test k ks (Spec k) (identity) P`. Their `GeometricData`
  records actual restriction, scalar structure, and variable Galois action. Thus these
  are the given `E_R,E_R'` expressed in their normalized geometric coordinates.
  `h : FieldActionToposNormalization k ks` supplies the common set-topos equivalence
  over condensed sets, including its natural finite-operation and coefficient-ring
  comparison. `over` and `over'` identify the underlying set sheaves of these very
  module functors with the module lifts of that common equivalence.
- `FieldBalancedTensor.tensor`, `naturality` and `pure` give the balanced tensor comparison
  on these same sections; `fieldActionInternalPureTensor` transparently re-exports the original relative coequalizer
  pairing, already including sheafification. `regular` and `regular_one` normalize the
  regular module: linearity then gives identity on every scalar, not just on one.
- The two K-flat iff clauses use exactly the acyclic total-tensor test. On the action
  side `IsActionTensorKFlat` tests all acyclic action complexes; its tensor is read after
  forgetting, where the diagonal-action tensor has the original internal tensor.
  Exact conservative forgetting detects its acyclicity. The iff, together with the field
  equivalence, also gives preservation by the inverse, including arbitrary unbounded tests.
- `ScalarTransport` is the dependency's full scalar-data type. Its `restriction` is
  `ScalarAction`, retaining the underlying module and all actions. Its ordinary field
  section equation is `field_sections`; `ordinary.transpose` and `underlying.transpose`
  assert every Hom transpose, hence the ordinary units and counits. The actual scalar
  adjunctions are `Mod.extendRestrictAdjunction`, not arbitrary adjunctions.
  The existing generator `internalScalarGenerator` and sectionwise scalar adjunction give
  `m ↦ 1 tensor m` and `r' tensor m ↦ r'f(m)`, also after module sheafification.
- `ScalarTransport.derivedExtension`, `derivedCounit`, `isDerived`,
  `derivedCounit_normalization`, and `derivedAdjunction` specify the universal total
  left derivation and its actual adjunction to exact scalar restriction.
  `derived` and `underlyingDerived` preserve all transposes. Their right comparisons are
  fixed by `derived_restriction` and `underlyingDerived_restriction`.
  `shift`, `derivedCounit_shift`, `derivedAdjunction_shift`, and `derived_shift` retain
  the cited shift normalization. No flatness hypothesis is made on `φ`.
- `ScalarRepresentativeNormalization` additionally pins the extension comparison on
  K-flat representatives by the square of the actual total-left-derived counits and
  termwise ordinary extension comparison. This prevents replacing it by an arbitrary
  automorphism of a derived object.
- For every `X`, `CompactSpace X` and `QuasiSeparatedSpace X` are exactly qcqs; `a` is its
  specified structure morphism. `DirectImageScalarComparison.comparison` is the existing
  `CoefficientComparison` for actual `CondensedRing.lowerStar` and `restrictX`.
  Its `unit` field is precisely the total-right-derived-unit normalization. Its
  `identity` field says the ordinary comparison is identity on the entire abelian sheaf,
  hence on every section. In the identical ringed-composite square this uniquely
  characterizes the composition/K-injective comparison `ρ_a`.
- `GeometricScalarComparison` uses the supplied geometric section functors, not new
  arbitrary functors. Its `sections` says ordinary scalar comparison is identity on
  `X^s[P]`. Its `field`, `field'`, and `transport` identify it with transport of this
  same `ρ_a` and the ordinary field scalar square. The derived identification is fixed by the universal
  unit equations on both sides, so conjugation gives this same derived map.
  Its `CoefficientComparison.unit`
  retains the universal right-derived normalization, fixing the derived geometric map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.ProfiniteTestObjectFunctor`: `profinite_test_object_functor`; the actual
  `profiniteToProEtOf` construction is in upstream `ModuleObject.Basic`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `coefficientRing_X`, `condensedRingObj`, `isCommMonObj_condensedRingObj`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its module action and maps.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and the upstream
  right-derived framework: universal right-derived functors, computation units.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `sectionModule`,
  `forgetAction`; `CondensedEquivariantBarData`: `Ring`, `ActionAbelian`, `ScalarAction`.
- `Sheaf.AlgebraicGeometry.FieldActionScalarTransportData`: `ScalarTransport`; its public
  dependency `FieldActionTransportData`: `FieldData`, `fieldFunctor`, `ForgetData`,
  `AdjunctionSquare`, `derivedExtend`, `scalarDerivedAdjunction`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: `Mod.extendScalars`,
  `Mod.extendRestrictAdjunction`; `DerivedExtendScalars` supplies the K-flat derived pair.
- `Sheaf.AlgebraicGeometry.FieldActionToposNormalization`: `FieldActionToposNormalization`
  transparently re-exports `FieldActionTopos.Normalization`, including its coefficient comparison
  and naturality. `Sheaf.AlgebraicGeometry.GeometricSectionFunctors`: `fieldActionFieldSets`,
  `fieldActionActionSets`, `fieldActionActionUnderlying` re-export the three actual underlying-set
  functors and identify the induced module lifts. These definitions have their own DAG nodes.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`, the
  total right derivation of the actual `lowerStar`, with the original K-injective model.
- `Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent`: `Modules`, `GeometricData`,
  `test`, `restrictX`, `CoefficientComparison`, and ordinary unbounded localizations.
- `Sheaf.AlgebraicGeometry.FieldActionInternalPureTensor`: `fieldActionInternalPureTensor`,
  a transparent alias of the existing generic `comparison_internalTmul` pairing. Its definition
  node covers both the coherent topology of Profinite and the small pro-etale site. No theorem
  conclusion from `lem-pe-internal-section-tensor-comparison`,
  `lem-sfb-field-action-topos-coefficients` or `lem-sfb-geometric-sections-adjunction`
  is used to state this item; none of these three is in its `stmt_deps`.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`: actual scalar generators and
  ordinary/derived sectionwise normalization, used to interpret the local formulas.

All recorded proof-dependency modules are imported or publicly reexported by those
imports; the proof docstring follows all seven accepted proof steps. In particular it
uses the ringed tensor and K-flat transport inputs added by the stage-1 reviewer, rather
than treating preservation of colimits alone as preservation of tensor products.

Sources checked: the local Bhatt--Scholze PDF Example 4.1.10 identifies the field site
with profinite continuous Galois sets; it supplies geometric context only. The node's
conditional normalized scalar assertion is the agent assembly explicitly recorded in
its source and proof_origin, with Stacks 03CU, 03CZ, 03EL, 06YN, 06YY, 07A6 and 0D6E.
The newest blueprint direct-images paragraph was also read; no unit statement is changed.

Edge cases checked before writing: trivial Galois group; identity coefficient map;
nonflat maps such as integer coefficients to mod-2 coefficients; maps into the zero
ring; zero modules and complexes; empty profinite tests; empty qcqs scheme; arbitrary
positive and negative degrees and shifts. No nonzero, faithful-flat, boundedness,
finite-cohomological-dimension or coefficient-topological-presentation hypothesis occurs.
The inverse K-flat claim follows from the iff and essential surjectivity on complexes.
Restriction is not assumed to preserve K-injectives.

Searches (the exact wrapper results are in the sandbox searches.jsonl):

- `msearch.py ... leanfinder`: "Ringed equivalence transports scalar adjunctions derived
  scalar extension K flat and normalized coefficient restriction pushforward". Eight
  unrelated flatness/base-change results; no matching normalized field theorem.
- `msearch.py ... loogle`: `CategoryTheory.Mod.extendScalars, CategoryTheory.Adjunction`.
  Zero hits; unknown identifier for the project's extension construction in the service.
- `msearch.py ... grep` in CategoryTheory: `ScalarTransport|scalar.*[Cc]omparison|
  [Kk]Flat.*[Ee]quivalence`. Zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for ScalarTransport, the item id,
  scalar adjunction transport, and normalized comparisons: found the recorded scalar
  specification and downstream derived-section assertion, not this conditional theorem.
  Other scalar-transport declarations concern open immersions, stalks or finite models.
- Exact item-id grep of `lean/WeilConjectures`: no result. Upstream declaration index:
  no exact theorem match. Existing primitives are reused throughout.

## Second reading by Q44

This is the dispatched worker's second pass, not a claim of an independent second agent;
the brief reserves independent review to the maintainer and prohibits starting agents.
Read the complete DAG statement and all helper signatures alongside the final theorem.
Found and repaired an initially implicit hypothesis: the common equivalence over
condensed sets is now bound as `h`, and `over`, `over'` identify its two module lifts.
The already landed `Normalization` and underlying-set functors are reused.
Checked both rings, the same geometric field coordinates, all scalar Hom transposes,
K-flat preservation/reflection, the representative counit square, arbitrary nonflat φ,
qcqs quantification, the actual direct image, identity ordinary sections, and both
right-derived-unit normalizations. No node statement correction or dependency repair is
made. `DirectImageScalarComparison` bundles the existing coefficient square with its
identity equation; its `ordinary` accessor exposes those data at their fixed
additivity instances. The added specifications belong to this node's comparison, not new tensors
or copied module categories. Compiler-driven changes expose existing commutativity and
additivity witnesses and correct natural-transformation localization syntax; they do
not add mathematical assumptions.

Validation: the helper projection and representative square passed the prescribed
server compile; the final common-topos signature is checked again by `scompile.py`
and by the delivery dry run. The only postponed proof is the item theorem.

The public common-topos import exposed `WeilConjectures.integralOperationsSiteSmall`,
whose unused coefficient-universe parameter left a max-universe equation unsolved.
A diagnostic instance trace identified that exact candidate. The statement module
excludes that candidate from inference and uses the already available standard
site-smallness construction. This changes no site or coefficient universe.


## Repair of returned H2

The immutable returned head was b5bf19f23591. The current shared item has no Lean binding;
its accepted statement, proof and original dependency fields were compared with the retained
sandbox. The sole mandatory returned point is repaired by three new definition nodes and three
modules. The item publicly imports those modules and uses their transparent aliases; its
`stmt_deps` is exactly the current base list plus these three definition nodes. The three
theorem nodes identified by H2 are removed from `stmt_deps`. All other existing-node fields
are preserved except `lean`. No mathematical hypothesis or clause is changed by this repair.
The advisory about further pinning `field` and `field'` is not a required H2 repair; their
reviewed signatures and the geometric scalar `sections` and `transport` equations are retained.

## New nodes

`def-sfb-field-action-internal-pure-tensor` owns
`Sheaf.AlgebraicGeometry.FieldActionInternalPureTensor.fieldActionInternalPureTensor`
(in the namespace `AlgebraicGeometry.ProEtale.FieldActionTransport`). This is the local
pairing for internal relative tensor on an arbitrary small-enough site: the lax comparison
for the inclusion of abelian sheaves into presheaves, followed by the coequalizer projection.
Its explicit universes and assumptions are `C : Type v`, `Category.{w} C`,
`UnivLE.{max v w, u}`, `HasSheafify J AddCommGrpCat.{u}`, and monoidal local equivalences,
then the commutative ring object, its two modules, a test object and two sections. Its body
is exactly the recorded generic `comparison_internalTmul`; no pairing is duplicated and no
proof of the tensor-comparison theorem is used. Source: Stacks 03EK, section-tensor-product.
LeanSearch returned sheaf-module constructors and section APIs, LeanFinder returned
sheafification scalar constructions and a presheaf tensor, Loogle returned an unknown
project identifier and zero hits, and Mathlib grep returned zero hits. DAG and project
searches found the generic pairing only in the tensor-comparison theorem's module; the
existing `internalPureTensor` definition node fixes ProEt and cannot serve coherent Profinite.
The blueprint search `pure tensor` found five unrelated nodes, no owner of this pairing.
Empty test objects and zero modules require no special nonemptiness assumption; the same
formula handles both sites without equating their object and morphism universes.

`def-sfb-field-action-topos-normalization` owns
`AlgebraicGeometry.ProEtale.FieldActionTransport.FieldActionToposNormalization` in
`Sheaf.AlgebraicGeometry.FieldActionToposNormalization`. It transparently re-exports the
existing `FieldActionTopos.Normalization` type, not the theorem asserting its inhabitation.
The new node spells out the exact original datum: dense free-subsite coordinates, canonical
geometric Galois labels, section restrictions and covering tests, point and invariants
adjunctions, universal fixed-section inclusion and cover equalizer, the mate comparison,
finite operations and coefficient naturality. Source: Bhatt--Scholze Examples 4.1.9--4.1.10,
pp. 27--28, with the inherited paragraph (3) normalization. The Lean binders are exactly
`k Ω : Type u`, fields, algebra and separable closure; the body is the existing structure
name. LeanSearch and LeanFinder found unrelated action/module forgetful APIs; Loogle found
generic sheaf equivalences; Mathlib grep returned zero hits. Searches of the DAG and both
project trees found no definition node owning this complete datum, only its theorem module.
The whole-blueprint search `normalized field` returned zero matches. No existence theorem
is used to choose an inhabitant; trivial Galois groups and all finite arities, including zero,
remain covered by the unchanged underlying structure.

`def-sfb-geometric-section-functors` owns the three aliases in
`Sheaf.AlgebraicGeometry.GeometricSectionFunctors`: `fieldActionFieldSets`,
`fieldActionActionSets` and `fieldActionActionUnderlying`, in the same field-transport
namespace. The first forgets the field module and abelian group structures; the second
forgets action, module and abelian group structures and transports to the small profinite
site; the third forgets the set-sheaf action. Each body is precisely the corresponding
existing definition in `GeometricSectionsAdjunction`. Source: Stacks 00YV and the
Bhatt--Scholze Example 4.1.10 presentation. The field functor takes only `k` and `R`;
the action functors also take the specified separable closure, as their actual categories
require. No action-abelian hypothesis is introduced. The same LeanSearch/LeanFinder,
Loogle and Mathlib grep searches as for the normalized field interface found general
forgetful APIs but no exact field/action interface. DAG and project searches locate these
definitions only inside the geometric-section theorem module; the definition node now
owns them without importing a theorem conclusion into the statement dependency graph.
Zero coefficients, the trivial group and empty profinite tests are retained.

Second reading of the H2 repair: compared each new node with its alias body and the full
original declaration. All alias bodies are definitionally the existing notion. In the item,
the pure-tensor equations still use the identical internal pairing on both sites; `h` is
the identical normalization datum; `over` and `over'` use the identical three functors.
The new generic pairing keeps independent site universes and explicit instance binders.
All four delivered files passed the prescribed server `scompile.py` command, with no
errors or warnings other than the permitted postponed item theorem. The repair adds no
new postponed theorem and changes no accepted mathematical statement.
