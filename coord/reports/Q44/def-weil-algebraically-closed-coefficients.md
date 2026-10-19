## Worker report

This repairs the N7 arbitrary-base-field interface in the owning node only.
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` imports and preserves the
published intrinsic finite-field and legacy interfaces. The principal declaration
`WeilConjectures.generalAlgebraicallyClosedConstructibleCategory l Ω Y` has no
FiniteFieldDatum, characteristic, structure-map, finite-type or Noetherian binder.
Scheme universe u and algebraic-closure universe v are independent.

The current source is main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
order 1821 (formerly master order 1462). It fixes a global datum but imposes no
structure morphism from Y to that datum. The reusable general construction and
its canonical specialization therefore preserve the informal statement. No
statement correction, new node or dependency-owner repair is submitted.

Clause-by-clause correspondence:

* Prime l is `[Fact l.Prime]`; `Padic l` is Q_l; `[Field Ω]`,
  `[Algebra (Padic l) Ω]`, `[IsAlgClosure (Padic l) Ω]` specify any chosen closure.
  `specialization D l hl Ω Y` reinstates exactly the source global datum and l ≠ D.p.
* `Index l Ω`, `Coefficient.{u} l Ω E`, and `coefficientInclusion` reuse the published
  finite intermediate fields, their canonical small models, and transported inclusions.
  Composita give `Common A B` a nonempty directed index, including repeated fields.
* `Stage l Ω Y E` is precisely `sfRationalConstructibleCategory` for that model,
  with the published category, preadditive, zero, integer-shift, pretriangulated and
  triangulated structures. No withdrawn integral predicate is used as a stage.
* `transition` is the actual `sfRationalScalarExtension` at p = 0. Reading
  `sfConstructibleIntegralScalarExtension` shows p/hl occur only in its membership
  proof; its underlying tensor objects/maps do not depend on them. Primality gives
  l ≠ 0, without assuming any characteristic for Y. The rational functor is fixed
  by its exists-unique tensor specification. `integralTransition` is that existing
  completed integral restriction, not a replacement scalar construction.
* `integralScalarCommShift_existsUnique` fixes the shift comparison by the
  ordinary balanced tensor shift through `sfIntegralOrdinaryComparison`.
  `transitionCommShift_existsUnique` fixes its rational localization; `transitionExact`
  states exactness for this comparison. `associator` and `unitor` are the published
  normalized `sfRationalScalarComp` and `sfRationalScalarUnit`, transported along
  the coefficient-inclusion laws. `associator_cocycle` states the tensor pentagon.
* `stageSystem_existsUnique` fixes every StageSystem data field to those actual
  transitions and associators. `Pair` is the existing `StageSystem.PairCategory`,
  whose objects literally have fields `.stage` and `.obj`, with its quotient Hom,
  identity and common-stage composition. It is not merely a sigma carrier.
* `StageHom`, `transport` and `transportHom` render the displayed Hom system.
  Transport is inverse source associator, scalar image of the map, target associator.
  `transportSystem` supplies identity and composition. `ColimitHom` is Mathlib's
  `AddCommGroup.DirectLimit`; `homCoordinates_existsUnique` fixes the equivalence
  of actual quotient Homs with it on every finite representative. Hom addition is
  transported along that equivalence; `composition_bilinear` supplies preadditivity.
* `ofHom` is the existing quotient constructor. `representatives` states existence
  and equality precisely after one common enlargement. Generic PairCategory
  composition is the composite of the transported finite-stage maps.
* `shiftPair n A` is literally `(A.stage, A.obj[n])`. `shiftRepresentative` conjugates
  shifted maps by the specified scalar shift comparisons. `shift_existsUnique`
  specifies objects, every representative, and coherent identity-normalized stage
  inclusion comparisons, determining the full HasShift structure.
* `Distinguished` is the existing `CommonStageDistinguished` predicate for this
  system. The recorded generic `commonStage_verdier_existsUnique` supplies the
  pretriangulation, Verdier axioms and exact stage inclusions. `distinguished_iff`
  exposes its criterion. `commonStage_cone` uses the full recorded cone with second
  and connecting arrows and literal cone pair `(L,C)`.
* The principal abbreviation is exactly `Pair`. No Karoubi completion, idempotent
  data, quotient of objects or additional objects is introduced. Objects already
  have a finite coefficient field; arrows have representatives and distinguished
  triangles are isomorphic to a distinguished finite-stage image.

Canonical finite-field specialization:

* `specialization_transition`, `specialization_comparisons`, and
  `specialization_transitionShift` identify the actual normalized scalar functors,
  associators/units, and coherent shift comparisons, independently of proof parameters.
* `specialization_stageSystem` identifies the complete normalized systems.
  `specialization` is the existing `Pi.eqToEquivalence` along that equality.
* `specialization_pairs` fixes literal pairs and every represented arrow;
  `specialization_transport` intertwines the conjugated Hom transition maps;
  `specialization_homCoordinates` identifies their canonical directed-colimit
  coordinates. `specialization_additive` uses those prescribed group structures.
* `specialization_commShift_existsUnique` fixes identity components on shifted
  pairs and their coherent comparison; `specialization_distinguished` preserves
  and reflects distinguished triangles and `specialization_exact` states exactness.

Dependency declarations read and reused:

* `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, for specialization only.
* Mathlib PadicNumbers, PadicIntegers, IsAlgClosed.Basic/AlgebraicClosure:
  `Padic`, `PadicInt`, `IsAlgClosure`, `AlgebraicClosure`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public imports:
  coefficient valuation rings, chosen uniformizers, finite quotients.
* `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  `finiteCoefficientCompositum`, `finiteCoefficientBase`, properties theorem.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, its
  named structure instances, localization, normalized scalar extension and additivity.
* `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`:
  `sfConstructibleIntegralScalarExtension`, explicit lift and preservation theorem.
* `Sheaf.Paper.ScalarExtensionExactIntrinsic`:
  `sfScalarExtension_exact_triangulated`; its K-flat/Roos proof confirms that
  no finite-field geometry enters the normalized exactness argument.
* `Sheaf.Paper.SfScalarExtensionComposition`: `sfIntegralOrdinaryComparison`,
  `sfIntegralScalarComp`, `sfIntegralScalarUnit`, `sfRationalScalarComp`,
  `sfRationalScalarUnit`, `sfRationalScalar_coherence`, with their unique normalizations.
* `Sheaf.Paper.AlgebraicallyClosedCoefficients`: only its datum-free coefficient
  Index, Coefficient, inclusion maps/laws and directed/nonempty instances.
* `WeilConjectures.CategoryTheory.StageSystem.Basic`: `StageSystem`, `PairCategory`,
  `mkHom`, `ι`, `transIso`, `isoToStage`, quotient representatives and composition.
* The recorded PBC modules `FiniteStagePairCategory`, `PbcCommonStageCones`,
  `PbcVerdierAxioms` were read. Their concrete categories require different
  geometric hypotheses; the general construction reuses their common generic
  machinery, `Sheaf.CategoryTheory.StageSystemCommonStageCones` and `StageSystemVerdier`,
  rather than incorrectly imposing those hypotheses on Y.
* Mathlib `AddCommGroup.DirectLimit`, `Equiv.addCommGroup`, `Pretriangulated`,
  `IsTriangulated`, `Idempotents.Karoubi` (checked absent from the construction),
  and `CategoryTheory.Pi.eqToEquivalence`.

Edge cases checked: characteristic-zero and infinite geometric base fields add
no restriction; arbitrary closure universe is shrunk only at finite stages;
the empty scheme retains the bottom coefficient stage; zero objects and their
zero Hom groups are included; identity inclusions and repeated coefficient
stages use the normalized scalar units and associator cocycle. No auxiliary
FiniteFieldDatum is manufactured.

Searches (also recorded by msearch.py in searches.jsonl):

* LeanFinder: “triangulated common stage category finite coefficient field pairs
  directed colimit Hom scalar extension arbitrary schemes” returned eight scheme
  colimit results, no matching coefficient construction.
* LeanSearch: “triangulated category finite coefficient fields directed colimit
  Hom scalar extension” returned eight module/ring direct-limit results, no match.
* Loogle: `CategoryTheory.Pi.eqToEquivalence` returned its exact existing signature,
  which is reused. Mathlib CategoryTheory grep
  `PairCategory|CommonStageDistinguished|sfRationalScalarExtension` returned no hits.
* rg in upstream WeilConjectures and shared lean/Sheaf for
  `generalAlgebraicallyClosed|GeneralAlgebraicallyClosedCoefficients|sfRationalScalarExtension.*(indep|eq)`
  returned no matching general interface. Upstream node-id search found a direct
  adic constructible-sheaf model and a Weil-sheaf model, not the source's finite
  pairs and raw rational Hom-colimit construction. Their source was inspected.
* `scompile.py --source Sheaf.Paper.SfAlgebraicallyClosedCoefficients` retrieves
  the current published finite-field interface retained by import.

No statement dispute. No new definition node or dependency-owner module.

## Repair changes

The previous sandbox contained split owning-node modules and three transitive
import patches belonging to other owners. These are archived outside lean/ and
dag/ in scratchpad/earlier-delivery; they are not part of the delivery. The full
general construction and specialization are consolidated into one owning module.
Only lean differs between the refreshed node copy and current shared base, with
the UTC date. Stage and StageHom use ordinary definitions with the published stage instances.
The integral shift normalization is stated once over ordinary coefficient fields
and then specialized to the small models. `scalarAssociator` constructs the actual
normalized comparison over ordinary fields; `associator_existsUnique` fixes its
size-transported counterpart by HEq of the entire specified isomorphism. Typed
finite-field pair arguments prevent inference from unfolding rational Hom tensors.
These changes address the observed timeout without splitting the owning module
or raising the 60-second limit. No profiler or heartbeat option is delivered.

The minimal required rational-stage import now compiles successfully through the
prescribed wrapper; the historical duplicate declaration is no longer reproduced.
Current compilation, consumer probe and dry-run results are recorded below.

The independent second reading remains for the separate worker requested by the
dispatcher; this worker does not supply a second-reading section.


## Validation

The updated owner and scratchpad/ConsumerValidation.lean compile successfully through
the prescribed scompile.py wrapper with the normal 60-second per-file limit.
Evidence: scratchpad/parameter-repair-compile.log. The owner took 21.2 seconds
in the preliminary check, 17.6 seconds in the sandbox check and 17.9 seconds in
the library check. The consumer took 2.8 and 2.6 seconds. There are no errors
or warnings other than the permitted postponed proofs.

The consumer explicitly binds an arbitrary field K0, l invertible in K0, schemes
X/Y over K0, independent closure universe v, and the downstream rational compact-support
functor RfBang at a finite coefficient stage. It forms the literal output
`⟨E, RfBang.obj K_E⟩ : generalAlgebraicallyClosedConstructibleCategory l Ω Y`.
RfBang is supplied by the downstream owning construction: this probe checks the
output interface without restating that node. Category, Preadditive, HasZeroObject,
HasShift by ℤ, additive shifts, Pretriangulated and IsTriangulated all synthesize.
The specialization, normalized transition shift and distinguished-triangle criterion
also elaborate.

The owner has 32 explicitly named sorry theorems with source, blueprint and proof-plan
docstrings. All 80 declarations are recorded in lean.declarations. Definitions use
actual data or specifications that uniquely determine their chosen data.

## Current repair verification

In addition to retaining the general category and its canonical specialization, the
module now states `scalarExtension_parameter_independent`. It identifies the actual
completed integral functors and normalized rational functors for any two allowed
p/hl parameters, over ordinary finite coefficient fields and arbitrary schemes,
without a datum binder. Its proof plan reduces integral equality to proof irrelevance
of the restricted objects, then applies the published rational tensor specification's
uniqueness. This makes the justification for p=0 an explicit reusable statement
rather than only prose in the specialization proof plan. It is an owning construction
helper, not a restatement of the scalar-extension dependency node. Only lean differs
from the current shared node; its statement and dependency lists are unchanged.

The current base imports no longer reproduce the historical duplicate-declaration
failure. No transitive dependency module or node is delivered. The old independent
review concerned the earlier retained file and is removed: the separate second reader
must review this changed module afresh. This worker does not provide a second reading.

Repeated searches in this repair: LeanFinder query “common stage coefficient category
finite extensions directed colimit morphisms rational scalar extension” returned eight
intermediate-field/Galois/ring-colimit results, no matching construction. Loogle again
confirmed the reused Pi.eqToEquivalence. Mathlib CategoryTheory grep for
PairCategory|CommonStageDistinguished|sfRationalScalarExtension returned zero hits.
Project and upstream rg found no parameter-independence theorem for either intrinsic
scalar functor.

The final check is deliver2.py Q44 def-weil-algebraically-closed-coefficients --no-push,
with current modules and records. Its log is scratchpad/parameter-repair-dry-run.log.
The separate second reader supplies the review and delivers; this worker pushes nothing.

## Second reading by Q44

I independently read the unchanged DAG statement, all 915 lines of the delivered
module, the released stage-2 N7 repair note, and the cited blueprint source at
master order 1462 and main-20261015 order 1821. This node's source is a blueprint
Markdown definition, not a Stacks tag. I also read its unit's ambient-typing
statement and the finite-stage/common-stage portion of the slopmaster2 note
42_qbarl_triangulated_colimit.tex. The latter takes a subsequent Karoubi envelope
and has different finite-stage hypotheses; neither is imported into the meaning
of the present blueprint definition, which explicitly takes no such envelope.

My checklist of the source's objects, hypotheses and clauses, with their Lean
counterparts and verdicts, is as follows. Names below without a namespace are in
WeilConjectures.GeneralAlgebraicallyClosedCoefficients.

| Source item | Lean rendering and verdict |
| --- | --- |
| Fixed global datum (p,a,q,k0,k), prime l distinct from p | The preserved SfAlgebraicallyClosedCoefficients interface takes FiniteFieldDatum D and hl : l != D.p. The new specialization takes exactly these binders. The N7-required general interface omits unused global data and specializes canonically to every allowed D. Pass: no auxiliary datum is chosen and no source case is lost. |
| Q_l and an arbitrary chosen algebraic closure | Padic l, Fact l.Prime, Field Ω, Algebra (Padic l) Ω and IsAlgClosure (Padic l) Ω. Pass: Ω is not restricted to the particular type AlgebraicClosure (Padic l). |
| An arbitrary scheme Y | Y : AlgebraicGeometry.Scheme.{u}. Pass: there is no structure map to D.k, finite-type, Noetherian, dimension, or invertibility hypothesis on Y. |
| Finite coefficient fields inside Ω, ordered by inclusion | The reused Index is Padic.FiniteCoefficientFields, the subtype of IntermediateField with FiniteDimensional over Padic l. Pass: finiteness means extension degree, not cardinality. |
| Base coefficient field and common upper fields | finiteCoefficientBase, finiteCoefficientCompositum, and the reused indexDirected/indexNonempty; Common, commonNonempty and commonDirected retain both lower bounds. Pass: the index of each Hom is nonempty and directed. |
| The specified rational stage D^b_c(Y,E) | Stage is exactly the dependency's sfRationalConstructibleCategory on Coefficient.{u}, with its published structures. Coefficient and coefficientInclusion reuse the canonical Shrink algebra equivalences. Pass: no withdrawn integral predicate or different rational category is substituted. |
| Actual scalar extension for E contained in L | transition uses sfRationalScalarExtension with the transported inclusion. integralTransition is the published completed integral restriction. scalarExtension_parameter_independent identifies the actual integral and rational functors for any two allowed p/hl parameters. Pass: setting p to zero selects a proof parameter and imposes no characteristic on Y. |
| Exactness and canonical composition of transitions | integralScalarCommShift_existsUnique conjugates the ordinary tensor shift by sfIntegralOrdinaryComparison; transitionCommShift_existsUnique fixes its localized shift. transitionExact asserts exactness for that comparison. scalarAssociator uses sfRationalScalarComp, associator_existsUnique fixes the entire resulting comparison, unitor uses sfRationalScalarUnit, and associator_cocycle is the pentagon. Pass: comparisons are normalized tensor maps. |
| Objects are literal pairs (E,K) | stageSystem_existsUnique fixes both data fields of the upstream StageSystem (T and assoc); its only other field is a proof. Pair is that system's existing PairCategory, whose fields are stage and obj. Pass: the construction is an actual category on the prescribed pairs. |
| Displayed abelian-group Hom colimit | StageHom is precisely the Hom between the two extended objects; transport is source associator inverse, scalar map, target associator. transportHom and transportSystem give the directed group system. ColimitHom is AddCommGroup.DirectLimit. homCoordinates_existsUnique fixes the quotient-Hom equivalence on every representative, and homAddCommGroup transports that colimit's group law. Pass: both the underlying Hom and its addition are specified. |
| Representatives and equality after one further extension | ofHom is the existing PairCategory.mkHom; representatives states both existence and the iff with a common later field. Pass: the quantifiers allow different initial common fields and give equality of their transported maps. |
| Composition at a common finite field | Pair inherits upstream Rep.comp and categoryStruct: compose the two transported representatives at a common upper field. composition_bilinear equips these same compositions with the colimit addition. Pass: no separate arbitrary composition is introduced. |
| Shift (E,K)[1] = (E,K[1]) | shiftPair preserves stage; shiftRepresentative conjugates the shifted map by the specified scalar comparisons. shift_existsUnique fixes objects, all represented arrows, and identity-normalized coherent inclusion comparisons, hence the zero/addition constraints of HasShift as well. Pass: all integer shifts, including zero and negative shifts, are covered. |
| Distinguished common-stage triangles and cone pair (L,C) | Distinguished reuses CommonStageDistinguished, the triangle-isomorphism closure of distinguished finite-stage images. distinguished_iff identifies it with the actual distinguished set. commonStage_cone uses the recorded commonStageCone with u, i, p and literal third object (L,C), including its connecting-arrow shift comparison. Pass: the full triangle, rather than only its first arrow or cone carrier, is specified. |
| Verdier axioms, finite definition, no Karoubi completion | pretriangulated, isTriangulated and inclusion_exact use commonStage_verdier_existsUnique for these actual stages. The principal abbreviation is exactly Pair. Pass: every object is a finite pair, every arrow has a finite representative, and every distinguished triangle is isomorphic to a finite-stage image; no idempotent or additional object is adjoined. |

I opened the recorded dependency declarations, not just their names:
FiniteFieldDatum; Padic and IsAlgClosure; the coefficient-extension finite-ring
interface; FiniteCoefficientFields and its compositum; SfRationalizationKaroubi;
IntegralScalarExtensionConstructibleIntrinsic; ScalarExtensionExactIntrinsic;
SfScalarExtensionComposition; the legacy coefficient size transports; the
upstream StageSystem.Basic; StageSystemCommonStageCones and StageSystemVerdier.
I checked that StageSystem has exactly T, assoc and the proof cocycle, that its
Hom is the quotient by common-stage equality, and that its composition really
transports and composes representatives. I also opened the recorded concrete
FiniteStagePairCategory, PbcCommonStageCones and PbcVerdierAxioms modules: their
PBC specializations have extra geometric hypotheses and different finite stages,
so they cannot replace this construction for arbitrary Y. Their shared generic
pair/cone/Verdier declarations are already reused here. Mathlib's DirectLimit,
Pretriangulated/IsTriangulated and Pi.eqToEquivalence have the required meanings.

The canonical-specialization portion also passes. specialization_transition and
specialization_comparisons identify the normalized functors, associators and
units; specialization_transitionShift identifies the shift structures.
specialization_stageSystem identifies all system data, and specialization is
Pi.eqToEquivalence along that equality, not a chosen equivalence from mere
existence. specialization_pairs fixes literal pairs and every represented arrow;
specialization_transport identifies every Hom-system map;
specialization_homCoordinates identifies the colimit classes.
specialization_additive, specialization_commShift_existsUnique,
specialization_distinguished and specialization_exact give the prescribed group,
shift and triangle compatibilities, with preservation and reflection of triangles.

Edge cases: the coefficient index and every common-overfield index contain a
stage even when Y is empty, so an empty index is not an excluded source case.
Zero objects and zero morphisms remain included in the Hom colimit. Repeated
fields and identity inclusions use the normalized units and pentagon; shift n=0
and negative shifts are quantified in the shift specification. The source has
prime l != D.p in its finite-field specialization, while the datum-free category
places no characteristic assumption on any geometric base. Universes u and v
are independent; finite fields alone are shrunk to u, so an arbitrarily large
closure and an arbitrary scheme universe are retained. The specialization also
keeps the datum universe d independent.

Independent searches on this reading:

* LeanFinder: "algebraic coefficient category finite field of definition morphisms
  common overfield triangulated filtered colimit" returned eight ring-colimit and
  intermediate-field results, with no matching category construction.
* LeanSearch: "triangulated category algebraic closure coefficients finite
  intermediate extensions Hom colimit" returned eight general category/colimit
  results, with no matching construction.
* Loogle: AddCommGroup.DirectLimit returned the existing group-colimit definition
  and its canonical maps, representative induction and universal property; these
  are reused rather than defined again.
* rg in Mathlib CategoryTheory and Algebra/Colimit for finite coefficient fields,
  CommonStage, PairCategory and algebraically closed categories found no matching
  concrete category. Project/upstream searches for qbar/Qbar, PairCategory,
  algebraically closed constructible categories, the node id and the new helper
  names found the finite-field/legacy interfaces and the PBC/point models.
  I opened the upstream Adic.Constructible, ClosedImmersionStages and WeilSheaf.Category
  declarations: they use direct adic sheaves or Frobenius-equipped objects, not
  the prescribed rational pair category. PointFdQbar is only the point model;
  PBC uses its different integral stages. No existing general interface meets N7.

No mathematical mismatch was found in the repaired delivery, and I changed no
Lean declaration or node statement. This reading adds the independent review
and fresh validation only. The node copy differs from the shared node only in
lean; its recorded principal signature is verbatim the file's signature, all 80
declarations are recorded, all variables/universes are bound, and no line exceeds
100 characters. All 32 postponed proofs are named sorry theorems with source,
blueprint and proof-plan docstrings. Each chosen datum has a uniqueness
specification fixing its data (or the recorded universal property); definitions
contain no sorry data. No new node, dependency-owner module, statement correction
or target-unit change is present, so no correction/citer audit is applicable.

Fresh validation through the required scompile.py wrapper passed for the owner
and scratchpad/ConsumerValidation.lean. Owner checks took 19.3, 16.6, 17.0 and
19.9 seconds; the consumer checks took 2.8 and 3.0 seconds. No errors or warnings
were emitted. I inspected the consumer: with arbitrary K0, l invertible in K0,
X/Y over K0 and independent closure universe v, its value is literally
`⟨E, RfBang.obj K_E⟩` in generalAlgebraicallyClosedConstructibleCategory l Ω Y.
The finite-stage compact-support functor is a supplied downstream functor,
not an assumption used to construct the category. Category, Preadditive,
HasZeroObject, HasShift by integers, additive shift, Pretriangulated and
IsTriangulated synthesize from the delivered module with no D binder. The probe
also checks specialization, its normalized transition shift, and the
distinguished-triangle equivalence. This verifies the exact consumer interface
required by the N7 repair note.

The second-reader dry run completed successfully: deliver2.py --no-push printed
`OK (dry run): commit 3c7ab92e41 passes the preflight and compiles; nothing pushed`.
The packet contains exactly the owning module, its node's lean repair and this
report; no archived scratchpad module is delivered.

