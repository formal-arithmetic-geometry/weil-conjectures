## Worker report

`Sheaf.Paper.PbcQbarCategory` defines
`AlgebraicGeometry.Scheme.pbcQbarCategory` as an abbreviation of the published
`AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory`. It constructs the Qbar
scalar action on precisely its quotient Hom sets. The category retains the
published common-stage shifts and the common-stage cone distinguished triangles.
No Karoubi envelope is applied. All theorem proofs in this delivery are `sorry`;
all definitions have real data, or select structures uniquely determined by
explicit normalization equations.

The blueprint definition, its source note, the common-stage cone definition, and
the Verdier-axiom proof were read in the literature mirror. The node statements
are unchanged. The older sandbox's large prerequisite replacement is archived
under scratchpad and is excluded from this delivery. Since that attempt, the
concrete rational coefficient stages, normalized tensor transitions, pair category,
and common-stage shifts have landed. Generic common-stage cone and Verdier
interfaces also landed during this audit; this delivery reuses them.

| Source hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]`. |
| Q_l | Mathlib `ℚ_[l]` (`Padic l`). |
| Fixed algebraic closure | `Qbar : Type w`, `[Field Qbar]`, `[Algebra ℚ_[l] Qbar]`, `[IsAlgClosure ℚ_[l] Qbar]`. |
| Scheme T | `T : Scheme.{u}`, with `u` independent of `w`. |
| Noetherian | `[IsNoetherian T]`. |
| Finite dimension | `[hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]`. |
| Ell invertible | `[hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`. A global section is a unit iff its germs are units; this is the published pair-category interface. |
| Finite stages | `Padic.FiniteCoefficientFields l Qbar`; its subtype property is finite dimension over Q_l, not finite cardinality. |
| Integral and rational stage categories | `pbcStageCategory l Qbar T E` is the recorded `PbcRationalCategory` at `pbcStageDatum` and its uniformizer, whose integral full subcategory is the published complete, uniformly constructible category with compatible etale origins. |
| Canonical tensor transitions and associators | Published `pbcScalarSystem`, whose `T` is `pbcScalarExtension` and `assoc` is `pbcScalarAssociator`; these are normalized integral-derived tensor followed by raw rationalization. |
| Pair objects | `PbcFiniteStagePairCategory` is the upstream `StageSystem.PairCategory`; its fields are `stage` and `obj`. |
| Morphisms [M,u] | The same upstream `PairCategory.Rep` and quotient are used, with their recorded source and target stage inclusions. |
| Transport u_N | The existing `StageSystem.tr` conjugates `T.map u` by the source inverse associator and target associator. |
| A finite field containing alpha | `qbarScalarField` is literally the simple intermediate field `IntermediateField.adjoin ℚ_[l] {α}`, with the named finiteness theorem retaining `[IsAlgClosure]`. |
| Common N containing M and Q_l(alpha) | `qbarScalarRep` uses the actual finite compositum of the representative stage and the scalar field. |
| alpha [M,u] = [N,alpha u_N] | `qbarScalarRep` multiplies the actual transported arrow by the element of `N.val`. `qbarScalarRep_rel` supplies its quotient compatibility; `qbarScalarHom` is `Quotient.map` of that operation. |
| Any permitted N, including N=M | `qbarScalarHom_mkHom` states the displayed formula for every overfield `N`, inclusion `hMN`, and membership proof `hα`. |
| The finite-stage E action on rational Homs | `qbarStageFieldEquiv` is the unique ring equivalence from the actual uniformizer localization to `E.val` fixing all lifted integral elements. `qbarStageLinear` restricts the existing localization scalar action along its inverse. |
| The Qbar scalar action | `qbarPairLinear.homModule.smul` is exactly `qbarScalarHom`; `pbcQbarLinear` specializes this to `pbcScalarSystem`, and `pbcQbarScalarAction` exposes it as an operation. |
| Underlying category is P_T | `pbcQbarCategory` abbreviates the recorded `PbcFiniteStagePairCategory`, with unchanged objects and Hom classes. |
| Shift | The existing `CommonStageCalculus.pbcPairHasShift` is reused. It sends `(E,K)` to `(E,K[n])` and conjugates representative arrows by the prescribed tensor shift comparisons. |
| Distinguished triangles | `pbcCommonStageDistinguished` specializes the recorded `StageSystem.CommonStageDistinguished`, equivalently the isomorphism closure of its recorded `commonStageCone` triangles. |
| Ordinary triangulated category | `pbcQbarTriangulated` uses the separately stated `pbcVerdierAxioms` for that exact distinguished set. |
| No Karoubi envelope; later completeness property | There is no `Karoubi` in the underlying category definition. Idempotent completeness and the later envelope equivalence are not imposed as data or hypotheses here. |

`Fact` packages only the two existing scheme hypotheses so the finite-stage
triangulation instances can infer them. It adds no mathematical assumption.
The coefficient field's size is transported through the published `pbcFiniteField`
(Shrink) equivalence and its existing ULift integer ring; no equality of site,
coefficient-field, object, or morphism universes is imposed.

Dependency declarations used:

- `Sheaf.Paper.FiniteStagePairCategory`: `pbcStageCategory`, `pbcStageLocalization`,
  `pbcScalarExtension`, `pbcScalarAssociator`, `pbcScalarSystem`,
  `PbcFiniteStagePairCategory`, and the canonical `pairPreadditive` instance.
- `Sheaf.Paper.PbcFiniteCompletedCoefficientMap`: `pbcFiniteField`,
  `pbcStageDatum`, `pbcStageUniformizer`, and the actual completed coefficient maps.
- `Sheaf.Paper.CommonStageCalculus`: the normalized stage shifts, scalar-extension
  `CommShift`, associator compatibility, `pbcPairHasShift`, stage-inclusion shift
  comparisons, finite biproducts and common-stage equality interfaces.
- `WeilConjectures.CategoryTheory.StageSystem.Basic` and `.Functor`: the existing
  representative quotient, transport, inclusions and stage identifications.
- `Sheaf.Paper.PbcRationalCategory`: actual raw scalar localization and its
  constant-section integral linearity; `Sheaf.CategoryTheory.ScalarLocalization`
  supplies its tensor-Hom scalar action.
- `Sheaf.Paper.IntegralTStructure`: the published
  `pbcIntegralProperty_isTriangulated` on exactly the actual integral category.
  Its inherited triangles are the input to the missing rational triangle interface.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`:
  `exists_triangulated_scalarLocalization`, including its normalized shift and
  integral-image characterization.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: finite intermediate fields,
  compositum, base stage, and `finiteCoefficientFields_properties`.
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`:
  `coefficientExtension_localization_uniformizer`.
- Mathlib `Padic`, `IsAlgClosure`, `IntermediateField.adjoin`, `Linear`,
  `Pretriangulated.Triangle`, `Pretriangulated`, and `IsTriangulated`.
  Mathlib's `Idempotents.Karoubi` and `toKaroubi` were inspected for the exclusion
  clause; the category is not replaced by either construction.

The canonical scalar-extension *data* required here are already in the published
pair-category and common-stage modules, even though the full independent property
node `prop-weil-pbc-scalar-extension` has not yet acquired a Lean record. The
consumer uses those actual canonical declarations rather than defining a second
scalar-extension system or introducing arbitrary transitions. No missing scalar
construction or missing prerequisite is left as a hypothesis.

Edge cases checked: alpha zero or one; zero morphisms; alpha already in M, so N=M
is permitted; an arbitrary larger N; equal endpoint fields; identity scalar
extensions and repeated associator indices; distinct endpoint fields; positive,
zero and negative shifts; zero complexes; the empty finite diagram (base field
exists), and the empty scheme. Finite-dimensionality includes Krull dimension
minus infinity. The stalk invertibility condition is vacuous on the empty scheme,
as is equivalent to invertibility of the section in its zero global-section ring.
No perfection, unramifiedness, or nonempty-scheme hypothesis is added.

Searches were rerun with `msearch.py` and recorded in `searches.jsonl`:

- LeanSearch, "Bounded constructible algebraic closure l adic coefficients finite
  stage pair category scalar multiplication": eight hits, including `PadicAlgCl`,
  scalar tower and adic-completion actions; none is this varying-field category.
- LeanFinder, "bounded constructible Qbar l coefficient category common finite
  stage scalar multiplication": eight generic constructibility, localization,
  adic-completion and linear-quotient hits; no exact match.
- Loogle, `CategoryTheory.Linear, CategoryTheory.Quotient`: six generic linear
  quotient constructions. They assume a fixed scalar ring already acting on the
  original category; they do not construct this varying-field action.
- Mathlib CategoryTheory grep,
  `Qbar|finite.stage.pair|common.stage.cone|PadicAlgCl`: two unrelated `qbar`
  variables in Pseudoelements.
- Direct `rg` in upstream `WeilConjectures` and shared `lean/Sheaf` for
  `pbcQbarCategory|qbarScalarHom|Qbar.*Category|def-weil-pbc-qbar-category`:
  no existing implementation of this definition; PointFdQbarCategory is a
  different category used for a pointwise comparison.
- The newer upstream `StageSystem.Basic` and `.Functor` were inspected and their
  actual generic quotient reused. `scompile.py --source` confirms the published
  `CommonStageCalculus`; it reports `PbcCommonStageCones` unavailable. A read-only
  server delivery-ref check found no cones, Verdier, or scalar-extension delivery.

The possible overlap `def-weil-algebraically-closed-coefficients` was also
opened, together with `AlgebraicallyClosedCoefficients.Stage`,
`algebraicallyClosedConstructibleCategory`, and `rationalConstructibleCategory`.
That module fixes a `FiniteFieldDatum`, assumes `l ≠ D.p`, and uses
`boundedConstructibleDerivedCompleteIntegralCategory` under
`def-weil-rationalization-karoubi`. This node instead requires the published
`PbcBoundedConstructibleComplete` category with its compatible uniform reduction
tower and etale-origin conditions, on an arbitrary noetherian finite-dimensional
scheme with l invertible. The categories are not interchangeable by definition,
and that alternate module does not construct the requested Qbar Hom action.
The generic StageSystem category, cones and Verdier theorem common to both are
reused directly.

There is no new DAG node, no statement correction, and no disputed statement.

## Dependency modules

`def-weil-pbc-finite-stage-pair-category`: the record now points to the upstream
generic `StageSystem.PairCategory`, which needs a coefficient family and its
scalar-extension system as inputs. The published
`Sheaf.Paper.FiniteStagePairCategory` already supplies exactly the concrete
`AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory` required by this node.
The dependency record is repaired with `existing: true` and an explanatory note.
No module is written and neither the category nor the stage system is duplicated.

`def-weil-pbc-common-stage-cones`: the recorded generic
`Sheaf.CategoryTheory.StageSystemCommonStageCones` provides `commonStageCone`
and `CommonStageDistinguished`, and both are reused. It requires the actual
finite stages' triangulations and the induced pair shift; these concrete
triangulation instances were absent. `Sheaf.Paper.PbcCommonStageCones` supplies
the specialization with the published normalized stage shift. Its rational
triangle structure is uniquely characterized by isomorphic integral images.
The existing integral full subcategory inherits exactly its ambient triangles;
scalar localization and the unique shift normalization identify the image
criterion. The module then abbreviates the recorded distinguished predicate on
the actual `PbcFiniteStagePairCategory`. No cone or distinguishedness definition
is copied.

For the clause-by-clause cone check, the recorded `commonStageCone` takes
`X`, `Y`, `M`, `hX`, `hY`, `Z`, `u`, `i` and `p`. Its cone is literally `(M,Z)`.
Its first arrow is `mkHom M hX hY u`. Its second is the canonical identification
of Y with its M-stage image followed by the included stage arrow i. Its third is
the included p followed by the stage-inclusion shift comparison and the inverse
shifted identification of X. The literal-identity tensor normalization makes
these the source's `[M,i]` and `[M,sigma.inv ≫ p]` representatives, in diagrammatic
composition order. `CommonStageDistinguished` is the triangle-isomorphism closure
of included finite-stage distinguished triangles. Moving the first two objects
to their common stage by `isoToStage` identifies this with the common-stage cone
criterion. No cone object is selected from mere existence.

`thm-weil-pbc-verdier-axioms`: the recorded generic
`Sheaf.CategoryTheory.StageSystemVerdier.commonStage_verdier_existsUnique`
is reused, including its exact finite-stage inclusions and uniqueness of the
specified distinguished set. Its assumptions include concrete exact finite-stage
structures, additivity of stage inclusions, and shift compatibility of transition
identifications, which were not yet provided on these actual coefficient stages.
`Sheaf.Paper.PbcVerdierAxioms` supplies those named proof obligations and the
concrete specialization. `qbarStageInclusionAdditive` is exactly additivity of
`S.ι E` for the recorded Hom group laws. `qbarTransIsoCommShift` states the actual
shift equation for `S.transIso h`, with the induced stagewise shift.
`qbarPairPretriangulated` selects the unique structure characterized by the
recorded `CommonStageDistinguished` predicate; it does not choose an unspecified
triangle set. `qbarStageTriangulated` states TR4 for the already normalized rational
triangles; `qbarScalarExtensionExact` states exactness for the already specified
tensor functor and shift comparison.

`pbcVerdierAxioms` states Mathlib TR4 on that exact pretriangulation, exactness
of every `S.ι E`, and `NatTrans.CommShift (S.transIso h).hom ℤ` for every coefficient
inclusion. Mathlib `Pretriangulated` incorporates TR1 (isomorphism closure,
identity triangles, and cones), TR2 (signed rotation iff), and TR3 (completing a
commutative square with both third-arrow equations). `IsTriangulated` supplies
TR4, with its commuting octahedral faces and remaining distinguished triangle.
The generic theorem's docstring supplies the full finite-stage argument;
the specialization's docstring records that argument explicitly. Every stage,
shift, associator and distinguished set is fixed by the actual coefficient
construction. The concrete theorem has exactly the source's prime, algebraic
closure and scheme hypotheses.

The dependency copies change only their `lean` records, with notes explaining
the missing specialization. No new DAG nodes or statement changes are made.

## Second reading by NN

I reread the node statement against the blueprint paragraph and the cited Stacks
places (Tags 09BS, 09BT, 09C1, and 09C7). The item-by-item rendering is:

| Node item | Lean rendering | Verdict |
|---|---|---|
| prime `ell` and `Q_l` | `l : ℕ`, `[Fact l.Prime]`, and Mathlib `ℚ_[l]` | exact |
| fixed algebraic closure `Qbar` of `Q_l` | `Qbar : Type w`, `[Field Qbar]`, `[Algebra ℚ_[l] Qbar]`, `[IsAlgClosure ℚ_[l] Qbar]` | exact; no universe identification is imposed |
| scheme `T`, noetherian, finite-dimensional, `ell` invertible | `T : Scheme.{u}`, `[IsNoetherian T]`, `hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))`, and `hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))` | exact published scheme hypotheses, packaged as `Fact` for inference |
| finite stages | `Padic.FiniteCoefficientFields l Qbar`, namely finite-dimensional intermediate fields, with compositum and base stage from the recorded dependency | exact; “finite” is dimension, not cardinality |
| rational stage category | `pbcStageCategory l Qbar T E`, the recorded `PbcRationalCategory` at `pbcStageDatum` and its uniformizer | exact dependency specialization |
| scalar-extension functors and normalized associators | `pbcScalarSystem`, with `pbcScalarExtension` and `pbcScalarAssociator` | exact canonical system; no duplicate transitions |
| pair objects and common-stage morphisms | `PbcFiniteStagePairCategory`, `StageSystem.PairCategory`, `PairCategory.Rep`, `mkHom`, and `StageSystem.tr` | exact; the quotient and transport are inherited |
| scalar formula `alpha [M,u] = [N, alpha u_N]` | `qbarScalarRep`, `qbarScalarHom`, and `qbarScalarHom_mkHom` | exact, including arbitrary permitted `N` and the equal-stage case |
| well-definedness and Qbar-linear action | `qbarScalarRep_rel`, `qbarScalarHom_laws`, `qbarPairLinear`, and `pbcQbarScalarAction` | exact; proofs are postponed named statements, while data is canonical |
| underlying category `P_T` | `abbrev pbcQbarCategory := PbcFiniteStagePairCategory ...` | exact; objects and Hom classes are unchanged |
| shift and common-stage cone triangles | `pbcCommonStageDistinguished` from the recorded common-stage construction and the normalized shift supplied by `PbcCommonStageCones` | exact; no cone is chosen from bare existence |
| Verdier axioms and ordinary triangulation | `pbcVerdierAxioms` and instance `pbcQbarTriangulated` | exact; it uses the specified distinguished predicate |
| no Karoubi envelope in this definition | the underlying abbreviation is the pair category itself and contains no `Karoubi`/`toKaroubi` construction | exact |

The Stacks source entries define fixed-coefficient constructible/adically lisse
sheaves and the fixed-coefficient suitable derived category; they do not define
the finite-stage Qbar colimit. Thus the blueprint’s added pair category and scalar
action are correctly supplied by the Lean dependencies.

Edge cases checked: `alpha = 0` and `alpha = 1`; zero representatives and zero
composition; `alpha` already in the representative stage (so `N = M` is allowed);
an arbitrary larger common stage; equal and distinct endpoint stages; identity
scalar extensions and repeated associator indices; positive, zero, and negative
shifts; zero complexes; the base field witnessing nonemptiness of the finite-stage
index (including an empty diagram); and the empty scheme. No assumption of a
nonempty scheme, perfection, unramifiedness, or positive dimension is introduced.
The stalk formulation of invertibility is the published local form and is vacuous
on the empty scheme, as required.

I searched Mathlib and both project source trees with the recorded LeanSearch,
LeanFinder, Loogle, and `rg` queries (including `qbar`, `Qbar`, finite-stage pair,
common-stage cone, and `PadicAlgCl`). The only nearby project declaration is
`PointFdQbarCategory`, which is a different pointwise category. No exact existing
Qbar finite-stage category or scalar-action declaration exists, so the item remains
new. The exact canonical pair-category, finite-stage, common-stage, rational-stage,
and Verdier declarations were opened and reused; no private duplicate notion was
introduced.

No statement mismatch was found. The worker’s Lean files were not changed. The
only dependency records supplied are the already reviewed concrete specializations
of the generic pair-category, common-stage-cone, and Verdier interfaces; their
statements remain the dependency-node statements and their `lean` notes explain
why those specializations are needed.
