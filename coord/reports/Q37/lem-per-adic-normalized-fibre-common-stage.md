## Worker report

The delivery states `AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_common_stage`
in `Sheaf.Paper.AdicNormalizedFibreCommonStage`. Its sole postponed proof is `by sorry`.
The two structures `CommonStageHeartExactness` and `CommonStageFibreDescent` package
this node's assertions; their data and equations are written in full. No object is
chosen from the postponed theorem. The node's mathematical statement and proof are
unchanged. Its statement dependencies gain the already landed
`def-per-adic-fibre-comparison-data`, whose actual CommonPoint and stageHeart are reused.
There are no new nodes or dependency repairs.

The source read was Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15,
PDF pp. 61--62, together with the current blueprint
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-smooth-pullback-t-exact.proof.md`.
The target node is the formal common-heart/fibre assembly needed for the first
paragraph's exactness and support pullback assertions. I read its ten proof steps,
all twenty statement dependencies and their recorded interfaces, and the two
existing fibre-data nodes used by those interfaces.

Hypotheses and objects:

| Node | Lean |
| --- | --- |
| Field k | `{k : Type u} [Field k]` |
| Prime l invertible in k | `(l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]` |
| Separated finite-type k-schemes | `X : FiniteTypeBase k`, the existing CondensedERealization.Base: `scheme`, `Over`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`. No smoothness, flatness or nonemptiness is added. |
| Algebraic closure of Q_l | `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` |
| Finite intermediate fields and inclusions | `Padic.FiniteCoefficientFields l Ω`, ordered by inclusion, with their existing small field models `pbcFiniteField.{u} l Ω A` and `pbcFiniteFieldInclusion l Ω h` |
| Integers, uniformizer, positive quotient tower, completed continuous coefficients | The recorded `pbcIntegralDatum` and `pbcUniformizer` inside `pbcStageCategory`; `Padic.coefficientExtensionIntegers`, `AdicCoefficientDatum` and `completedReductionTower` remain the existing constructions. Positive quotient index n+1 includes every n≥1. |
| Small pro-etale site and compatible etale-origin complete integral categories | Existing `Scheme.ProEt`, `ProEt.topology` and `PbcBoundedConstructibleComplete`, through the recorded rational and stage interfaces |
| Raw rational category and standard hearts | `NormalizedFibre.Heart l E (base l X)`, with the existing `ContinuousRational.localizedT`; no Karoubi envelope |
| Pair category, scalar functors, associators and common heart | `pbcScalarSystem`, `stageHeart`, `heartScalar`, `(pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory` |
| Continuous realization J | `(R : ContinuousRational.Family.{u} l)`; all finite fibres and pullbacks are those for this specified normalized realization family |
| Given normalized finite fibres, alpha and beta | `ω : Fibres (k := k) l R`, `α : NormalizedPullback l R ω`, `β : NormalizedScalar l R ω α`. The conclusion works for these supplied compatible data, rather than choosing different ones. |
| Lattice limit/fraction prescription | Inherited literally from `Fibres`: its values are the recorded `NormalizedFibre.Assertions`, including all local lattice normalization and fractional-arrow naturality. `NormalizedPullback` and `NormalizedScalar` retain the integral-limit, unit and quotient normalization and coherence. |

Conclusion, clause by clause:

| Node clause | Lean field / interpretation |
| --- | --- |
| Additive finite-dimensional common-heart fibre V_x | `CommonStageFibreDescent.point X κ x : CommonPoint ...`; its `functor`, `additive`, and `finite` are the existing declarations. The functor has values in modules with `FiniteDimensional Ω` for every object, hence precisely finite-dimensional vector spaces without a second category encoding. |
| V(E,F) is omega_E(F) tensor Ω | `CommonPoint.finite_stage A`, a natural isomorphism of the actual included finite heart with `omega_E ⋙ ModuleCat.extendScalars (stageEmbedding ... A)` |
| Arrow [M,u] is the extended omega_M(u) conjugated by beta | `scalar` fixes the finite-stage comparison on the actual `pbcScalarSystem.transIso h`, equates it with `β.scalar` extended to Ω, and fixes the balanced associator on every pure tensor. The naturality of `finite_stage M` gives the arrow formula at M; the two equations for the endpoints give exactly its beta conjugations. This applies to every u, not only integral arrows or isomorphisms. |
| Independence of enlargement and associator-conjugated representatives | The preceding normalization holds for every `h : A ≤ B` and the underlying comparison is HEq to the recorded `transIso`; all arrows are maps of a functor on the actual quotient category. Together these specify independence for every representative of the same class, with the actual transport associators. |
| Identities, composition and addition | Functor laws and `CommonPoint.additive` on the actual common heart |
| Extension to isomorphism closure and natural presentation comparisons | The domain is the entire recorded common heart. `finite_stage` is natural. For any heart presentation e, its comparison is `functor.mapIso e` followed by `finite_stage`; functoriality gives naturality and the presentation cocycle. No arbitrary inverse or additional lattice choice is introduced. |
| Inclusion preserves kernels and cokernels with their maps | `heart_exactness.inclusion_additive` and `inclusion_homology`; Mathlib's `Functor.PreservesHomology` preserves every kernel fork and cokernel cofork, including their structure arrows. |
| Cone descriptions H^-1 C(u), H^0 C(u), with cone/truncation maps | The named existing heart-triangle declarations give the kernel fork and cokernel cofork of each finite distinguished cone, with exactly these maps. The preceding preservation fields assert preservation of those very forks/coforks, so the common kernel and cokernel are their images. This is a statement of preservation of all kernel/cokernel data, not a comparison of bare objects only. No alternate shift or triangulation is supplied. |
| Images of finite heart arrows represented at that stage | `inclusion_image` supplies an isomorphism whose two equations identify both the image inclusion and the factor-through-image map. |
| Finite heart complexes represented at one stage | `finite_complex_stage` quantifies every finite index type `ι : Type w`, every `ComplexShape ι` and every common-heart complex of that shape, and supplies a finite-stage complex with an isomorphism in HomologicalComplex, hence preserving differentials. |
| Their homology and its maps represented by finite-stage objects | `inclusion_homology` is Mathlib's preservation of kernels and cokernels and hence of the full left/right homology data of every short complex. Applied at each position of the represented finite complex this supplies the canonical homology comparisons. It includes the differential-induced maps, not only equality of dimensions. |
| Finite-stage zero image becomes zero further on | `eventual_zero`, an iff on every finite-stage derived object, with an explicit stage B and inclusion h : A≤B |
| Common short exact sequence has short exact finite-stage representative | `short_exact_stage`: every ShortComplex S with S.ShortExact is isomorphic as a ShortComplex to the image of S₀ with S₀.ShortExact. Thus it retains both arrows and their zero composite. A compositum with any initial presentation field realizes the asserted single enlargement. |
| V_x exact | The existing `CommonPoint.exact` maps every short exact heart complex to a short exact vector-space complex. |
| Family detects zero objects, isomorphisms, zero morphisms | `detects_zero`, `detects_iso`, `detects_zero_map`, all iff tests, over every algebraically closed κ and every Spec κ→X |
| Family detects short exact complexes | `detects_short_exact`, iff for all short complexes. For two arbitrary consecutive arrows with short exact fibre sequences, functoriality and zero-map detection first force their composite to be zero, after which this field applies. |
| Scalar extension faithful and exact | `scalar_additive`, `scalar_faithful` and `scalar_homology`, on the actual ModuleCat.extendScalars from each finite stage to Ω. Preservation of kernels and cokernels is exactness; additivity gives the equivalent preservation of finite limits and colimits |
| w→w tensor 1 injective | `scalar_unit_injective`, with Mathlib's left-tensor convention `(fun w ↦ (1 : Ω) ⊗ₜ[E, stageEmbedding ...] w)` |
| Scalar extension identifies homology | `scalar_homology : (...extendScalars...).PreservesHomology`, which supplies the canonical `ShortComplex.mapHomologyIso` and full homology-map comparisons |
| Actual common-stage pullback comparisons | `pull` is a natural isomorphism using `commonHeartPull` (the literal heart restriction of pbcQbarCompletedPull). |
| Comparison on every finite heart pair is alpha tensor Ω | `pull_finite`, including the HEq of the stage/pull comparison to the underlying identity and the equation with `α.pull` extended by ModuleCat.extendScalars |
| Naturality under every common-stage representation | `pull` is a natural isomorphism on the actual quotient heart, not only a family of objectwise isomorphisms. The normalization equations are quantified at all stages. Its naturality therefore covers every representative map [M,u]. |
| Identity and composite-pullback equations | `identity` and `composition`, using the actual `commonHeartPull` functors, exactly as in the recorded Descent interface |
| Transition comparison exactly beta with balanced associator | `scalar`: the z map sends b tensor (a tensor m) to (b*embedding(a)) tensor m, for every a,b,m; the final equation identifies the transition map with `β.scalar` followed by z. No freely chosen associator is allowed. |

Dependency declarations used (recorded modules are imported directly or transitively; indirect ones remain canonical):

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing` and its public coefficient definitions.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower` and the coefficient datum.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`; the actual stage interfaces reuse the canonical underlying integral full subcategory.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `PbcRationalDerivedCategory`.
- `Sheaf.Paper.LocalizedTStructure`: `pbc_localized_tstructure`.
- `Sheaf.Paper.IntrinsicQbarCategory`: `WeilConjectures.intrinsicPbcQbarCategory`.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension` and its actual scalar data.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`: `ContinuousRational.Family`, `localizedT`, `continuous_rational_derived_realization`.
- `Sheaf.Paper.AdicNormalizedFibreExactness`: `ContinuousRational.NormalizedFibre.adic_normalized_fibre_exactness`, via the existing normalized fibre assertions.
- `Sheaf.Paper.FiniteStagePairCategory`: `PbcFiniteStagePairCategory`, `pbcStageCategory`, `pbcScalarSystem`.
- `Sheaf.Paper.CommonStageCalculus`: `commonStageCalculus`.
- `Sheaf.Paper.PerAdicCommonStageTruncations`: `perAdicCommonStageTruncations`.
- `Sheaf.Paper.AdicStratifiedPullbackInterface`: `pullbackAssertions`, `FiniteTypeBase`, `base`, `heartPull`, `commonHeartPull`.
- `Sheaf.Paper.AdicNormalizedFibrePullback`: `NormalizedPullback`, `adic_normalized_fibre_pullback`.
- `Sheaf.Paper.AdicNormalizedFibreScalar`: `NormalizedScalar`, `adic_normalized_fibre_scalar`.
- `Sheaf.Paper.AdicFibreComparisonData`: `Fibres`, `CommonPoint`, `stageHeart`, `heartScalar`, `stageEmbedding`.
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology` (publicly importing ShortExact): `exists_isLimit_kernelFork_of_distTriang`, `exists_isColimit_cokernelCofork_of_distTriang`, `isHomological_homology₀`.
- `Sheaf.Paper.PbcCommonStageCones`: `pbcCommonStageDistinguished`.
- `Sheaf.Paper.PbcVerdierAxioms`: the recorded Verdier assertion, for the proof plan.
- The Mathlib leaf `lem-weil-field-scalar-extension-exact` has no Lean record and needs none. Its match is `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` in `Mathlib.Algebra.Category.ModuleCat.Descent`, together with `extendRestrictScalarsAdj` and left-adjoint preservation of colimits. The new statement retains arbitrary coefficient-closure universe v; its scalar preservation fields do not force v=u.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration. Its actual finite-type/separated properties are precisely those stored by FiniteTypeBase, as above.

Existing-statement searches actually run:

- msearch.py leanfinder: “Finite stage fibre functors descend to a common coefficient heart, preserve exact sequences and jointly detect zero objects and morphisms”. Eight generic hits, including `Functor.exact_tfae`, `preservesFiniteLimits_tfae`, Freyd--Mitchell and Grothendieck-category results; none states this completed PBC/coherence assertion.
- msearch.py loogle: `Functor.PreservesHomology, ModuleCat.extendScalars, PreservesFiniteLimits`. Zero hits; service reported unknown identifier Functor.PreservesHomology. This is a namespace/query limitation, not evidence that homology preservation is absent. The exact class was then read locally in ShortComplex/PreservesHomology.lean.
- msearch.py grep: `homologyComparison|imageComparison|PreservesHomology|tensor.*injective` under CategoryTheory: 25 generic hits about homology and abelian image comparisons.
- msearch.py grep: `commonStage.*[Ff]ibre|normalizedFibreCommon|CommonPoint`: zero Mathlib hits.
- rg in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no duplicate of the three delivered names, no upstream reference to the item's id. Project hits locate CommonPoint, CommonAssertions, Descent, and `normalizedFibreComparisons`. The last theorem additionally asserts finite/common rank stratifications and existence of all finite comparison data; it is not the statement here, which accepts specified alpha/beta and concludes descent plus the explicit finite-stage exactness assertions. It is never used as a premise.

No missing mathematical notion was found: every category, scalar functor, fibre and
comparison is reused. The two records are assertion packages belonging to this node.
The already documented future proof import from PerAdicNormalizedFibreComparisons
back to this module must be omitted to avoid its import cycle through the scalar
normalization module (stage-2 rule 3.7). No live source was edited.

Edge cases checked before and after writing:

- Empty X: no geometric points; zero detection correctly asserts all heart objects are zero. Existing normalized fibre data have this empty-scheme case. No Nonempty hypothesis was added.
- Zero objects, zero arrows, zero vector spaces, empty finite complex shape, and rank zero are included in every quantifier. No basis is demanded in the statement.
- Identity coefficient inclusion E=E: the scalar transition equation and normalized beta identity give the identity map. Arbitrary further enlargements use the prescribed transIso, not equality of field labels.
- Ω can be an infinite extension of a finite stage. Faithfulness and injectivity use a basis retraction and do not assume FiniteDimensional E Ω.
- Non-flat scheme maps g are included. Only finite coefficient field tensor is asserted exact; no pro-etale stalk/limit commutation is assumed.
- Characteristic equal to l is excluded exactly by the node's invertibility hypothesis; all other characteristics are allowed.
- Universes u (schemes and small finite fields), v (coefficient closure), and w (finite complex index) are independent and explicitly declared. The adjunction unit in Mathlib requires a shared large module universe; using its exact explicit pure-tensor map avoids imposing that restriction on the theorem.
- The preservation clauses refer to all kernel/cokernel data. An attempted explicit shifted-cone restatement exposed the project's two presentations of the rational shift; it was replaced by the equivalent universal preservation assertion on the existing heart, retaining the actual maps. No triangulation is redefined or assumed equal.

Validation: scompile.py passed the sandbox and final-module checks for the final
assertion (55.0 s and 41.8 s on that run), without warnings. The final import closure and
report packaging are checked by the mandatory deliver2.py dry run. Redundant
finite-limit/finite-colimit fields were consolidated into their equivalent
PreservesHomology assertion to reduce elaboration work, retaining all canonical
kernel/cokernel maps. Redundant direct public imports were removed; their recorded
modules remain in the transitive dependency closure. The
60-second limit has not been changed; no direct Lean or global build was run.

## Second reading by Q37

The dispatcher forbids subagents, so this is a separate rereading by the assigned
worker, not a claim that another worker reviewed it. The maintainer's independent
review remains the external second reading. I reopened the node and full final
module and checked the hypothesis and conclusion tables above against both.

The rereading caught two distinctions and retained them in the final signature:
alpha and beta are supplied inputs (not existentially replaced), and the existing
CommonAssertions package includes rank assertions not in this node (so only the
published CommonPoint is reused). It also checked that short_exact_stage uses an
isomorphism of ShortComplex, finite_complex_stage an isomorphism of complexes,
inclusion_image identifies both maps, and scalar/pull equations use the actual
raw transition/pullback functors. Detection is over all geometric points, and
scalar_unit_injective uses the explicit canonical unit with no universe equality.
All ten proof steps are retained in the theorem docstring. There is one sorry,
no hollow definition, no silent statement correction and no reported dispute.
