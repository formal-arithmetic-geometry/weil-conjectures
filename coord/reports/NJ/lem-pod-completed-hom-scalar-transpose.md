## Worker report

The module `Sheaf.Paper.CompletedHomScalarTranspose` states
`WeilConjectures.CompletedHomScalarTranspose.completed_hom_scalar_transpose` and its
completion/coherence clauses. Every theorem has proof `by sorry`. Definitions have
real data; chosen isomorphisms come from generator-normalized unique-existence
statements. The item statement, dependencies, proof and all other node fields are
unchanged. No new node or dependency replacement is needed.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`,
second sentence. This sentence supplies the coefficient-ring computation; the
nine-step agent-written DAG proof supplies the refined scalar, sign and strict-cone
normalizations. The module's theorem docstrings carry the relevant proof steps.

Hypotheses and objects, clause by clause:

* `D : FiniteFieldDatum.{u}` provides the finite field and its specified algebraic
  closure `D.k`; every site is the original `(Spec (.of D.k)).ProEt`, object size
  `u+1`, arrow size `u`.
* `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` render the prime/invertibility condition.
* `E`, `L`, their field, p-adic algebra and finite-dimensional instances, and
  `ι : E →ₐ[ℚ_[l]] L` express the finite coefficient inclusion. Abstract embedded
  fields are represented by the inclusion map, without selecting a second closure.
  There is no restriction such as unramified, proper or distinct inclusions.
* `PointCompletedEvaluation.R` is exactly the recorded lifted ring of integers.
  `PointCompletedEvaluation.B` is the completed sheaf, not the discrete constant
  sheaf. `integerMap` is `integralScalarIntegerInclusion` conjugated by `ULift.ringEquiv`.
* `P`, `lo`, `hi`, `_hlo`, `_hhi`, `_hP` render boundedness and finite projectivity
  of every term. The definition is the same bounded-projective model criterion
  underlying `DerivedCategory.IsPerfectRingComplex`; no extra perfectness hypothesis
  on its derived image is added.
* `PL` uses `ModuleCat.extendScalars` termwise; the scalar-first order is
  `S ⊗[R] P`, canonically the node's `P ⊗[R] S`. Its tensor generators use the
  specified scalar map explicitly. `PointCompletedEvaluation.dual` is the existing
  ordinary product Hom complex into `R[0]`, with its signed differential.
* `PointCompletedEvaluation.model D l E P` and the same model on the dual are K,H.
  The models over L on `PL` and its dual are K_L,J_L. They use the existing
  sheafified constant modules and existing extension functor, not private copies.
* `_hmodelsE` and `_hmodelsL` impose `finiteTorConstructibleIntegral` on the listed
  two models and their ordinary evaluation tensor complex. This predicate includes
  `sfIntegralConstructible` (derived completeness, finite constructible reductions,
  uniform cohomological bounds) and one Tor interval for every positive quotient.
  Thus it renders exactly the statement's complete/constructible/finite-Tor model
  hypotheses and their evaluation tensor hypotheses.
* `h`, `hL` are the supplied ordinary finite-projective Hom identifications.
  `HomNormalized` gives their canonical evaluation formula on the existing constant
  tensor generators. `_hd` and `_hdL` say their composites with the recorded canonical
  ordinary-to-derived Hom map are invertible, as supplied by the stated point
  completed-evaluation identification. `homMap` is that composite, not a newly
  chosen derived Hom map.

Conclusions, clause by clause:

* `modelBaseChange_existsUnique` gives FK ≅ K_L with the stated forward and inverse
  formulas. In the scalar-first encoding, forward is `a tensor (b tensor x)` mapped
  to `image(b)*a tensor (1 tensor x)` and inverse is `b tensor (a tensor x)` mapped
  to `image(a)*b tensor (1 tensor x)`. Both formulas are on actual sheafification
  generators and in every degree. The same declaration applies to the dual model.
* `ModelResult` gives an actual morphism `gamma : FH ⟶ J_L`. It is a morphism of
  cochain complexes, so the differential compatibility is part of its type.
  The first conjunct, using `value` and `modelBaseChange`, is exactly
  `gamma(h tensor a)(z tensor b) = image(h(z))*a*b` for arbitrary local homogeneous
  sheaf-model sections h,z and arbitrary completed coefficients a,b.
* Values into the coefficient complex are read with `sheafValue` when `p+j=0`.
  In every other degree the coefficient single complex is zero; hence those
  evaluations vanish uniquely. This retains every homogeneous degree.
* The next conjunct is `Q.map gamma ≫ homMap_L = identifiedTranspose`. The latter
  is the ordinary evaluation-defined scalar transpose `scalarHomOrdinary` with
  precisely the model factors on its source, input and coefficient output. Thus
  the assertion identifies the actual cochain map, not just its cohomology maps.
* `completed_conjugation` explicitly identifies the completed operation delta,
  after its Hom-output and two input completion units, with `scalarHomOrdinary`.
  It applies in particular to K and B[0]. Combining its displayed equality with
  the preceding model equality is precisely the stated conjugation by chi.
* `completion_implementation_transport` identifies the two published implementations
  of ordinary extension and completion. Its first conjunct is equality of actual
  chain maps through `ordinaryTransport` into the same strict quotient cone.
  Its unique derived transport has the ordinary counit square, the strict completed
  representative square and the chi equation. Therefore the chi here is the one of
  `FiniteFreeCompletedScalarComparison`, not an independently chosen completion.
* `CompletionSquare` is required both for gamma over B' and for its signed evaluation.
  It gives equality of the two actual chain maps into the identity quotient cone,
  their product projection in every quotient, and zero shifted-product projection
  in every degree. The product formula is reduction of the actual image of f;
  for gamma/evaluation this is the displayed (signed) coefficient product.
  The maps are strict tower maps via `integralScalarComplexFunctor`, so quotient
  transition compatibility is built into these actual chain maps.
* The last part of `ModelResult` supplies evaluation on `K_L tensor FH` with value
  `(p*j).negOnePow • (image(h(z))*a*b)` on its total-tensor generators. These are
  the existing total injections, not an abstract replacement tensor.
* `derived_coherence` first quantifies over every derived arrow between the actual
  sheaf models and gives the contravariant Hom naturality square. It imposes no
  chain-representability hypothesis, so includes roofs and inverse quasi-isomorphisms.
  Via the model identification equality this is naturality of the gamma maps.
* The second clause of `derived_coherence` is the identity-extension square under
  `integralOrdinaryDerivedScalarUnit` (multiplication). Combined with
  `completed_conjugation` it is the completeness-normalized identity for delta.
* The third clause quantifies over every further finite field M and inclusion
  `j : L →ₐ[ℚ_[l]] M`, giving the two-step/direct scalar-Hom equation with the
  recorded `integralOrdinaryDerivedScalarComp`. The node specifies its integral
  associator by conjugation of this ordinary associator by chi; the preceding
  conjugation equality supplies exactly that equation after cancellation.
  The strict-cone product formulas reduce both paths to the same coefficient
  product, including the same Koszul sign and zero shifted coordinate.
* No assertion about taking sections is present.

Dependencies used (all statement-dependency declarations and source signatures read):

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  publicly retaining `Padic.coefficientExtensionIntegers` and finite quotient definitions.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the recorded completed coefficient sheaf.
* `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`; the theorem uses its explicit model binders.
* `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `Scheme.proEtaleConstantModuleSheafOfUniverses`, through the recorded point model.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing sheaf tensor construction.
* `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, through
  `finiteTorConstructibleIntegral`.
* `Sheaf.Paper.PointCompletedEvaluation`: `point_completed_evaluation`, `model`,
  `dual`, `B`, `R`, `generator`, `coefficient`, `total`, `sheafValue`, `moduleValue`.
* `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleIntegral`
  (publicly retained integral clause; the primary etale predicate is not substituted).
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedCoefficientMap`,
  `completedOrdinaryScalarComplex`, `completedDerivedScalarExtension`,
  `completedScalarChainComparison`, `completedScalarComparison`, `completedScalarCounit`.
* `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`,
  `integralScalarExtensionComparisonOfUniverses`.
* `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarHomOrdinary`,
  `scalarHomCompleteInputs`, `scalarCompletion`, `scalarCompletionIso`, the actual
  quotient-normalized tensor and Hom comparisons, `scalarOperationsOrdinary_tower`.
  Publicly retained `integralOrdinaryScalar`, `integralOrdinaryDerivedScalar`,
  `integralScalarCompletionChain`, `integralScalarRoosBoundary`, tensor sections,
  and `integralOrdinaryDerivedScalarComp`/`Unit` are used directly.

All stated proof-dependency modules are imported with plain `import` unless already
public statement dependencies. These include PerfectDualScalarCalculus,
BoundedAboveFlatSheafKFlat, OrdinaryDerivedChangeOfRings,
DerivedInternalHomMixedUniverses, OneKFlatChainTranspose,
RingedDerivedClosedSymmetricMonoidal, IntegralDerivedOperationsOnSlices, StrictRoosModel.
No import cycle was found or omitted.

Edge cases checked mathematically: P=0 (all maps are the unique zero-source maps);
P=R[0] (both formulas give coefficient multiplication); P concentrated in degree 1
(the degree -1 functional gives the required negative evaluation sign); arbitrary
negative degrees (integer `negOnePow`); vanishing output degrees (the coefficient
single complex is zero); finite projective summands without a basis (the formulas
use no basis); ramified extensions (no flat quotient-map assumption); L=E,
E=L=M and one identity inclusion in a tower (the unit/associator clauses apply).
No extra equality between object and arrow universes is imposed. All universe and
term variables are explicitly bound, with `autoImplicit false`.

Searches for existing declarations:

* `msearch.py ... leanfinder "completed coefficient sheaf internal Hom scalar extension transpose finite projective evaluation"`:
  eight LightCondensed/internal-Hom hits, none on these completed coefficient point models.
* `msearch.py ... loogle "Module.Dual.baseChange, CategoryTheory.MonoidalClosed.uncurry"`:
  zero combined-query hits. The separate `CategoryTheory.MonoidalClosed.uncurry` query
  found twelve abstract currying lemmas, including injectivity, none the model theorem.
* `msearch.py ... grep "baseChange_apply_tmul|baseChange_baseChange|uncurry_injective"`:
  sixteen matches, including ordinary module dual base change and abstract currying.
* `rg` on WeilConjectures, Sheaf and the upstream declaration index for the item id,
  `CompletedHomScalarTranspose`, `completed_hom_scalar_transpose` and interface names:
  no existing match. A different namespace has an unrelated point-transport helper.
* Related source search found `SpecifiedHomScalarEvaluation` and its arbitrary-scheme
  version. Those concern K-flat/K-injective Hom models with a resolution augmentation;
  neither supplies this ordinary finite-projective J_L target or the explicit
  FK/K_L inverse. `PointProjectiveDualTensorModels` gives the dual models over a
  single coefficient field, not this completed scalar transpose.

No statement fault or STATEMENT-DISPUTED flag was found.

Validation: scompile.py compiled the module in both sandbox and library module modes
with the required module header. The final dry run and delivery use deliver2.py.

## Second reading by NJ

Independent clause-by-clause reading (maintainer reviewer, written into the report because the
dispatcher forbade a second worker reading). Node statement against
`WeilConjectures.CompletedHomScalarTranspose.*` and the stmt_dep declarations:

* s = Spec k, k = F̄_q, ℓ ≠ char k: `D : FiniteFieldDatum`, `Spec (.of D.k)`, `[Fact l.Prime]`,
  `_hl : l ≠ D.p`. Same as lem-pod-point-completed-evaluation's `point_completed_evaluation`. OK.
* E ⊂ L finite over ℚ_ℓ: `E L : Type u` fields, finite-dimensional over `ℚ_[l]`, `ι : E →ₐ L`.
  `integerMap` is `integralScalarIntegerInclusion` (the codomain restriction of ι) under ULift. OK.
* R, S, B, B': `PointCompletedEvaluation.R/B` over E and over L (the completed sheaf, not the discrete
  constant sheaf). OK.
* P bounded, finite projective terms: `IsStrictlyGE lo`, `IsStrictlyLE hi`, `Projective ∧ Finite` in
  every degree, the same binders as the dependency. No extra hypothesis. OK.
* P_L, P^∨: `PL` = `ModuleCat.extendScalars integerMap` termwise (S ⊗_R P, canonically P ⊗_R S);
  `dual` = the dependency's `moduleHomComplex P R[0]`. OK.
* K, H, K_L, J_L: `PointCompletedEvaluation.model` over E on P and on dual P, and over L on PL and on
  dual PL. These are the recorded sheafified constant extension models. OK.
* "Assume K,H ∈ D^b_c" and "these models and their evaluation tensors are complete, constructible and of
  finite Tor amplitude, uniformly": `_hmodelsE/_hmodelsL` (`finiteTorConstructibleIntegral`, which
  contains `sfIntegralConstructible`) on K, H, total(K,H) and on K_L, J_L, total(K_L,J_L). Proof step 1
  confirms that these are hypotheses. OK.
* The ordinary Hom identifications: `h`/`hL` with `HomNormalized`, which is verbatim the dependency's
  `_hom_normalized`, so it pins h uniquely, and with `IsIso (homMap …)`, which is the dependency's
  `_derivedHom_isIso`, same composite with `IntegralHom.homModelMap`. These are the same objects as
  in the dependency's `Result`. OK.
* F, χ, T_{L/E}: `F` is the chain-level ordinary extension; `identifiedTranspose` passes to D(B') by
  `mapDerivedCategoryFactors`. `completion_implementation_transport` identifies the item's χ
  (`completedScalarComparison`/`completedScalarChainComparison` of
  lem-weil-finite-free-completed-scalar-comparison) with the `scalarCompletion` used by
  lem-pur-integral-operations-scalar-extension. It does so by an equality of actual chain maps into
  the same strict cone and by ∃!-pinned transports. OK.
* δ: `scalarHomCompleteInputs` = `scalarHomCompleted`, which is the χ-conjugate of `scalarHomOrdinary`
  (= `coefficientBaseChangeHom`, the transpose of extended evaluation under `scalarClosedTensor`).
  `completed_conjugation` is the conjugation identity, which is definitional from the dependency.
* FK ≅ K_L with the displayed forward/inverse formulas: `modelBaseChange_existsUnique`. It sends a⊗(b⊗x)
  to ι(b)a ⊗ (1⊗x), and the inverse sends b⊗(a⊗x) to (ab)⊗(1⊗x), on generators in every degree. ∃!, so
  the data is genuine. The coefficient analogue is `coefficientBaseChange_existsUnique`. OK.
* γ actual cochain map with γ(h⊗a)(z⊗b) = h(z)ab: `ModelResult` ∃ γ (a chain map), first conjunct
  for arbitrary local sections h, z and arbitrary a, b ∈ B'. Degrees p+j ≠ 0 land in the zero part of
  B'[0]. OK.
* The χ-conjugate of δ is γ in D(B'): `Q.map γ ≫ homMap_L = identifiedTranspose` (all factors fixed),
  combined with `completed_conjugation` and `completion_implementation_transport`. OK.
* Strict-cone compatibility (quotient product components, zero shifted components): `CompletionSquare`
  for γ and for ev. It is exactly proof step 5's "augmenting after the map = diagonal tower map after
  augmentation", with both coordinates written out. OK.
* Signed uncurried evaluation (-1)^{pq}h(z)ab: ∃ ev on total(K_L, FH) with that value on the total
  generators. OK (advisory: ev is tied to γ by the formula, not stated as the closed-structure
  uncurrying).
* Derived naturality, L=E identity, E⊂L⊂M associator: `derived_coherence`. It specializes the
  dependency's `scalarHomOrdinary_naturality` and `scalarOperationsOrdinary_unit/_tower` (Hom clauses)
  to the point models; v is an arbitrary derived arrow (roofs included); M and j are arbitrary. The
  integral associator is the χ-conjugate by node stipulation. OK.
* No sections assertion. OK.

Edge cases: P = 0; P = R[0] (multiplication); P = R[-1] (sign (-1)^{pj} with j = -1); L = E with ι = id;
ramified L/E; non-free projective terms (no basis used). Universes: one `u`, the pro-étale site with objects
in u+1 and morphisms in u, the same as the dependencies; nothing is forced equal.

Searches: recorded in the worker report. I also grepped the live lean/ tree for the point-model
base-change maps (`PointCompletedEvaluation.model D l L`, `integralScalarIntegerInclusion` lifts). No
existing FK ≅ K_L or γ declaration exists; `integerMap` is a one-line ULift conjugate, also written
inline in CoefficientTwistsDetailed (advisory).

Records: the item node differs from the base only in `lean`. `lean.statement` is verbatim the file
signature, and all 19 declarations exist. No import is a module of a node whose closure contains the
item (no stage-3 cycle). Uncited def-node owners reached through stmt_dep modules
(def-pod-point-derived-hom-models, def-sf-integral-hom-reduction-models,
def-trf-integral-scalar-tower-functors, def-weil-pbc-integer-quotient-inclusions,
def-a1-flat-term-kflat-complex) are advisory, as in earlier landings.
