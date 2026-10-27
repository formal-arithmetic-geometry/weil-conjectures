## Worker report

Stage 2, Q23, lem-trf-primitive-quotient-realization-comparisons. The accepted
six-step split is retained verbatim. The inherited BLOCKED ending concerned an
unchanged stage-1 delivery, not the current stage-2 task: the live queue assigns
stage 2, and the item has no Lean record. No repair note exists. The current
brief-stage2 §0 explicitly authorizes this handoff.

The new module is Sheaf.Paper.PrimitiveQuotientRealizationComparisons. Its seven
named theorems have only `sorry` proofs, with source and complete proof plans.
Its three helper definitions contain real data: the existing universal cochain
change-of-rings model at the finite quotient inclusion, its sheafified tensor
generator, and the predicate specifying balanced association on all generators.
The universal pair fixes its ordinary functor on objects and maps and its derived
functor by the universal counit. There is no unconstrained map or object choice.

Clause-by-clause rendering:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. Every coefficient field has `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, and likewise L and M.
  `ι : E →ₐ[ℚ_[l]] L` and `j : L →ₐ[ℚ_[l]] M` encode inclusions in the fixed
  closure by their induced embeddings. Equality is allowed: the unit theorem
  explicitly uses `AlgHom.id`, and the triple theorem imposes no distinctness.
- Arbitrary schemes have universe t, independent of coefficient universe u.
  `_hlX`, `_hlY`, `_hlW` state `∀ x, IsUnit (l : X.residueField x)`, exactly
  invertibility of ell. No finite type, separatedness or nonemptiness is assumed.
- The imported `Scheme.ProEt` and `Scheme.ProEt.topology` are the fixed small
  pro-etale site presentation (objects t+1, morphisms t). Coefficients and modules
  have size max u (t+1). No equality of site and coefficient universes is imposed.
- `integralCoefficientCommRingSheaf l E W n` is the constant quotient sheaf at
  exponent n+1. `completedIntegralCommRingSheafUnrestricted` is its actual inverse
  limit, not the discrete constant integer sheaf. `integralTowerModules` and
  `scalarReductionSource` are its module category. `DerivedCategory` is the
  ordinary unbounded localization at quasi-isomorphisms.
- `SY`, `SW : CoefficientDerivedSystemCalculus ...` fix the whole-system reduction
  functors, realization, specified adjunction, unit and counit. These are the
  exact recorded calculus objects; their existence is the dependency theorem,
  so they are fixed choices from the node, not an extra effectivity assumption.
- The geometric operation is `integralComparisonDerivedSequencePullback l E f`,
  the exact derived left adjoint on the entire ringed sequence site. The scalar
  operation is `integralComparisonDerivedSequenceScalar l E L ι W`, the universal
  cochain-normalized derived change along the actual quotient sheaf map.
- The completed operations are `integralDerivedPullback` and
  `integralScalarExtensionOfUniverses`, as used in the two model structures.
  `ρX`, `ρW : IntegralComparisonRoosModel ...` fix the normalized comparison.
  Its `comparison` goes from total limit to H; its inverse is the rho of the
  node. Its `computes` clause pins it on K-injectives by the ordinary limit
  tuple with zero shifted coordinate. The map functor is the actual Roos cone.
- `primitiveQuotientRealizationComparisons` supplies
  `IntegralComparisonPullbackModel ...` and `IntegralComparisonScalarModel ...`.
  Each `.realization` is the full natural isomorphism on the ambient derived
  category, hence for every K and every derived morphism, without boundedness
  or completeness restrictions. Their codomains are respectively R ⋙ U ⋙ L
  and R ⋙ S ⋙ L, so the orientations are exactly alpha and beta in the node.
- `primitiveQuotientReductionGood` states flat terms and K-flatness of every
  ordinary quotient of every `integralOperationsGoodComplex` P. That property
  is exactly K-flatness plus flat terms of the completed-ring complex.
- The input presentation in `primitiveQuotientSystemGood` is the recorded
  `CoefficientReductionPresentation`: C, e and κ are one whole quotient
  presentation. Its first equation pins the finite comparisons, and its second
  equation pins every horizontal map for n ≤ m to the actual ordinary quotient.
  Existence of these presentations is `SY.reductionModel`/`SW.reductionModel`.
- Pullback `.normalization` is `IsIntegralComparisonPullbackNormalized`. It
  quantifies over EVERY such P,C,e,κ, supplies an isomorphism q of strict towers
  with `integralOperationsPullbackTowerFunctor`, and pins q on the actual
  inverse-image unit generators. This identifies the termwise pullbacks and
  their actual transitions, rather than independently chosen evaluated objects.
  Its final equation identifies alpha, after these representative comparisons,
  with the defining pullback Roos model. No product is passed through pullback.
- `primitiveQuotientScalarAssociation` supplies the simultaneous family a_n of
  natural isomorphisms between (P tensor A_E,n) tensor A_L,n and P tensor A_L,n.
  `PrimitiveQuotientAssociation` fixes EVERY balanced generator: in the library's
  coefficient-first convention b tensor (s tensor x) maps to (iota(s)b) tensor x.
  This is precisely (x tensor s) tensor b mapping to x tensor sb in the node.
  Naturality of the module functors makes these chain isomorphisms degreewise.
  Uniqueness follows from the generator formula; no flat coefficient map is used.
- `primitiveQuotientSystemGood` asserts K-flatness and flat terms on the entire
  ringed sequence site and invertibility of the actual universal cochain counit
  `(integralComparisonSequenceScalarModel ...).ε.app C`. Thus the termwise scalar
  system computes whole-system derived extension, not just each evaluated object.
- Scalar `.normalization` is `IsIntegralComparisonScalarNormalized`. Its q is an
  isomorphism of strict restricted towers from the whole scalar system to
  `integralScalarTowerFunctor`, fixed by the same scalar-unit tensor generators.
  Its equation says beta followed by the cochain counit, total-limit/Roos bridge
  and H(q) is the defining scalar model comparison. Rearranging says exactly
  beta = rho composed with H(a_P) inverse, on the defining cone.
- `primitiveQuotientScalarTransition` is the actual transition square on every
  sheafified tensor generator in every degree; reduction of the two coefficients
  agrees with reduction of their product. Together with naturality and the strict
  tower q this is a strict-system chain isomorphism, not a levelwise-only claim.
- `primitiveQuotientScalarTriple` includes the finite and mixed associators with
  their multiplication formulas and an equality of natural isomorphisms, including
  the functor associator, for the two associations from E through L to M. Both
  send the three coefficient factors to their product in M. It includes arbitrary
  j and iota, hence identity and repeated fields too.
- `primitiveQuotientScalarUnit` fixes the identity finite scalar map by s tensor x
  mapping to sx, fixes the identity completion-to-quotient comparison by the same
  ordinary quotient tensor generator, and states their unit square as an equality
  of natural isomorphisms. It makes no assertion that ambient completion is identity.
- No declaration assumes flatness or finite Tor-amplitude of A_E,n → A_L,n.
  All representative equations quantify over arbitrary unbounded good complexes.

Dependency declarations read and used:

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing, with the constructions of
  Sheaf.NumberTheory.Padics.CoefficientExtension publicly retained.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and its topology.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses:
  integralConstantToCompletionOfUniverses and the publicly retained actual
  completedIntegralCommRingSheafUnrestricted and its quotient projections.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and Q.
- Sheaf.Paper.CoefDerivedSystemEvaluationCalculus:
  coefficientDerivedSystemEvaluationCalculus, CoefficientDerivedSystemCalculus,
  CoefficientReductionPresentation, CoefficientReductionModels.
- Sheaf.Paper.IntegralComparisonSequenceSystems:
  integralComparisonDerivedSequencePullback, integralComparisonSequencePullback,
  integralComparisonDerivedSequenceScalar, integralComparisonSequenceScalarModel.
- Sheaf.Paper.IntegralDerivedOperationsOnSlices publicly retains
  integralDerivedPullback and its defining good-representative comparison from
  IntegralDerivedOperations; the latter is the operation this node uses.
- Sheaf.Paper.IntegralScalarExtensionUniverses:
  integralScalarExtensionOfUniverses, integralScalarExtensionComparisonOfUniverses;
  integralScalarQuotientSheafMap, integralScalarReduction, integralScalarTensorSection,
  integralScalarTransition and integralScalarTowerFunctor from the retained construction.
- Sheaf.CategoryTheory.StrictRoosComparison: strictRoosComparison, with its complete
  signature and normalization read. The specialized presentation is the existing
  IntegralComparisonRoosModel, not another construction of Roos.
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients:
  CochainComplex.exists_isKFlatResolutionIndependentCoefficients.
- Sheaf.Paper.IntegralComparisonRealizationModels:
  IntegralComparisonRoosModel, IntegralComparisonPullbackModel,
  IntegralComparisonScalarModel and their two IsIntegralComparison...Normalized
  predicates. Its definition node def-trf-integral-comparison-realization-models
  is already landed and is added to stmt_deps, as authorized for landed definitions.
- Proof imports retain ChangeOfRingsKFlat, SemilinearDerivedSections,
  ProEtaleConstantExact, ProEtaleCountableProductsExact, FlatRoosFunctorDescent,
  and OrdinaryDerivedChangeOfRings. The last publicly retains the generic
  DerivedChangeOfRingsCochainModel used here; its ordinary-module specialization
  is not substituted for the generic site statement.

Sources opened: local proetale.tex lemma-pushforward-Noetherian-case, especially
clause (5); sites-cohomology.tex lemma-K-flat-resolution, lemma-pullback-K-flat,
lemma-derived-pullback-composition and lemma-derived-limit-is-ok. Stacks 099N(5)
assumes completeness: the present ambient claim follows the recorded completed
operation's explicit all-ambient quotient/Roos definition, exactly as the accepted
node says, rather than extending the Stacks assertion beyond its hypotheses.
The latest trace-transport blueprint proof was read; the old named Karoubi
ancestor is absent, as already recorded in the accepted split's blueprint metadata.

Edge cases checked: zero P (all tensors and cone maps are zero-object maps), empty
schemes (no hidden point or nonempty-site hypothesis), n=0 in Lean (exponent 1),
unbounded P, f identity, E=L=M and identity embeddings, and independent t,u.
For ramification, Q_3 ⊂ Q_3(sqrt(3)) at exponent 2 has the nonflat map
Z/9 → F_3[epsilon]/epsilon²: K-flatness of the input, rather than flatness of
this ring map, is precisely what both counit-computation statements use.
No statement correction, disputed assertion, new independent definition node,
or unusable dependency repair is required.

Searches (msearch.py, Q23/item):

- leanfinder: "Primitive completed pullback and integral scalar extension
  realization isomorphisms from strict quotient systems on K-flat complexes";
  8 hits, including ModuleCat.preservesFiniteLimits_extendScalars_of_flat,
  Algebra.Extension.tensorH1Cotangent, AdicCompletion.tensor_map_id_left_eq_map.
  No simultaneous strict quotient/Roos realization theorem.
- loogle: "SheafOfModules.pullbackComp"; 5 hits: pullbackComp, pullback_comp_id,
  pullback_id_comp, pullback_assoc, conjugateEquiv_pullbackComp_inv. These are
  ordinary pullback coherence, not the completed primitive realization assertion.
- grep: "primitiveRealization|quotient.*KFlat|KFlat.*quotient"; zero Mathlib hits.
- grep: "scalar.*(associat|realiz)|realiz.*scalar", Algebra/Category/ModuleCat;
  zero hits.
- leansearch: "K flat quotient systems scalar extension realization natural
  isomorphism"; 8 hits, ordinary ModuleCat extension/restriction adjunction and
  localization/flatness results, no match for this node.
- rg in WeilConjectures and Sheaf for primitive/completed/realization comparisons:
  found IntegralComparisonRealizationModels (definitions, used),
  NormalizedCompletedOperationModels (tensor/pullback, no scalar assertion),
  CompletedPrimitiveCounitComparison (different inverse-image presentation and
  tensor/counit assertion, no scalar realization), and generic quotient flat models.
  None states this combined node with its scalar transition/triple/unit formulas.
- rg for the item id in WeilConjectures: no declaration. All ten chosen declaration
  names searched in both project roots and the upstream-name inventory: no clashes.

Validation: scompile.py compiled the actual module against the live published
library (both sandbox and library passes), clean, 5.8/6.0 seconds at the recorded
intermediate version. Every variable and universe is explicit; autoImplicit is
false. An initial wrong FlatRoosFunctorDescent directory and an omitted explicit
site parameter in IsFlatOnSite were repaired; no API or universe restriction was
introduced to resolve either error. Final delivery/preflight results follow below.

Final validation: deliver2.py --no-push printed `OK (dry run): commit 20dcfde2ac8
passes the preflight and compiles; nothing pushed`. This used the complete final
module, including the recorded proof-dependency import. No preflight repair was
needed. The prescribed wrapper supplies the second-reading placeholder; the
maintainer performs the independent review, as required by the current dispatch.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
