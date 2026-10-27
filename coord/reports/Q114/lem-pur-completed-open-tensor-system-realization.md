## Worker report

The module `Sheaf.Paper.CompletedOpenTensorSystemRealization` states
`WeilConjectures.CompletedOpenTensor.completedOpenTensorSystemRealization`.
Its sole postponed proof is that theorem. All other declarations are concrete
composites, abbreviations, or types packaging the specified compatible presentations.
No definition contains sorry or chooses data from a mere uncharacterized existence.
The item statement, source and proof are unchanged.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The coefficient extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  Every coefficient construction is the existing Padic integer-ring/uniformizer
  construction. Natural-number level n denotes the positive exponent n+1,
  as in the dependencies; exponent zero is not inserted into the tower.
- The schemes are `{U V : Scheme.{t}}`, with `j : U ⟶ V`,
  `[IsOpenImmersion j] [QuasiCompact j]`. Invertibility is stated as
  `IsUnit (l : Γ(V, ⊤))` and `IsUnit (l : Γ(U, ⊤))`, following the recorded
  integral-open comparison. These express that l is invertible on the schemes.
- The small pro-etale sites retain object universe t+1 and morphism universe t.
  Coefficients/modules use max u (t+1); t and u are independent. The completed
  ring and finite projections are `completedIntegralCommRingSheafUnrestricted`
  and the existing scalar-reduction constructions, not arbitrary ring sheaves.
- Unbounded derived categories are `DerivedCategory (scalarReductionSource …)`;
  the system category is `coefficientSequenceDerived`, the derived category of
  sheaves of modules on the ringed sequence site, not a category of unrelated
  finite derived objects. No boundedness, constructibility or Tor restriction occurs.
- `Context.operations`, `openUnit`, `openUnitHom`, `completeOpen` and `strictOpen`
  retain the existing exact localized open extension/restriction adjunction,
  actual section unit, strict coefficient comparison r_j, and realization d_j.
  `sameOpen` identifies the all-input r_j with the recorded complete-input r_j.
  Context is existentially constructed in the conclusion, not an extra hypothesis.
- `Context.ambient` and `openSite` are the recorded coherent reduction/total-limit
  calculi, with their actual units/counits, tensor models, quotient transitions
  and coherence. `completionV`, `completionU`, `unitV`, `unitU` identify quotient
  completion and its actual unit with L R and u. `tensorV`/`tensorU` in Context
  identify the integral tensor with the tensor used by completedTensor.
- Completed restriction is ordinary `star` on complete inputs, with the actual
  completion comparison `restrictionCompletion` and its unit square
  `restrictionUnit`. This is the restriction used in the final identity.
- The universally quantified K,N have exactly the two completeness hypotheses
  `complete l E U K` and `complete l E V N`. The ordinary tensors H,H_U are
  `ordinarySource.obj (K,N)` and `ordinaryOpen.obj (K,N)`. They are never assumed
  complete. `strictOpen.r` applies to them without a completeness hypothesis.
- The entire systems T and S are `sourceSystem` and `openSystem`, using the
  existing system tensor of the two reductions. Their finite evaluations are
  precisely the displayed finite tensors by the calculus evaluationTensor and
  reductionEvaluation. Those declarations retain every quotient transition.
- `reductionTensorV`, `reductionTensorU` are q_V,q_U, composed from the existing
  normalized strict-system reductionTensor. `systemMap` is exactly
  q_V inverse followed by R(gamma ordinary), r_j(H_U), and J(q_U). Thus the
  system arrow is a specified composite before total limit, not a chosen lift.
- `RepresentativeLaws` first fixes gamma ordinary by localization of
  `strictOpen.totalComparison.chain` on every flat-term K-flat pair. That chain
  comparison is pinned on ordinary extension generators and on every signed
  total-tensor summand by the dependency's TotalComparison.
- `strictChain` is a single chain isomorphism of whole systems: termwise strict
  reduction of that ordinary chain comparison, followed by the ordinary strict
  open comparison. In RepresentativeLaws its scalar-unit augmentation square
  holds in every degree, level and local section before localization; these are
  components of strict chain maps, so they express equality of augmented strict
  system maps. The actual coefficient-comparison formula is used on the right.
  The two `OpenSemilinearTensor.Computation` witnesses include all quotient
  squares and the actual adjunction-transposed strict augmentations. The final
  whole-system localization square identifies this chain map with systemMap.
- The completed isomorphism is the existential `γc`, with exactly the two
  completed tensor endpoints in the node. The first equation is
  eta_V followed by γc = gamma ordinary followed by j_! eta_U. The next clause
  quantifies over every competing isomorphism g and proves g=γc from that
  equation alone; realization is not included in the uniqueness assumption.
- `sourceIdentification` is completionV followed by L(q_V), the defining tensor
  substitution comparison. `openIdentification` is its open analogue.
- `hc` and `he` assert completeness of L_U S and invertibility of the actual
  e_S. `targetIdentification hc he` is L_V J(e_S inverse), then the recorded
  completeOpen.d at L_U S, then j_! of openIdentification inverse. The existing
  dFormula is L_V(r_j inverse) followed by the inverse actual unit. Thus b_S
  and both tensor vertices are the specified substitution maps.
- The third equation is sourceIdentification followed by L_V(systemMap) and
  targetIdentification = γc.hom, i.e. equality of these specified realized maps.
- The final equation applies star to γc and removes the target open unit.
  Its right side is `restrictedIdentification`: restriction/completion,
  completion of the ordinary restricted tensor identification, and the inverse
  open unit. After those identifications the resulting map is identity. This
  definition uses the pinned ordinary gamma, never γc itself.
- No assertion of faithfulness of finite derived evaluations occurs. The equality
  in RepresentativeLaws is in the derived category of whole systems; its strict
  augmentation equation is checked before that localization.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported coefficient constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, retaining the completed
  coefficient sheaf and its projections.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib `DerivedCategory`, the category used by all the calculus interfaces.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`;
  read the full Assertion.gamma_inverse and gamma_restriction normalizations.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `CoefficientTensorModels.iso`, reductionTensor and its strict representative
  normalization, coefficientDerivedSystemEvaluationCalculus.
- `Sheaf.Paper.WeilCompletedTensorReflector`: `AlgebraicGeometry.Scheme.wfCompletionReflector`;
  `Sheaf.Paper.ConstantCompletionEquivalence`: `CategoryTheory.ConstantCompletion.equivalence`.
  These are proof imports; completion objects are the already published slice operations.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `WeilConjectures.IntegralOnSlice.duality`, `completion`, `completionUnit`, `completedTensor`.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`:
  `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.immersion_completed_pullback_comparison`.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`: Operations, Comparison,
  shriek, star, J, complete, TensorComparison, openAdjunction, dFormula,
  AugmentedPresentation, integralOpenReductionComparison.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`: completedOperationTowerSubstitution;
  also read Models.completion_unit, tensorRealization and tensorComparison, whose
  primitive formulas sourceIdentification and openIdentification specialize.
- `Sheaf.SixFunctors.OpenSemilinearTensorModel`: OrdinaryReduction, Computation,
  Comparison, ordinaryChain, TotalComparison, total, extensionComplex and
  restrictionComplex. These plain definitions are owned by the live definition
  node `def-sf-open-semilinear-tensor-model-data`, now cited in stmt_deps.
  The theorem `openSemilinearTensorModel` is not used in the Lean statement;
  `lem-sf-open-semilinear-tensor-model` remains a proof dependency only.
- All stated remaining proof-dependency modules are imported without public:
  KFlatResolutionIndependentCoefficients, PurNormalizedReconstructionAdjunctionCalculus,
  OpenQuotientKoszulCompleteness, RingedTopoiCanonicalTensorPullbackOfUniverses,
  WeilCompletedTensorReflector and ConstantCompletionEquivalence.

Edge cases checked: identity open (all open comparison formulas reduce to unit
identifications); empty open (the zero module/complex categories and their actual
units remain available, with no nonempty-open hypothesis); K=0 or N=0; first
positive quotient and identity quotient transitions; uniformizer-torsion inputs
where higher Tor is present; unbounded complexes; complete inputs with incomplete
ordinary tensor. None is excluded. Quotient maps are not assumed flat. The proof
plan explicitly inverts the reconstruction unit only at complete objects.

Searches performed with msearch.py:

- LeanFinder: “Strict open tensor systems realize the unique completed open
  projection isomorphism normalized by the completion unit”: 8 hits, concerning
  free-monoidal normalization; none is the completed strict-system theorem.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Functor`: 12 hits for generic
  adjunction data and basic constructors; none states the theorem.
- Mathlib grep: `completed.*[Oo]pen.*[Tt]ensor|[Oo]pen.*[Tt]ensor.*[Rr]ealization`:
  no hits.
- LeanSearch: “The completion unit uniquely determines the derived open extension
  tensor isomorphism and it is realized from strict coefficient systems”: 8 hits,
  mostly uniform-space completion and monoidal adjunction units; no match.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and completed-open-tensor
  patterns: no declaration for the theorem. Nearby hits about punctured completion
  charts concern ordinary algebraic tensors on affine charts.
- rg for the new namespace/declaration names in both source trees and
  dag/lean_names_upstream.json: no collision. Other RepresentativeLaws names have
  different namespaces and different mathematical statements.

Sources read directly: sites-cohomology.tex at lemma-j-shriek-and-tensor (Tag 0GL1),
sites-modules.tex at the same label (Tag 0E8I), the entire node proof and all statement
prerequisites, and the recorded modules/signatures. The Stacks result is the ordinary
formula; the strict-system and completion-unit assertions are the explicitly attributed
agent refinement, not claimed to be literal Stacks statements. No statement correction
or disputed mathematical assertion was needed.

## Second reading by Q114

A second pass by the dispatched worker compared the node, all helper definitions,
and the final theorem. This is self-review; no independent worker was launched,
as the dispatch explicitly forbids other agents. The maintainer's independent
review remains the independent reading of this delivery.

The check concentrated on four possible mismatches: ordinary H_U must not acquire
completeness (it does not: strictOpen.r is the all-input comparison); uniqueness
must use only the unit equation (it does); the target identification must use the
actual e_S and u at j_!L_U S (it does, via targetIdentification and dFormula);
and representative augmentation compatibility must not be replaced by agreement
of finite derived evaluations (it is a strict chain augmentation equation and a
separate whole-system localization square). The use of max u (t+1) does not equate
site object and Hom universes. The restricted identity uses only ordinary gamma
and the unit-normalized restriction/completion comparison in its identification.
No new independent notion or dependency repair was needed. All helper declarations
belong to the canonical comparisons asserted by this node and are listed in lean.declarations.

## Repair of independent return 62638ca129b7

H2/H12: replaced the added statement dependency
`lem-sf-open-semilinear-tensor-model` with the existing definition owner
`def-sf-open-semilinear-tensor-model-data`, exactly as the return requests.
The live definition node records the same module and all the plain declarations
used by Context, strictChain, the representative helpers and RepresentativeLaws.
Reading the module confirms that these declarations are ordinary definitions
and structures; the statement never invokes `openSemilinearTensorModel`.
The theorem node remains in proof_deps and in the natural-language proof plan.
No Lean declaration or mathematical statement changed. No node was created.

The saved packet's initial dry run passed at 1e55dc4fea6; that mechanical success
did not fix the independently reported ownership defect. Comparing its node
with current main showed only lean and the added stmt_dep differed. This repair
retains that packet and changes the added dependency to the live definition
owner, rather than replacing or restating any existing notion.

The two advisory observations were reviewed: the integral open comparison's
existing statement dependency and the existential openSystems presentation
remain as independently checked in the return. They introduce no new hypothesis
in this delivery. In particular no supplied section-construction datum is added
to the main theorem: C and its operations remain existential conclusions.

Self-check after repair: Context uses OrdinaryReduction and Comparison; strictChain
uses totalComparison.chain and ordinaryChain; source/openComplex use total and
extension/restrictionComplex; RepresentativeLaws uses Computation. All are listed
under the definition owner's lean.declarations. The only postponed theorem is the
item theorem, with its nine-step source proof docstring. The recorded signature
matches the file verbatim; autoImplicit is false; t and u remain independent;
the completion-unit characterization, uniqueness, specified total-limit
realization and restricted identity are retained without modification.
