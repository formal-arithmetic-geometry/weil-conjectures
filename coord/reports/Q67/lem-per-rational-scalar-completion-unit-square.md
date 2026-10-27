## Worker report

Item: lem-per-rational-scalar-completion-unit-square. The natural-language node is unchanged.
The main module is Sheaf.Paper.RationalScalarCompletionUnitSquare, with the primary theorem
AlgebraicGeometry.Scheme.rationalScalarCompletionUnitSquare. All theorem proofs are `sorry`;
the four scalar comparison definitions are actual inverses or composites of canonical
isomorphisms. The ambient tower isomorphism is selected from its unique
augmentation-normalized theorem in this same module. The module has no axioms, arbitrary-map hypotheses, local notation, private
copies of coefficient objects, or automatically bound variables.

Hypothesis and object audit:

- `l : ℕ` and `[Fact l.Prime]` give the prime. `E L : Type u`, their field and
  Padic-algebra structures, their two `FiniteDimensional` instances and
  `i : E →ₐ[ℚ_[l]] L` encode the finite coefficient inclusion, including identity inclusions.
  All coefficient comparisons use the chosen uniformizers of the recorded coefficient node;
  there is no additional unramified, etale, nonempty or invertible-coefficient-map hypothesis.
- On each scheme the hypotheses are `[IsNoetherian W]`,
  `[Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]` and
  `[Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]`.
  The stalk condition expresses invertibility of l and includes the empty scheme.
  `g : X ⟶ Y` in the file is the node's map X' → X, with the file's X denoting X'.
  Geometric-composition clauses also give Z the same hypotheses.
- The rings are exactly `pbcAdicCompletion W (pbcIntegralDatum l F)`, finite quotient
  limits on `Scheme.ProEt`, indexed by n : ℕ with exponent n+1. `PbcIntegralRing` is
  the existing ULift of the actual valuation ring. This is a universe presentation,
  with the recorded ring equivalence, not a different coefficient algebra. The site
  retains object universe u+1 and Hom universe u; they are never equated.
- `pbcModules`/`ringedSiteModules`, the published sheaf tensor and `PbcCompletedDerived`
  give the module sheaves, tensor and unbounded derived categories. No boundedness
  condition is placed on an ambient K or N.
- `PbcBoundedConstructibleComplete` is the completed integral category, including its
  intrinsic completeness, uniform reductions and compatible etale-origin witnesses.
  `PbcRationalCategory` and `pbcRationalization` are the existing raw localization.
  The contextual realization J and its object/fraction formulas are exactly those of
  `RationalModuleRealization` imported from the recorded realization dependency; this
  item makes no additional assertion about J and does not define a second realization.
- `pbcEmbeddingAmbientTensor` is C; its coefficient map is fixed by finite projections.
  Its constructible restriction and raw localization are the recorded
  `pbcEmbeddingIntegralTensor` and `pbcRationalScalarExtension`.
- `pbcActualDerivedPull` is ordinary P. `pbcActualStrictCompletedPull` and
  `pbcActualStrictCompletedPullUnit` are the actual quotient-tower functor and gamma.
  `pbcActualCompletion` and `pbcActualCompletionUnit` are the intrinsic-complete reflector
  and eta, with the existing Koszul and constant/quotient interpretations. The item
  supplies the unit-compatible ambient comparison to the strict construction.

Conclusion audit, clause by clause:

- `rationalScalarCompletionCoefficients` states a module-sheaf basis isomorphism of rank
  `WeilConjectures.completedScalarRelativeDegree l E L i` (defined by Module.finrank with
  the algebra induced by i). It states e ≥ 1, a valuation-ring unit a and t_E=a*t_L^e.
  Its final universal clause states the same equality on every coefficient-sheaf section
  and invertibility of the constant section of a. Thus the sheaf and ring assertions
  retain arbitrary positive ramification indices.
- `rationalScalarCompletionKappa` is `(pbcScalarCompletionIso ...).symm`, the natural
  isomorphism C Lambda_E → Lambda_L C. `rationalScalarCompletionKappa_unit` is
  C(eta_E) followed by kappa = eta_L, for every ambient N.
- `rationalScalarCompletionKappa_identity` identifies kappa with the actual tensor
  unitor at Lambda N followed by Lambda of its inverse at N.
  `rationalScalarCompletionKappa_coefficients` is the successive-coefficient equation
  under `pbcAmbientScalarComp`. Its equation is written in the inverse orientation,
  exactly as the published comparison; inversion gives the node's kappa orientation.
- `rationalScalarOrdinaryBeta` is the inverse of the published
  `pbcScalarOrdinaryPullIso`, so its direction is C_X' P_E → P_L C_X.
  `rationalScalarOrdinaryBeta_tensor` gives s tensor r tensor m ↦ s*i(r) tensor m on
  inverse-image tensor generators, using the actual module adjunction unit and
  `pbcTensorSection`. Linearity fixes all balanced sections. The explicit `@id` terms
  only expose the target section type of the published direct-image unit.
  `rationalScalarOrdinaryBeta_representative` states the actual universal-counit
  square on flat-term K-flat complexes, with the ordinary balanced chain isomorphism.
  The coefficient square is the existing `pbcScalarCoefficientStructureSquare`, proved
  by all finite projections; no isomorphism of inverse-image completed rings is used.
- `rationalScalarCompletionRightAdjoint` gives preservation of intrinsic completeness
  by the canonical derived right adjoint and the exact eta-normalized direct-image
  comparison `pbcActualDirectCompletionIso`. This is the right-adjoint input to
  `ReflectedCoefficient.Square` with F0=P_E, F1=P_L, C_A=C_Y, C_B=C_X, delta=beta inverse.
- `rationalScalarReflectedBeta` is the inverse of the published reflected completed
  comparison. The second conjunct of the primary theorem is precisely
  kappa at P_E K followed by Lambda_L(beta_K), in Lean's left-to-right composition.
  Hence it is the inverse comparison from the specified reflected-square construction.
- `rationalScalarStrictBeta` transports this exact comparison to the actual strict
  quotient functors using the two augmentation-normalized ambient isomorphisms.
  The first conjunct of the primary theorem is C(gamma_E) followed by beta_hat =
  beta followed by gamma_L. The third conjunct identifies its transport with
  eta_L at C(P_E K) followed by Lambda_L(beta). The first equality also identifies
  the other side with this intermediate expression, after the same specified
  target identification. No equation is inferred merely from isomorphic objects.
- `rationalScalarCompletionUnitSquare_constructible` asserts C_Y K belongs to the
  actual integral L category and asserts invertibility of both actual strict gamma
  arrows, for every integral constructible K and arbitrary g.
- `rationalScalarCompletionUnitSquare_identity`, `_comp` and `_coefficients` state
  identity, geometric-composition and finite-coefficient pasting for the published
  reflected comparison, in its inverse-beta orientation. The first two use complete
  inputs, the domain of the ambient completed pullback composition/id comparators;
  in particular they apply to every integral constructible input. The ambient scalar
  coefficient equation applies on every complex. The strict functors carry exactly
  these equations through their specified unit-compatible identifications.
- Already published ordinary coherence is reused, not restated, through
  `pbcScalarOperations_identity`, `pbcScalarOrdinaryPull_comp` and
  `pbcScalarOrdinaryPull_coefficients`. The specified raw scalar associator is
  `pbcRationalScalarComp`, whose components are the rationalizations of the same
  `pbcAmbientScalarComp` (`pbcRationalScalarCompComponent`).
  `pbcScalarCompletedPull_rational` uniquely characterizes descent by these exact
  localized integral components. Therefore the displayed integral pasting is with
  those specified raw associators, on all raw fractions, without adjoining retracts.
  These public imported declarations remain owned by prop-weil-pbc-scalar-extension
  and are not listed in this item's lean.declarations.

Dependency declarations read and reused (module → principal declarations):

- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses →
  SheafOfModules.cochainModulesMonoidal and the additive/colimit instances.
- Mathlib.Algebra.Homology.DerivedCategory.Basic → DerivedCategory, HasDerivedCategory, Q.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite → Padic.finite_coefficientExtensionRing;
  public CoefficientExtension supplies the valuation ring, quotients and chosen uniformizer.
- Sheaf.Paper.AdicCoefficientDatum → Scheme.completedReductionTower and coefficient limits.
- Sheaf.Paper.IntegralUniformCoefficient → Scheme.pbcBoundedConstructibleComplete;
  its published generic PbcBoundedConstructibleComplete is used with the lifted datum.
- Sheaf.Paper.PbcQbarCompletedPullback → pbcQbarCompletedPull and public
  PbcActualStrictPullback's pbcActualStrictCompletedPull, its unit, and its former
  complete-input comparison. Its proved node record is unchanged; the ambient
  comparison is an auxiliary theorem of the present item.
- Mathlib.AlgebraicGeometry.Sites.Proetale → Scheme.ProEt and ProEt.topology.
- Sheaf.Paper.PbcRationalCategory → PbcRationalCategory and pbcRationalization.
- Sheaf.CategoryTheory.RingedSiteModules → CategoryTheory.ringedSiteModules.
- Sheaf.Paper.RationalModuleRealizationFunctor → RationalModuleRealization,
  rationalModuleRealizationFunctor and its exact object/fraction normalization.
- Sheaf.Paper.RationalRealizationPullbackComparison → RationalPullIntegral.unit_isIso,
  RationalRealizationPullbackComparison and rationalRealizationPullbackComparison.
- Sheaf.Paper.FiniteFreeCompletedScalarComparison →
  WeilConjectures.finiteFreeCompletedScalarComparison and completedScalarRelativeDegree.
- Sheaf.Paper.ConstantCompletionEquivalence → ConstantCompletion.equivalence,
  koszul_quotient_reflector and the finite-reduction/unit comparisons.
- Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares →
  ReflectedCoefficient.Context, Change, Arrow, Square, Square.normalization and pasting.
- Sheaf.Paper.WeilCompletedTensorReflector → Scheme.wfCompletionReflector and its unit.
- Sheaf.Paper.RingedPushforwardCompletion → CategoryTheory.ringedPushforward_completion.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses →
  SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback;
  its public scheme specialization and PbcActualScalarPullback preserve representative
  normalization. pbcActualScalarDerivedPullIso_exists fixes the beta used here.
- Sheaf.Paper.PbcScalarExtension → pbcEmbeddingAmbientTensor, pbcScalarCoefficientMap,
  pbcScalarCompletionIso, pbcScalarOrdinaryPullIso, pbcScalarCompletedPullIso,
  pbcEmbeddingAmbientUnit, pbcAmbientScalarComp and the raw declarations listed above.
- Proof-only imports: FiniteFreeCompletionTransport.finiteFreeCompletionTransport and
  its identity/composition laws; FiniteFreeConstructibleScalarTransport;
  RingedDerivedMonoidalComparisons.ringedDerivedMonoidalComparisons;
  Padic.extension_integers_dvr; Mathlib's spectralNorm_unique_field_norm_ext.

Source checks: read algebraization.tex, lemma-derived-completion-koszul (0A0E),
lemma-pushforward-commutes-with-derived-completion (0A0G), and the source docstrings
of each recorded dependency. These are the item's source; no older blueprint
snapshot was used as the governing source.

Edge cases checked before and during drafting: E=L and i=id; positive ramification
indices e>1; zero/unbounded complexes; arbitrary g; empty schemes (the stalk
invertibility hypothesis is vacuous exactly as it should be there); all finite
quotient levels (n=0 in Lean means exponent one). Neither empty-scheme exclusion nor
completeness of ambient K is introduced. K-flat/flat-term hypotheses occur only in
the computation clause about representatives, not in the ambient theorem.

Searches:

- msearch.py leanfinder, query 'Finite coefficient scalar extension commutes with
  quotient tower completed pullback preserving actual units': eight hits, including
  RingHom.finite_isStableUnderBaseChange and ordinary AdicCompletion.ofTensorProduct
  results; none is the normalized unbounded sheaf-derived unit square.
- msearch.py loogle, queries 'SheafOfModules.changeOfRings, CategoryTheory.NatIso',
  'CategoryTheory.NatIso, CategoryTheory.Functor', and 'Functor, IsIso': zero results;
  the service reports unknown identifiers. These are recorded as inconclusive remote
  index searches, not evidence that the local declarations do not exist.
- msearch.py grep 'completion.*pullback|pullback.*completion' over Mathlib and
  'derived.*completion.*pullback|completion.*scalar|scalar.*completion' in
  Mathlib/CategoryTheory: zero hits for the derived coefficient unit square.
- rg on lean/WeilConjectures and lean/Sheaf for the item id and
  rationalScalarCompletion/rationalScalarStrictBeta/scalar-completion-unit patterns:
  no exact ambient statement. PbcScalarExtension supplies the reflected comparisons
  and coherence but its strict-tower identification is restricted to complete inputs.
  StrictScalarCompletionUnit treats restriction from completed to constant coefficients,
  not finite E-to-L scalar change with geometric pullback. The parent's
  RationalRealizationScalarCoherence has a constructible-input strict comparison,
  not an ambient one. All usable existing declarations were retained and reused.

Validation: scompile.py has compiled each delivered module separately in dependency
order against the live published build, including the repaired single library-named module. Only
expected 'declaration uses sorry' warnings are allowed. No global build or direct git
command was run. No STATEMENT-DISPUTED claim or source-statement correction is needed.

## Repair of return 383f88ea7027

- H13: removed the dependency-node replacement and its module
  Sheaf.Paper.CompletedPullbackAmbientUnit from the packet. The live
  def-weil-pbc-completed-pullback record (Q99, pbcQbarCompletedPull) is untouched,
  including its proof-review metadata. The item imports
  Sheaf.Paper.PbcQbarCompletedPullback directly. Moved
  pbcActualAmbientCompletedPullback_tower and pbcActualAmbientCompletedPullbackIso
  into RationalScalarCompletionUnitSquare.lean, before the coefficient section
  variables, and listed both in the item's lean.declarations. Their signatures,
  proof/data bodies and natural-language proof are unchanged; their blueprint
  docstrings now name this item's node. Their two proof-only imports moved with them.
  The ambient comparison is auxiliary to the item's all-ambient unit square; no
  proved dependency is rebound to a sorried theorem.
- H4/record: removed pbcScalarOperations_identity, pbcScalarOrdinaryPull_comp,
  pbcScalarOrdinaryPull_coefficients, pbcScalarCompletedPull_rational,
  pbcRationalScalarComp and pbcRationalScalarCompComponent from lean.declarations.
  They remain imported and are owned by prop-weil-pbc-scalar-extension. No copies
  or restatements were added.
- H11 advisory: the section below explicitly records an author's self-audit;
  independent maintainer review remains required. No other agent was started.

## Second reading by Q67

Author's second clause audit, under the dispatcher's instruction to work without
other agents; this does not claim an independent reader. Independent maintenance
review remains required. I reopened the node and the repaired Lean file and checked the
source/destination reversal (file X is node X'), left-to-right composition, kappa
orientation, the two distinct strict versus reflected units, and each hypothesis.
The audit caught the need for an ambient rather than complete-input tower comparison,
required explicit section types on the tensor-unit generators, and retained the
exact site object/Hom universes. It also added the explicit sheaf-section ramification
equality rather than leaving that consequence only in prose. Identity and tower
clauses use the actual published unitors, composition comparators and raw associators.

Repair self-check: compared the packet with the returned layout and the live
completed-pullback record. The only node delivered is the item, with only its lean
field changed. Its sixteen original declarations retain their complete text and
order; the two ambient helpers retain their signatures and bodies, with explicit
A/X/Y/u binders before the scalar section variables. All eighteen declarations in
the repaired module belong to this item, and each is listed in lean.declarations.
The six imported names removed from that list remain available through the original
scalar-extension import. Rechecked the primary signature verbatim against the node,
the actual strict-unit square, reflected formula and intermediate expression; no
hypothesis or mathematical conclusion changed. The empty-scheme, identity coefficient,
ramified, zero and unbounded-input cases in the original audit still apply.
