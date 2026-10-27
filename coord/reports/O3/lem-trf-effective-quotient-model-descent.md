## Worker report

Module: `Sheaf.Paper.EffectiveQuotientModelDescent`. The five named theorems state the
five parts of this one DAG node; each proof is `sorry`. No new construction, axiom,
private copy, helper definition, node, or statement correction is introduced.

Hypotheses and objects:
- The prime is `l : ℕ` with `[Fact l.Prime]`. Finite coefficient fields use
  `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`, and similarly L and M.
  `ι : E →ₐ[ℚ_[l]] L` and `j : L →ₐ[ℚ_[l]] M` render inclusions, with the composite
  `j.comp ι`. No inequality or distinctness excludes E=L, L=M, or E=L=M.
  The imported Padic coefficient constructors supply the actual integer rings,
  uniformizers, positive-exponent quotients, and quotient maps.
- `X Y W : Scheme` and `f : X ⟶ Y` impose no finite type, separatedness, properness,
  Tor-dimension, or cohomological restrictions. Invertibility of l is the pointwise
  `IsUnit (l : X.residueField x)`, or the equivalent `Invertible` instance convention
  in the constructible and simultaneous clauses. These concern the same schemes.
- The ambient declarations retain independent universes t and u. As in the recorded
  sfIntegralConstructible interface, constructibility is expressed at one common
  bound u for coefficients and schemes. This does not equate the small site's
  object and morphism universes: these remain u+1 and u. Any finite collection of
  coefficient fields and schemes has a common universe bound. No arbitrary smaller
  test universe or bound on cohomological degrees is introduced.
- `scalarReductionSource` is modules over the actual completed coefficient sheaf,
  not the discrete constant ring. `DerivedCategory` is the ordinary unbounded
  localization. `coefficientSequenceDerived` retains the entire strict quotient
  diagram; `SY`, `SX`, `SL` are the specified evaluation-calculus adjunctions.
  The realization is `coefficientSequenceLimit`, and the arrows are the actual
  `S.adjunction.unit` and `.counit`. `ρX`, `ρL` are the recorded K-injective-normalized
  `IntegralComparisonRoosModel` interfaces. Natural number n always means exponent n+1.

Clause-by-clause rendering:
1. `effectiveQuotientModelDescent` quantifies over EVERY ambient K and states
   `IsNormalizedCoefficientSequence` for its reduction, its whole-system pullback,
   and its whole-system scalar extension. This predicate is the recorded canonical
   transition-adjoint invertibility for all m≥n, including m=n; it is not a property
   of an arbitrarily chosen comparison map.
2. Its next two conjuncts are `IntegralOnSlice.IsComplete ... none` for the two
   realizations; the following two are `IsIso` of the actual entire system counits.
   Its last ambient implication gives `IsIso (SY.adjunction.unit.app K)` exactly
   when the input is derived complete. K need not be constructible, bounded, or
   complete for the other assertions. The normalization/projection computation
   is the imported RoosAdjunctionQuotientNormalization, not a replacement unit.
3. The final two conjuncts give the existing `IntegralComparisonPullbackModel` and
   `IntegralComparisonScalarModel` with the SAME fixed system and Roos models.
   Their `realization` fields are natural α and β on ambient categories. Their
   `normalization` fields quantify over every good P, simultaneous quotient C,
   derived presentation e and every quotient identification κ, with actual unit
   and balanced-generator equations. Pullback is precisely rho on its tower;
   scalar change is rho after inverse strict association. No new realization map
   or levelwise stand-in is introduced.
4. `effectiveQuotientModelConstructible` assumes `sfIntegralConstructible ... K`.
   Its four conjuncts put completed pullback, completed scalar extension, and both
   system realizations in the required integral constructible categories. The
   published predicate is exactly completeness plus `∃ a b, a≤b ∧ ∀ n, ...` with
   intrinsic constructible reductions and support contained in `Set.Icc a b`.
   Thus one interval works for EVERY positive level, not a different bound per n.
5. `effectiveQuotientModelRepresentativeDescent` first states quasi-isomorphism
   invariance of both Roos-complex functors between flat-term K-flat inputs.
   The next two conjuncts are the unique functor isomorphisms compatible with
   the published good-representative comparisons. They express independence of
   every resolution choice and agreement on common refinements, not mere
   objectwise existence of some isomorphism.
6. Its next two equations state α/β naturality for every derived morphism. The
   next four conjuncts identify any other normalized α, β, or Roos comparison
   with the fixed one. The two existential clauses descend the Roos construction
   to the derived category of WHOLE restricted towers with a natural κ and ρ,
   fixing κ·ρ to the inverse recorded normalized comparison. Uniqueness is for
   that prescribed κ, so no arbitrary natural automorphism is called canonical.
   The final equality is counit naturality on WHOLE strict quotient systems.
   Together with the imported formula for every K-injective resolution, this
   says a second resolution computes the same counit morphism before evaluation.
7. `effectiveQuotientModelScalarCoherence` uses actual `j.comp ι` and the recorded
   strict `integralComparisonSequenceScalarComposition`. Its first equation says
   the two universal cochain counits and the strict generator associator descend
   to the derived associator. Its second equation fixes the identity inclusion
   by `integralComparisonSequenceScalarUnit`, which multiplies s and x. Neither
   equation mistakes identity completed scalar change for identity on ambient K.
   All objects and arrows are whole sequence-site objects; thus quotient transitions
   are retained. Their generator and quotient-transition identities were read in
   the primitive module, including its finite scalar triple and unit theorems.
8. `effectiveQuotientModelsSimultaneous` gives one system calculus and one normalized
   Roos model for every field and scheme, then primitive pullback and scalar models
   for every map and every inclusion using those same families. All fields in a
   triple are instances of these universal families. The preceding all-model
   assertions therefore apply simultaneously and retain the exact normalization
   of def-trf-integral-comparison-realization-models.
9. There is no flatness, unramifiedness, or finite Tor-bound assumption on finite
   quotient coefficient maps anywhere in the file.

Dependency interfaces read and used (all under namespace WeilConjectures unless noted):
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: convention-only record; universes and scheme-property binders are explicit.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale` / `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: convention-only record; universes and scheme-property binders are explicit.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` / `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic` / `DerivedCategory`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` / `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-trf-integral-comparison-sequence-systems`: `Sheaf.Paper.IntegralComparisonSequenceSystems` / `WeilConjectures.integralComparisonDerivedSequencePullback`.
- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperationsOnSlices` / `WeilConjectures.IntegralOnSlice.completedTensor`.
- `def-weil-integral-scalar-extension`: `Sheaf.Paper.IntegralScalarExtensionUniverses` / `WeilConjectures.integralScalarExtensionOfUniverses`.
- `def-coef-normalized-dvr-tower`: `Sheaf.Paper.NormalizedDVRTower` / `WeilConjectures.NormalizedDVRTower`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible` / `WeilConjectures.sfIntegralConstructible`.
- `lem-trf-roos-adjunction-quotient-normalization`: `Sheaf.Paper.RoosAdjunctionQuotientNormalization` / `WeilConjectures.roosAdjunctionQuotientNormalization`.
- `lem-trf-primitive-quotient-realization-comparisons`: `Sheaf.Paper.PrimitiveQuotientRealizationComparisons` / `WeilConjectures.primitiveQuotientRealizationComparisons`.
- `def-trf-integral-comparison-realization-models`: `Sheaf.Paper.IntegralComparisonRealizationModels` / `WeilConjectures.IntegralComparisonPullbackModel`.
- `lem-pur-coefficient-extension-reduction-model`: `Sheaf.Paper.CoefficientExtensionReductionModel` / `WeilConjectures.coefficientExtensionReductionModel`.
- `lem-pur-integral-operations-preserve-constructible`: `Sheaf.Paper.IntegralOperationsPreserveConstructible` / `WeilConjectures.integralOperations_preserve_constructible`.
- `lem-pur-integral-operations-well-defined`: `Sheaf.Paper.IntegralOperationsWellDefined` / `WeilConjectures.integralOperationsWellDefined`.
- `lem-pur-normalized-actual-reconstruction-maps`: `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` / `WeilConjectures.purNormalizedReconstruction`.
- `lem-pur-system-normalized-tensor-closure`: `Sheaf.Paper.SystemNormalizedTensorClosure` / `WeilConjectures.SemilinearSections.normalized_tensor_closure`.
- `lem-weil-integral-scalar-extension-constructible`: `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` / `WeilConjectures.sfIntegralScalarExtension_constructible`.
- `lem-weil-integral-scalar-extension-well-defined`: `Sheaf.Paper.IntegralScalarExtensionWellDefined` / `WeilConjectures.integralScalarExtensionWellDefined`.
- `lem-weil-proetale-countable-products-exact`: `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` / `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`.
- `lem-weil-strict-roos-comparison`: `Sheaf.CategoryTheory.StrictRoosComparison` / `CategoryTheory.strictRoosComparison`.
- `prop-weil-pbc-proetale-constant-exact`: `Sheaf.AlgebraicGeometry.ProEtaleConstantExact` / `AlgebraicGeometry.ProEtale.finiteCoefficientModulePullback_exact`.

Additional public import `Sheaf.Paper.DerivedCompleteOnSlices` exposes the already
recorded `IntegralOnSlice.IsComplete` used by the reconstruction theorem. It is
not a new notion; its global case is `IsDerivedCompleteUnrestricted`. No dependency
record needs a repair. All recorded statement modules and stated proof modules
are imported with their required visibility. The parent EffectiveComparisonRealizationModels
module is deliberately not imported: it is a downstream consumer of this node.

Searches:
- msearch LeanFinder: "Normalized quotient system effectivity and natural descent of
  pullback and scalar realization comparisons": 8 hits, effective epimorphism,
  profinite-presentation and refinement results, none about these quotient systems.
- msearch Loogle: "CategoryTheory.Adjunction, CategoryTheory.IsIso": 12 hits,
  including Adjunction.toEquivalence and full-faithfulness criteria; no match.
- msearch grep: "normalized.*counit|counit.*normalized": 0 Mathlib hits.
- msearch LeanSearch: "Normalized derived quotient module systems have complete
  realizations with invertible adjunction counits": 8 hits, general derived
  adjunction and discrete condensed counit statements, none the present assertion.
- rg on lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `lem-trf-effective-quotient-model-descent|effectiveQuotientModel|effective.*[Rr]ealization`:
  no declaration for this item. The existing parent has only constructible-input
  effectivity; the primitive theorem has only model existence. Neither states this
  node's ambient effectivity together with representative and scalar descent.
  The new declaration names do not occur in the upstream index or Mathlib.

Sources checked locally: sites-cohomology.tex lemma-derived-limit-is-ok (0941),
including the K-injective tower/ordinary-limit computation, and lemma-K-flat-resolution
(06YS); literature/blueprint/latest/blueprint/sec-trace-formula/sk-thm-tf-uniform-formula/
sk-thm-tf-uniform-formula.proof.md, integral transport paragraph. This is the assembly
specified by the node, not claimed to be a verbatim Stacks theorem.

Edge cases checked before writing and again against the signatures: K=0; empty X
or Y; unbounded and noncomplete K; f=id; E=L and all three fields equal; m=n;
first quotient exponent 1; ramified E→L. Nothing requires finite Tor-amplitude of
A_E,n→A_L,n. Normalization concerns derived extension even when that map is nonflat.
The constructible predicate includes the empty scheme (an empty stratum can cover it).
No STATEMENT-DISPUTED issue or source correction was found.

Validation: scompile.py passed both the sandbox and library module-mode checks
(14.3 s and 19.8 s), with no errors or non-sorry warnings. Five theorem proofs
are postponed; all have source and node proof plans in their docstrings.

## Second reading by O3

This dispatcher worker reread the node, the five signatures, the model structures
and their normalization predicates after compilation. This is a self-check; an
independent reader was not started, as the dispatcher explicitly prohibits other
agents and says the maintainer will independently review the delivery.
The first pass exposed that merely citing the parent would omit arbitrary ambient
K. The written ambient theorem restores that quantifier. A later pass made whole-tower
Roos descent and comparison-preserving uniqueness explicit, and added the simultaneous
families. The four constructibility conjuncts were checked against the actual
single-interval predicate. Triple and identity scalar formulas use the fixed strict
associator/unit and universal counits, keeping all transitions. Site sizes remain
unchanged; no additional quotient-map hypothesis or theorem proof was added.
