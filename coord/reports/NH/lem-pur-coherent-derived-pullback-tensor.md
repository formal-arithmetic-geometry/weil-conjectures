## Worker report

Attach the exact existing theorem
`WeilConjectures.pullbackTensorSystemComparison_existsUnique`, in
`Sheaf.Paper.CompletedPullbackTowerRealizations`, source lines 414–439. No new Lean
module is written: the one-definition rule requires reusing this declaration.
The theorem's proof is still `sorry`; this delivery records a statement, not a proof.
Only the item's `lean` field changes. No new nodes, dependency repairs, or statement
correction are needed.

Read the complete item, its statement dependencies and their records, the existing
theorem and enclosing section, and the definitions of its named constructions.
Read Stacks `sites-cohomology.tex`, labels `lemma-K-flat-resolution` (06YS),
`definition-derived-tor` (06YU), and `lemma-pullback-tensor-product` (07A4).
The latter proves the derived pullback/tensor isomorphism by flat-term K-flat
representatives. The item's all-K-flat normalization and uniqueness are its
explicit project-specific refinement. The current blueprint association
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md`
was read; it concerns compatibility with finite reduction and scalar extension.
This item is an extracted obligation, not that unit's full statement.

Hypotheses and clauses, matched to the existing Lean:

- Prime and coefficients: the enclosing section explicitly binds `(l : ℕ)` with
  `[Fact l.Prime]`, `(E : Type u)`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]`. The coefficient extension constructions fix
  the valuation ring, uniformizer, quotient rings and actual quotient maps.
- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)` are unrestricted.
- The ringed sequence site and its module category are
  `coefficientSequenceTopology (ProEt.topology W)`,
  `coefficientSequenceCommRingSheaf l E W`, and
  `coefficientSequenceModules l E W`. Its n-th level is the exponent n+1 quotient.
  `coefficientSequenceDerived` is its ordinary unbounded derived category;
  complexes are `CochainComplex ... ℤ` and localization is `DerivedCategory.Q`.
- Exact evaluation, simultaneous scalar restriction and the reduction/limit
  adjunction are the previously fixed constructions in
  `CoefficientRingedSequenceSite` and `CoefDerivedSystemEvaluationCalculus`.
  The chosen calculus is `pullbackTensorCalculus l E W`; its `systemClosed.tensor`
  and `systemTensorModel` supply exactly the specified tensor and model. These
  contextual constructions are not additional hypotheses on P or Q.
- Base change is `pullbackTensorSequenceBase f`, defined as
  `(𝟭 ℕ).prod (proEtaleBaseChange f)`. Its ring map is
  `pullbackTensorSequenceRing`, characterized by the actual constant-section map
  in `pullbackTensorSequenceRing_existsUnique`. The direct image is
  `pullbackTensorSequenceDirect`; its fixed left adjoint and unit come from
  `pullbackTensorSequenceInverse` and `pullbackTensorSequenceAdjunction`.
  The core module proves its identification with the recorded
  `integralComparisonSequencePullback` when proving exactness.
- The contextual finite adjunction and inverse mate are retained by
  `pullbackTensorSequenceInverseEvaluation_existsUnique`: its displayed
  Hom-adjunction equation uses the actual sequence unit and direct/evaluation
  comparison. The latter is the identity on underlying sections.
- `D_f` is `pullbackTensorSequenceDerived l E f`, defined as the exact functor's
  `mapDerivedCategory`. The cochain functor is its `mapHomologicalComplex (.up ℤ)`.
  `delta_P` is exactly its `mapDerivedCategoryFactors.hom.app P`; it is directed
  from derived inverse image of Q(P) to Q of termwise inverse image.
- The asserted natural isomorphism is the binder `∃! e : ... ≅ ...` between
  `systemClosed.tensor ⋙ pullbackTensorSequenceDerived` and
  `pullbackTensorSequenceDerived.prod pullbackTensorSequenceDerived ⋙
  systemClosed.tensor`. Thus naturality, invertibility and uniqueness concern
  the complete bifunctors on derived sequence systems.
- Every K-flat pair is quantified as `∀ (P Q : CochainComplex ... ℤ) (hP : ...)
  (hQ : ...)`. The predicates are exactly
  `CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}` on the actual
  site `ℕ × Y.ProEt`, with its specified `pullbackTensorSequenceSmall Y` instance.
  The definition tests total tensor against every acyclic complex.
- `tau_W(P,Q)` is `pullbackTensorSystemModel l E W P Q hP hQ`, which is literally
  `CoefficientTensorModels.iso` for the chosen calculus tensor model.
  `z_f` is `pullbackTensorSequenceCochain l E f`, the uniquely pure-tensor/unit
  normalized cochain comparison already stated by the cochain dependency.
- The left side of the equation is written in Lean's composition order:
  `D_f.map tau_Y.hom ≫ e.hom.app (Q.obj P, Q.obj Q) ≫ tensor_X.map
  (Prod.mkHom delta_P delta_Q)`. This is exactly the displayed mathematical
  `(delta_P tensor delta_Q) ∘ zeta ∘ D_f(tau_Y)`.
- The right side is `delta_Tot ≫ DerivedCategory.Q.map z_f.hom ≫ tau_X.hom`.
  Its two K-flat arguments are supplied by `pullbackTensorSequenceGood` applied
  to hP and hQ. This is exactly `tau_X ∘ q_X(z_f) ∘ delta_Tot`.
  Both sides live in `coefficientSequenceDerived l E X`, before any inverse
  limit, and have the source and target specified in the node.
- No termwise flatness, boundedness, completeness, normalized-system,
  constructibility or invertibility-of-l assumption occurs in this theorem.
  Flat-term good integral complexes occur only in its explanatory context.

Dependency declarations read and used (names below are fully qualified by the
indicated namespace):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the imported
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and
  `coefficientExtensionRing` constructions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `WeilConjectures.coefficientSequenceCommRingSheaf`,
  `coefficientSequenceModules`, `coefficientSequenceDerived`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus` and its
  `CoefficientDerivedSystemCalculus`, with `systemClosed` and `systemTensorModel`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift` (and its Bifunctor import):
  `HomologicalComplex.mapBifunctor`; its recorded tensor specialization is the
  same signed direct-sum totalization used by `coefficientTotalTensor`.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`:
  `WeilConjectures.integralComparisonDerivedSequencePullback`,
  `integralComparisonSequencePullback`, and its exactness theorem.
- `Sheaf.Paper.CompletedPullbackTowerRealizations`:
  `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`,
  `pullbackTensorSequenceCochain`, `pullbackTensorSequenceGood`,
  `pullbackTensorSystemModel` and the attached theorem itself.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.CoefficientClosedStructure.tensor`, `coefficientTotalTensor`,
  `CoefficientTensorModels`, and `CoefficientTensorModels.iso`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, the recorded Mathlib
  proof dependency, fixes the exact-derived comparison used in the square.

The existing proof dependency `SheafOfModules.cochain_tensor_model_rigidity`
(module `Sheaf.Algebra.Homology.CochainTensorModelRigidity`) supplies full
faithfulness on flat-term K-flat representatives, and
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`
(module `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`)
supplies the resolutions used to extend the square to every K-flat pair. The
accepted node's five-step proof remains unchanged: conjugate the prescribed
models, descend using fullness, prove inverse identities using faithfulness,
compare arbitrary K-flat pairs with resolving pairs, and use faithfulness for
uniqueness. No additional proof imports are written for an existing attachment.

Edge cases checked by reading the complete binders and constructions: identity
f, empty schemes, zero complexes, complexes in a single degree, unbounded
K-flat complexes without flat terms, and schemes where l is not invertible.
All remain within the theorem; no positivity, nonemptiness or boundedness
binder excludes them. The sequence starts at exponent one, not the zero ring
at exponent zero. Independent object/morphism sizes are preserved explicitly.

Searches actually run for this delivery:

- `msearch.py ... leanfinder`, query: "The derived tensor pullback comparison on
  coherent sequence module sheaves is uniquely normalized on all K-flat pairs by
  the cochain tensor comparison and exact-derived factorization". Eight hits,
  including `SheafOfModules.pullbackObjFreeIso`, unit/pullback formulas, `Tor'_map_app`
  and `Module.Flat.rTensor_shortComplex_exact`; none is this exact theorem.
- `msearch.py ... loogle`, query:
  `CategoryTheory.Functor.mapDerivedCategoryFactors`. Twelve hits, including that
  factorization and its shift/naturality statements, not this sequence theorem.
- `msearch.py ... grep`, query:
  `pullback.*[Tt]ensor|[Tt]ensor.*pullback|mapDerivedCategoryFactors`. Twenty-one
  Mathlib hits: exact-derived factorization, scheme pullback-carrier calculations,
  and categorical tensor constructions; no exact theorem.
- `msearch.py ... leansearch`, query: "Exact inverse image of coherent sequence
  module sheaves commutes with derived tensor uniquely normalized on all K-flat
  pairs". Eight hits: flat module tensor exactness and sheaf pushforward
  isomorphisms; no exact theorem.
- `rg -n 'pullbackTensorSystemComparison_existsUnique|coherent-derived-pullback-tensor'
  lean/WeilConjectures lean/Sheaf`: exact declaration at line 414, canonical choice
  at line 444, and consumers in `CompletedPullbackTensorSignedRepresentatives`
  and `IntegralSystemTensorComposition`; no upstream duplicate.
- `grep -rn 'lem-pur-coherent-derived-pullback-tensor' lean/WeilConjectures`: no hit.
- Read the dependency definitions with targeted `rg` and `sed`, including
  `CompletedPullbackTowerCore` lines 256–400 and 672–728, which fix the actual
  adjunctions and their evaluation mate.

No mathematical statement fault or STATEMENT-DISPUTED issue was found. There is
an inherited bibliographic imprecision: Tag 0941 is cited as the sequence-site
construction although its label is `lemma-derived-limit-is-ok` (also noted in
the existing stage-1 review). This does not change the explicit sequence-site
construction or this extracted theorem. No provenance field was edited.

## Second reading by NH

A second pass by the assigned worker (no subagents are permitted by the dispatch
brief) compared the open node with the open existing theorem, independently of
the signature extraction. The section supplies exactly the prime/finite-extension
binders. The result is a unique natural isomorphism of derived-system bifunctors,
not a family of finite-level maps. Both P and Q have only the independent-universe
K-flat predicate. Reading each composite in order confirms delta on the tensor
factors occurs on the left-hand route and delta on Tot occurs on the right-hand
route, with the prescribed cochain z and calculus tau between them. There is no
application of Rlim. The fixed unit and inverse mate were checked in the core
module, rather than replaced by isomorphic but unspecified constructions. The
node and theorem agree clause by clause; no mismatch required a change. The
maintainer's independent review remains separate from this self-check.
