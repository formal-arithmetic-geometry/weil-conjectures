## Worker report

The module `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` states
`WeilConjectures.CounitExpressions.expressionCounitSubstitutionCoherence`.
Its sole theorem has proof `sorry`; every helper definition contains real data.
The DAG node changes only in `lean`. There are no new nodes, dependency repairs,
statement corrections, or disputed statements.

The source read is blueprint main-20261015 order 2232,
`sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md`,
its final coefficient-passage paragraph, together with the item's full explicit
15-step argument and both expression/primitive dependency statements.

Hypotheses and notions, clause by clause:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  Their recorded quotient rings, uniformizer and constant quotient sheaves are
  inherited from `CoefficientExtensionFinite` and the primitive comparison module.
  No alternate ring or independently chosen uniformizer is introduced.
- Schemes are `W : S → Scheme.{t}`. `_hl` states that l is a unit in every
  stalk, exactly invertibility of l on every scheme. The universe variables
  `t,u,s,i,j` are independent; the site retains object size t+1, morphism size t.
- Whole systems and limits use `coefficientSequenceDerived` and
  `coefficientSequenceLimit`, not inverse diagrams in a derived category.
  The latter is actual derived limit after termwise scalar restriction.
- `Data.reduction` is the recorded `CoefficientDerivedSystemReduction` at each
  scheme, including its actual quotient model and canonical derived adjunction.
  `Data.roos` and `Data.primitive` retain the recorded
  `PrimitiveCounit.RoosRealization` and `PrimitiveCounit.Comparisons`, including
  their representative characterizations, projection normalization, naturality
  and invertibility. These are presentations of the specified constructions,
  not arbitrary operation functors, counits, or comparison morphisms.
- `system` uses `(D.reduction a).systemClosed.tensor` for T and
  `PrimitiveCounit.pull l E f` for F. `unit` is Mathlib’s `SheafOfModules.unit` in degree zero on the
  actual ringed sequence site, i.e. B_n[0] with the quotient transitions.
- `completed` uses exactly `integralCompletedTensor`, `integralDerivedPullback`
  and the total limit of that unit. These are the original normalized
  quotient-complex/Roos descents, publicly reexported by the recorded slice module.
- `Normalization.unit`, `.tensor`, `.pullback` are exactly the stated closure
  assumptions on U,T,F. Input normalization occurs at every quantified family
  as `∀ k, IsNormalizedCoefficientSequence ... (N k)`. No boundedness,
  constructibility, finiteness or Tor-amplitude is imposed.
- The grammar is the dependency's `CompletedOperations.Expression`, with its
  existing `Expression.substitute`. `system` and `completed` are recursive
  functors on input families: input evaluation, constant units, pairing then
  tensor, and composition with pullback.
- `beta` is identity at inputs and units. At tensor it is completed tensor of
  the two child beta maps followed by `PrimitiveCounit.tensorBeta`; at pullback
  it is completed pullback of the child beta followed by
  `PrimitiveCounit.pullBeta`. Those primitive definitions are exactly quotient
  realization followed by L(T(e,e)) and L(F(e)).
- `gamma` is `(D.reduction a).reduction.map (beta ...)` followed by the actual
  adjunction counit at the system evaluation. It is a whole-system morphism.
- `EvaluationLaws.invertible` records the recursive invertibility established
  in proof step 2 (and gamma by normalized counit effectivity).
- `EvaluationLaws.naturality` gives both displayed input naturality equations.
  Lean composition `≫` runs left to right, reversing the node's written
  right-to-left multiplication. The first conjunct is K(Lv) ≫ beta' =
  beta ≫ L(S(v)); the second is R(K(Lv)) ≫ gamma' = gamma ≫ S(v).
- `systemSubstitution` and `completedSubstitution` are exactly d and c:
  recursive identity isomorphisms at leaves and images of child isomorphisms
  under tensor or pullback, preserving all parentheses.
- `EvaluationLaws.substitution` states beta_flat ≫ L(d) =
  c ≫ K(beta_H) ≫ beta_outer, and gamma_flat ≫ d =
  R(c ≫ K(beta_H)) ≫ gamma_outer. H is a simultaneously quantified family
  of correctly located expressions with a freely chosen new input context J.
- `Compatible` is the two structural equations. Its first conjunct is the
  commuting beta square, equivalent to the conjugation formula because beta_Q
  is invertible; its second is the actual gamma square in the system category.
- `StructuralLaws.identity`, `.composition`, `.inverse`, `.tensor`, `.pullback`
  explicitly state closure of both equations under those operations. Tensor
  allows both factors to vary, covering tensor with any fixed expression.
  Inverse is stated for invertible structural maps, exactly where inverses exist.
- `StructuralLaws.substitution` takes natural system and completed structural
  transformations compatible on normalized inputs and asserts compatibility
  after simultaneous substitution, using d/c conjugation for the flattened
  maps. Natural transformations are essential: their naturality at beta_H
  is precisely proof step 14. The final sentence about constraints and finite
  pullback compositors is conditional on their primitive equations and is
  covered by these universally quantified structural transformations; no
  additional equation for an unverified primitive constraint is assumed proved.

Dependency declarations used:

- `Sheaf.Paper.CompletedOperationExpressions`:
  `WeilConjectures.CompletedOperations.Expression`, `.Expression.substitute`.
- `Sheaf.Paper.CompletedPrimitiveCounitComparison`:
  `WeilConjectures.PrimitiveCounit.Comparisons`, `.RoosRealization`, `.pull`,
  `.tensorBeta`, `.pullBeta`. The `.tensor`, `.geometric`, model, counit and
  naturality fields were read in full. This module imports all the recorded
  coefficient, normalized-tower, scalar-reduction, semilinear, effectivity,
  independent-universe derived-limit and completed-operation dependencies.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.CoefficientDerivedSystemReduction`, its `.reduction`,
  `.adjunction`, `.systemClosed`; `coefficientSequenceLimit`,
  `coefficientSequenceDerived`, `IsNormalizedCoefficientSequence` from the
  reexported coefficient ringed sequence interface.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` reexports the original
  `WeilConjectures.integralCompletedTensor`, `.integralDerivedPullback`:
  their original global quotient/Roos realizations are the primitive lemma's
  actual operations. The enlarged slice interface is not needed here.
- Mathlib’s `SheafOfModules.unit`, `HomologicalComplex.single` and
  `DerivedCategory.Q` construct the actual coefficient system in degree zero.
  The first dry run rejected the optional RingedSiteDualityMaps import because
  it belongs to a retired route. Removed that import and used these existing
  Mathlib constructions directly, with the identical coefficient-unit data.
- `Mathlib.CategoryTheory.Pi.Basic`: `CategoryTheory.Pi.eval`, the category
  of dependent input families. All universes and variables are bound explicitly.
- `def-weil-scheme-morphism-properties` is a convention node, not a declaration.
  Its invertibility condition is explicitly represented by `_hl`.

Edge cases checked before drafting: no scheme locations (no output expressions),
empty input context (unit-only expressions remain), input leaves, unit leaves,
repeated input in tensor(i,i), identity scheme maps, arbitrary finite nesting,
zero inputs and empty schemes. No Nonempty or finite context assumptions occur.
Positive coefficient index n means exponent n+1 throughout the dependencies;
there is no missing exponent-one case or extra flatness hypothesis.

Searches actually run:

- `msearch.py ... leanfinder`: “Naturality and simultaneous substitution
  coherence of recursively defined comparison maps between evaluations of
  typed tensor and pullback expressions”: 8 hits, including free-monoidal
  normalization and polynomial substitution, no exact coefficient-system theorem.
- `msearch.py ... loogle 'NatTrans.naturality, Functor.map_comp'`: 0 hits,
  service returned unknown identifier NatTrans.naturality; not claimed as an
  exhaustive no-match result.
- `msearch.py ... grep 'substitut.*[Cc]oher|[Cc]ounit.*[Ss]ubstitut'
  CategoryTheory`: 0 hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf/Paper` for substitution,
  counit coherence and expression comparison: found the existing parent
  `CompletedOperationTowerSubstitution` and unrelated scalar/polynomial results.
  Read the entire parent module. Its existing evaluator requires its stronger
  `CompletedOperations.Models` interface (full duality presentations, completion
  unit and a distinct pullback-realization interface), rather than the recorded
  primitive comparison data. Its result is existential in those Models, omits
  gamma input naturality and the explicit closure law for arbitrary natural
  structural transformations, and therefore is not an exact existing match.
  The new helpers evaluate the primitive lemma's supplied interfaces directly;
  they neither redefine its operations nor require the downstream parent theorem.
- `grep -rn 'lem-pur-expression-counit-substitution-coherence'
  lean/WeilConjectures`: 0 hits.
- `rg 'expressionCounitSubstitutionCoherence|CounitExpressions'` on
  Mathlib, `dag/lean_names_upstream.json`, upstream and project Lean: 0 hits
  before delivery; the chosen public names do not collide.

Validation: prescribed `scompile.py O2 ...` succeeded for the sandbox source
and its library module name (14.5 s and 18.1 s respectively), with no errors or
warnings. The module has one sorry, solely the named theorem proof, with the
complete 15-step natural-language proof and blueprint marker in its docstring.

Additional searches: `msearch.py leansearch` for recursive natural transformations
and simultaneous typed tensor/pullback substitution returned 8 hits (NatTrans and
monoidal naturality/recursors, no exact theorem). A corrected fully qualified
`loogle CategoryTheory.NatTrans.naturality` query returned 9 hits including the
ordinary naturality square, no typed coefficient-system substitution theorem.

After the import repair, the final source compiled cleanly again under both names
(sandbox 10.8 s, library 10.1 s). All lines are at most 100 characters; there is
exactly one sorry token, the named main theorem proof. The main signature and
lean.declarations remain unchanged by the unit-construction import repair.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
