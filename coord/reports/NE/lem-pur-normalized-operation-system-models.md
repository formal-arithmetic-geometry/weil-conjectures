## Worker report

Item: `lem-pur-normalized-operation-system-models`. Group NE, stage 2, 2026-10-21.
The module is `Sheaf.Paper.NormalizedOperationSystemModels`, with main theorem
`WeilConjectures.NormalizedOperations.normalizedOperationSystemModels`.
It states the node with one postponed theorem and fully written helper definitions.
No definition contains sorry, no theorem is proved, and no statement is corrected.
The helper structures collect the clauses of this node, rather than introducing a
second coefficient system, derived tensor, scalar adjunction, or flatness notion.

### Hypotheses and objects

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded coefficient
  construction supplies its valuation ring, uniformizer and quotient homomorphisms;
  none of these is replaced by a freely chosen ring or map.
- `W : Scheme.{t}` and `_hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w)` express
  the scheme and invertibility hypothesis. Every geometric source `X` has the same
  explicit stalkwise invertibility hypothesis. The theorem is universal in W, so
  the node's arbitrary target Y is W after renaming.
- `integralCoefficientCommRingSheaf l E W n` is the ACTUAL constant sheaf of the
  quotient by the `(n+1)`st uniformizer power. Thus Lean's n=0 is paper level 1;
  no level-zero quotient is introduced. `coefficientSequenceCommRingTransition`
  gives the actual adjacent quotient maps. The completed coefficient object remains
  the recorded inverse limit; no assertion here changes it or tensors over it.
- `Calculus`, `Whole`, `WholeModules`, `WholeRing` and `level` are abbreviations for
  the existing `SemilinearDerivedSectionsData`, `DS`, `Systems`, `systemRing` and `e`.
  These are the ordinary unbounded localization of modules on the sequence site.
  `(A : Calculus l E W)` supplies the existing operation realization; the theorem
  is universal in it and does not assume the desired preservation results.
- Normalization uses the existing `SemilinearSections.Normalized` predicate, meaning
  `IsIso` for the adjoint of every ACTUAL horizontal transition. This is the
  adjunction formulation of `def-coef-normalized-dvr-tower`, whose recorded
  `NormalizedDVRTower` uses the equivalent universal Hom property. Its extra global
  finite-field data and R-linear tower encoding are not imposed on the present
  arbitrary scheme or used as a substitute for the node's semilinear-system object.
- The site has object universe t+1 and morphism universe t; coefficients and modules
  have universe `max u (t+1)`. The geometric aliases use the generic canonical site
  pullback at that value universe, rather than the convenience API fixing it to t+1.

### Clause-by-clause rendering

1. Whole-system tensor is `A.systems.closed.tensor`; its finite evaluations are
   `A.systems.tensorEvaluation`. `OperationTensorLaws.normalized` states preservation
   for any two normalized whole-system objects. `transition` identifies its actual
   reduction with `scalarTensor.hom` followed by the tensor of the two input
   reductions, with exactly the evaluation comparisons needed to type the equation.
2. `OperationTensorLaws.input_factor` is the actual input transition equation:
   `derivedTransition = adjunction.unit ≫ resD.map reduction`. It retains the given
   transition, including any noncanonical sign or scalar twist. The unit is only
   the insertion step in this factorization.
3. `OperationTensorLaws.pure` gives the ordinary adjoint on sections:
   the scalar b times `(a tensor x) tensor 1` is sent to
   `transition(a) tensor b • transition(x)`. `scalarExtensionSection` is the existing
   adjunction-unit section; multiplication by b supplies the arbitrary last scalar.
   Its M and N are flat modules on the sequence site, expressed using the existing
   `flatTerms` on their degree-zero complexes; zero terms add no condition. Thus it
   applies termwise to the simultaneous flat representatives required by the node.
4. `OperationTensorLaws.cochain` is the tensor reduction equality for whole-system
   complexes and actual cochain maps, using `scalarTensorModel`,
   `tensorEvaluationModel` and `cochainReduction`. It uses the existing landed
   `cochain_tensor_reduction` interface, not a new evaluation-only tensor operation.
5. `OperationTensorLaws.cocycle` compares successive output adjoints with direct
   reduction through the existing adjunction-normalized `scalarComposition`.
   The underlying strict systems are modules on the sequence site; identity and
   quotient composition for their actual horizontal maps are already functor laws.
   The existing calculus fixes the scalar composition by its adjunction transpose.
   Thus equal indices and all input cocycles are retained, rather than postulated
   for a new family of unrelated maps.
6. Geometric inverse image uses the actual base-change functor of the small
   pro-etale sites, its sheaf inverse/direct image and its canonical adjunction.
   `HasOperationSystemModels` quantifies over every source X and morphism f and
   supplies a `Geometry` for these fixed functors. `CoefficientsIdentified` identifies
   its coefficients with the actual sheaves on X and its transition maps with their
   quotients, and fixes its ring isomorphism by the transpose of `coefficientDirect`.
   The latter is constructed by sheafification of constant sections, not chosen
   from mere existence or supplied as an arbitrary extra hypothesis.
7. `OperationPullLaws.normalized` states geometric preservation of normalization.
   `transition` is precisely the existing `Geometry.PullTransitionFormula`: the
   output adjoint is inverse coefficient association followed by geometric pullback
   of the input adjoint. `Geometry.coefficientPullback_transpose` fixes the derived
   association by the scalar adjunction units and the restriction comparison.
8. `OperationPullLaws.ordinary_scalar` supplies the ordinary association isomorphism
   BEFORE localization. Its inverse's adjunction transpose is geometric pullback of
   the ordinary scalar unit, followed by `restrictionPullback`. This uniquely fixes
   the insertion of 1 in the intermediate factor. Its second equation identifies
   the ACTUAL ordinary pulled-system reduction with this inverse association and
   pullback of the original ordinary reduction. Hence it does not replace an input
   transition with a canonical scalar unit.
9. `OperationPullLaws.scalar_cocycle` equates both association composites for three
   indices. `cocycle` then equates successive actual output adjoints and the direct
   one. The ordinary association is fixed by the preceding unique adjunction
   transpose; its triple-index equality is the associativity of scalar insertion
   and multiplication. The strict whole-system pullback already retains the
   horizontal cocycles, before passing to evaluated derived objects. These
   equations do not infer equality of whole-system derived maps from evaluation.
10. `operationUnitComplex` is the degree-zero regular module of the ACTUAL sequence
    site ring, with its actual quotient transitions. `operationUnit` localizes it.
    `OperationUnitLaws.normalized` and `transition` say that its derived and cochain
    adjoints are invertible. `multiplication` spells out `s tensor b ↦ q(s)*b`.
    `kflat` and `flat` give the unit base case among model representatives.
11. `OperationModelLaws.resolution` chooses ONE quasi-isomorphic whole-system
    complex P, flat-term K-flat on the sequence site, with flat-term K-flat
    evaluations at every level. This choice retains all transitions and cocycles.
    It is not a list of independently chosen level resolutions.
12. `OperationModelLaws.evaluation` permits evaluation of every later good whole
    representative. `tensor` and `level_tensor` give closure under the existing
    direct-sum `totalTensor`; `quotient` gives closure under actual termwise scalar
    extension. Its `IsIso operationScalarCounit` is the universal derived-to-ordinary
    comparison, so these are computations of the specified derived operations.
13. `OperationPullLaws.whole_model` and `level_model` give closure under actual
    termwise geometric inverse image. Exact inverse image has its existing
    canonical localization comparison. The corresponding model laws hold on X as
    well as W, as explicit concluding conjuncts of `HasOperationSystemModels`.
14. Resolution plus the unit case and the unary/binary closure clauses is the
    constructor-by-constructor formulation of every finite well-typed iterated
    expression. Structural induction keeps the originally selected representatives
    for all leaves and uses ordinary total tensor or termwise pullback at vertices.
    No new resolution is taken at a vertex. All complexes are indexed by ℤ with no
    lower or upper bound, and no flatness of a quotient map is an assumption.

### Dependencies used

The recorded signatures and docstrings were read. Public statement dependencies:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing`, the recorded actual finite quotient construction.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralCoefficientCommRingSheaf`, `coefficientSequenceCommRingTransition` and
  `integralConstantToCompletionOfUniverses`, retaining independent site sizes.
- `Sheaf.Paper.SemilinearDerivedSections` and its public calculus/model/geometry
  modules: `SemilinearDerivedSectionsData`, `Data`, `Geometry`, `Systems`, `DS`,
  `e`, `evaluation`, `reduction`, `Normalized`, `ScalarData`, `totalTensor`,
  `ordinaryTensor`, `scalarExtensionSection`, and the representative comparisons.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, its actual scalar
  restriction and universal adjunction formulation of normalization.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`.
- `Sheaf.Paper.SystemCochainTensorReduction`: `cochainReduction`,
  `cochainReduction_eq_transpose`, `cochain_tensor_reduction`; its public ordinary
  reduction module supplies `ordinaryReduction` and `ordinaryEvaluationTensor`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleBaseChange`
  and its continuity and finite-limit instances. The generic sheaf pullback and
  adjunction are the same construction as the recorded convenience declarations.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`; existing `flatTerms` packages it degreewise.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, used
  by the existing total tensor, with direct sums on p+q=n and the cochain signs.
- `def-weil-scheme-morphism-properties` is the recorded convention node; it has no
  new declaration to import.

The proof plan imports every recorded proof-dependency module: KFlatResolutionIndependentCoefficients,
SystemEvaluationKFlat, SemilinearDerivedSections, KFlatTotalTensorModel,
KFlatRingedToposPullback, RingedTopoiCanonicalTensorPullbackOfUniverses,
SheafRingDerivedCoefficientAdjunction, CochainPullbackTensorCoherence,
NormalizedDVRTower, ProEtaleConstantRingMap, FlatOnSite, and KFlatIndependentCoefficients
(the latter two as direct public statement imports). The main docstring gives the
natural-language proof, including the actual scalar formulas and triple-index checks.

### Edge cases checked

- Empty scheme and empty site objects: zero sheaf sections and the regular zero
  ring are allowed; no Nonempty, nontrivial-section or nonempty-scheme hypothesis.
- Zero complexes and the unit concentrated in degree zero: all operation and
  representative clauses remain typed; flat-term hypotheses include zero terms.
- Equal indices: actual sequence functor identities and adjunction-normalized
  composition supply identity transitions. Positive paper levels start at Lean 0.
- Nonflat quotient `ℤ/ℓ² → 𝔽_ℓ`: no ring-map-flatness assumption occurs. K-flat
  input models, rather than flatness of this map, compute scalar extension.
- Sign-twisted actual input transitions, e.g. multiplication by `(-1)^(m-n)`:
  every formula uses `transition` or its specified adjoint, preserving this twist.
- Arbitrary coefficient universe u, independently of t: no equality of site
  object/morphism sizes or coefficient/scheme sizes is imposed.
- Complexes unbounded in both directions: all model clauses use ℤ and the existing
  direct-sum total tensor; no truncation, finite diagonal, or boundedness condition.
- Arbitrary finite mixtures of tensors, geometric pullbacks, evaluations and
  coefficient quotients: each well-typed vertex is covered by one closure clause,
  and all chosen whole-system leaves retain their transitions.

### Searches and source checks

- `msearch.py NE lem-pur-normalized-operation-system-models leanfinder` with query
  “Derived tensor and geometric inverse image preserve normalized whole semilinear
  coefficient systems and simultaneous flat term K-flat models”: 8 unrelated
  ring-smoothness/Kähler-tensor hits, no exact match.
- `msearch.py ... loogle` with query
  `WeilConjectures.SemilinearSections.Normalized, CochainComplex.IsKFlatIndependentCoefficients`:
  no match (project identifier not in the Mathlib search index).
- `msearch.py ... grep` with `Normalized|semilinear` in `Algebra/Homology`:
  zero matches.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normalized semilinear systems,
  scalar coherence and K-flat models: found the existing calculus and the partial
  `SystemNormalizedTensorClosure` result. That result gives tensor/pull closure but
  not this node's unit, actual formulas, scalar association and simultaneous model
  clauses. Reused its underlying interfaces; no exact existing declaration.
- Exact item-id search, including `grep -rn` in `lean/WeilConjectures`: no match.
- Read Stacks `sites-cohomology.tex` at 07A4/0D6D and their K-flat mechanisms,
  and the live pro-etale framework instructions. The node is an extracted
  combination, not a claim that Stacks states a semilinear-system theorem verbatim.

The Lean source passed both server sandbox and named-library single-file compilation
without errors or warnings (44.2 s and 48.3 s before the final documentation-only
addition). Delivery preflight will repeat compilation. No STATEMENT-DISPUTED issue.

## New nodes

`def-pur-system-horizontal-reduction-adjoints` owns the existing plain definitions
`WeilConjectures.SemilinearSections.ordinaryReduction` and
`WeilConjectures.SemilinearSections.cochainReduction`, using `existing: true`.
The public module is `Sheaf.Paper.SystemCochainTensorReduction`, which publicly
imports `Sheaf.Paper.SystemOrdinaryTensorReduction`; neither is copied or changed.
The node defines the ordinary adjunction transpose of the actual system transition,
and its degreewise cochain morphism, for all indices and independent universes.
Its source is Zheng Construction 4.1 with Stacks 06YY/06YN. Its dependencies are
`def-coef-semilinear-system-models`, `def-coef-semilinear-derived-calculus`, and
`def-pc-cochain-complex-modules`: their `Systems`, `transition`, `evaluation`,
`Data.scalar` with its `ordinaryAdjunction`, and `CochainComplex` are used directly.
The ordinary definition is exactly `ordinaryAdjunction.homEquiv.symm` applied to
`transition.app M`. The cochain definition has component `ordinaryReduction ... (P.X k)`;
its existing `comm'` proof uses transition naturality and Hom-equivalence naturality.
No normalization, flatness, boundedness, or tensor theorem is assumed by this node.
Equal indices and degree-zero/zero complexes use the same definitions.

Searches for the new node: LeanSearch query “Horizontal reduction adjoints of strict
semilinear systems before localization and on cochain complexes” returned 8 generic
localization/adjunction hits; LeanFinder query “The ordinary scalar extension adjoint
of horizontal transitions of a tower of sheaves of modules, degreewise on cochain
complexes” returned 8 generic sheaf adjunction hits; Mathlib grep for
`ordinaryReduction|cochainReduction|semilinear.*system` in Algebra/Homology found none.
Project grep found these exact definitions only in the two recorded tensor-reduction
modules (and unrelated names in geometric comparisons). DAG grep found the theorem
nodes and unrelated comparison nodes; neither ordinary nor cochain adjoint had a
DEFINITION node. Blueprint searches for `ordinaryReduction` and `reduction adjoint`
each returned 0. All raw result names are retained in the new node's mathlib_searches.
Thus the repair adds ownership metadata for existing definitions, with no new Lean data.

The item's stmt_deps replaces `lem-pur-system-cochain-tensor-reduction` with this
new definition node. The separately added `def-weil-proetale-inverse-image` remains.

## Dependency modules

None. Existing dependency interfaces suffice; all concrete objects are reused.

## Second reading by NE

The maintainer's independent reading at immutable head `f91cca039d52` checked the
mathematics clause by clause and accepted the tensor/pull/unit adjoints, inverse
scalar comparison fixed by its transpose, actual ordinary pulled reduction,
cocycles, simultaneous flat-term K-flat models, actual X coefficients, universes
and edge cases. It returned H2 solely for ownership of the two plain reductions.
This packet implements that requested correction with an existing-definition node.
The worker's repair self-check compares the unchanged theorem/module and unchanged
item statement with the retained packet and live base; only the item's `stmt_deps`
and the new definition node change. It also matches the new node's ordinary formula
to the existing Hom-equivalence definition, and its cochain formula to the degreewise
components and existing naturality proof. This self-check is not a new independent
review; the maintainer independently reviews the repaired ownership record.

## Repair of return H2

At immutable head `f91cca039d52`, the statement imported plain `cochainReduction`
from a theorem-owned module and plain `ordinaryReduction` from another such module.
Added `def-pur-system-horizontal-reduction-adjoints`, with existing ownership of
both unchanged definitions, and cited it in place of the theorem node.
The mathematical statement, all Lean code, and all previous clause/edge-case checks
are unchanged. In particular the review advisories about `input_factor` and cocycle
clauses concern identities supplied by the existing calculus; no new claim is made
that these clauses impose independent data or require separate hypotheses.
The saved packet first passed dry run at `a57c4b156df`; it was retained and repaired
rather than restarted. The final server compile and dry run validate this packet.
