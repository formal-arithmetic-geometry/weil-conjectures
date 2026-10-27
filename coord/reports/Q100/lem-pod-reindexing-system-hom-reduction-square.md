## Worker report

Q100 states `lem-pod-reindexing-system-hom-reduction-square` in
`Sheaf.Paper.ReindexingSystemHomReductionSquare`, with main declaration
`WeilConjectures.podReindexingSystemHomReductionSquare`. The node's mathematical
statement, proof, source and other metadata are unchanged. The returned delivery's
H2 ownership fault is repaired by adding the definition owners to `stmt_deps` and
a new `existing: true` definition record; the Lean source is unchanged. The theorem has proof `sorry`. The additional named theorem
`podAmbientReindexingTensor_existsUnique` also has proof `sorry`, with a full
natural-language proof and the same owning DAG node in its docstring. It supplies
the uniquely characterized ambient tensor comparison used by this statement.
Every definition has real data; the latter comparison is selected from a
uniqueness theorem whose ordinary and K-flat normalizations determine the object.
No definition is a `sorry` or a choice of an uncharacterized map.

### Hypotheses and objects

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite coefficient extension: `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The dependency's canonical
  integral coefficient ring and quotients are used; there is no second valuation
  ring or uniformizer parameter. Its quotient index `n` means exponent `n+1`.
- Schemes and isomorphism: `{X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]`.
- Invertibility on both schemes: `[∀ x : X, Invertible (l : X.residueField x)]`
  and the analogous instance for Y, bound explicitly before the structures and
  main theorem that use the finite pullback comparisons.
- The actual strict system abelian category is `coefficientSequenceModules l E W`,
  modules on `coefficientSequenceTopology (Scheme.ProEt.topology W)` with ring
  `coefficientSequenceCommRingSheaf l E W`. The existing definition includes all
  horizontal coefficient-linear transition maps. Its derived category is
  `coefficientSequenceDerived l E W`, the ordinary unbounded derived localization.
  The site has object universe `u+1` and morphism universe `u`; these are not
  identified. A common containing universe for E and the schemes is used as in
  the recorded coefficient-stage operations.
- Completed ambient complexes range over the entire
  `DerivedCategory (integralTowerModules l E W)`, with completed coefficient sheaf
  `completedIntegralCommRingSheafUnrestricted l E W`. They are not restricted to
  constructible or complete objects.
- The actual operations are those of `pullbackTensorCalculus l E W`, the recorded
  coefficient evaluation calculus, and its `systemClosed`, `integralClosed`,
  `finiteClosed`, `reduction`, `adjunction`, `reductionTensor`, `evaluationTensor`
  and `quotientCalculus`. `coefficientSequenceLimit` is its specified realization.

### Clause-by-clause translation

| Node clause | Lean rendering |
| --- | --- |
| Reindexing fixes the sequence index and every coefficient arrow | The actual functor is `pullbackTensorSequenceInverse l E g`. Its base is `pullbackTensorSequenceBase g = (𝟭 ℕ).prod (proEtaleBaseChange g)`, and its ring map is the existing constant-section `pullbackTensorSequenceRing`; no replacement functor is quantified over. |
| Exact abelian equivalence | `PodSystemReindexingLaws.equivalence` asserts `IsEquivalence` of that functor. Its additivity, preservation of finite limits and finite colimits, and hence exactness are already supplied by the actual functor's global instances and `pullbackTensorSequenceInverse_exact` in `CompletedPullbackTensorComparison`; no new exactness assumption is imposed. |
| Preserves K-injectivity | `PodSystemReindexingLaws.kinjective` quantifies over every whole system complex and asserts `IsKInjective` of its termwise image. It does not assert K-injectivity of a level evaluation. |
| Preserves K-flatness | `PodSystemReindexingLaws.kflat` uses `CochainComplex.IsKFlatIndependentCoefficients` for the actual sequence-site sheafified signed total tensor, with both sites/rings explicit. |
| Ordinary unbounded derived equivalence | `PodSystemReindexingLaws.derived_equivalence` asserts `IsEquivalence` of `pullbackTensorSequenceDerived`, the existing termwise functor descended through ordinary localization. |
| Actual natural system internal-Hom isomorphism | `PodSystemReindexingLaws.hom` is an actual `NatIso` between the two bifunctors, whose components must equal `podSystemHomComparison`. That map is the existing `coefficientBaseChangeHom` closed transpose using `pullbackTensorSystemComparison`. It is not an arbitrary isomorphism or a list of finite-level maps. |
| Simultaneous product-Hom representative | `representative : Nonempty (PodSystemHomReindexing l E g)` supplies sheaf-Hom isomorphisms on the actual sequence site, their local slice evaluation formula for every arrow `a : V ⟶ U`, a chain isomorphism on all unbounded complexes, every product projection equation, and its specified K-injective localization equation. `chain` being an isomorphism of complexes includes compatibility with the signed Hom differential. `derived_model` identifies precisely the prescribed derived comparison, including the localization-factor isomorphisms. |
| Evaluation and transposition are the specified reindexings | `evaluation` gives the actual system evaluation equation. `compatible : CoefficientEvaluationCompatible ...` gives naturality, all closed transposes and composition for the same comparison. `sheafHom_sections` fixes ordinary evaluation as the relabeling of `f(x)`. |
| Cartesian first input, arbitrary second input | `PodCartesianSystemHomCalculus.fiber_isIso` assumes `IsNormalizedCoefficientSequence ... M` only. N is unrestricted. `podCartesianSystemHomFiber` is the evaluation-defined Hom map; it is an isomorphism under exactly this first-input hypothesis. The assertion is made on both Y and X by `cartesianY` and `cartesianX`. |
| Evaluations equal the finite-level c-zero maps | `PodCartesianSystemHomReindexing.fiber` identifies evaluation of `podSystemHomComparison` with `podFiniteHomComparison` after the specified `pullbackTensorDerivedEvaluation` input identifications. The first input is cartesian, and N is arbitrary. `podFiniteHomComparison` is the finite evaluation-defined closed transpose, so this is the c-zero comparison, rather than a choice of some finite isomorphism. |
| Finite evaluation preserves specified evaluation and transposition | `PodCartesianSystemHomCalculus.transpose` is `CoefficientEvaluationCompatible` for each actual evaluation functor and its tensor comparison. Together with the evaluation-defined fiber map and `compatible`, this fixes the same evaluations/transposes before and after reindexing. |
| Full m-to-n reduction word | `podCartesianSystemHomReduction` is the closed transpose of, in order: tensor of identity with `coefficientSequenceNormalizationIso ... M hM).inv`; `quotientCalculus.tensor h).inv`; scalar extension of finite evaluation; and `coefficientSequenceTransitionAdjoint ... h N`. Its `hM` is only on M. `PodCartesianSystemHomCalculus.reduction` states that the actual system-Hom transition, after the n-fiber comparison, equals scalar extension of the m-fiber comparison followed by precisely this word. |
| Reindexing commutes with scalar extension and both transitions, including inverse first transition | `PodCartesianSystemHomReindexing.normalized` preserves cartesianness. `transition` gives the actual scalar-extension/input-transition equation for every N, with `pullbackTensorQuotient`. `reduction` states equality for the entire transposed word, including both finite Hom comparisons and all input identifications. Thus the inverse first transition is not replaced by an unspecified isomorphism. |
| Ambient square for arbitrary M,N | `PodSystemHomReductionSquare` quantifies over all ambient M,N and equates `podSystemHomReductionLeft` and `podSystemHomReductionRight`. The former is reduction of ambient closed comparison followed by beta-X. The latter is rho at ambient Hom, then reindexing of beta-Y, then the actual system Hom comparison, then contravariant/covariant input transport by rho-M and rho-N. `PodSystemReindexingLaws.beta` asserts this equality in the system derived category. |
| Coefficient identifications from all quotient projections | `podCompletedRingMap`, `podCompletedModuleInverseImage`, `podOrdinaryLimitReindexing`, `podLimitReindexing` and `podReductionReindexing` are the existing actual constructions. The limit maps are uniquely projection/derived-functor normalized; rho is the actual adjunct of the transported unit, not an arbitrary natural isomorphism. The new ambient tensor comparison is pinned on local pure tensors and the signed K-flat total tensor. |
| Reduction/limit unit square | `PodSystemAdjunctionReindexing.unit` equates transported unit followed by inverse lambda with unit-X followed by `L_X.map rho`. As required by the adjunction's types, this is an ambient equation relating the system comparison rho under L-X; no ill-typed application of L-X to an ambient arrow is made. |
| Reduction/limit counit square | `PodSystemAdjunctionReindexing.counit` is the actual system equality under rho and lambda, for every system N. `PodSystemReindexingLaws.adjunction` supplies both squares. |
| Functorial realized identities | `PodSystemReindexedRealization.evaluation`, `.transpose`, `.beta` and `.counit` explicitly apply `coefficientSequenceLimit l E X` to both already-defined system routes. The unit equation already has the ambient codomain and explicitly includes `L_X.map rho`. All these equalities precede or follow actual functor application; no faithfulness or equality-detection property is assumed. |
| No beta invertibility for arbitrary inputs | No field asserts `IsIso` for arbitrary beta, and both ambient-square paths use beta only in its forward direction. |

### Dependency declarations read and used

- `def-weil-scheme-morphism-properties`: the recorded convention is rendered by
  Mathlib `IsIso` and residue-field `Invertible`, not by a private scheme predicate.
- `def-weil-derived-pullback-tensor-hom`, module
  `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`, `finiteIntrinsicClosed`,
  `finiteIntrinsicEvaluation` and `finiteIntrinsicTranspose`, via the recorded
  coefficient calculus and finite comparison interfaces.
- `def-weil-l-adic-coefficient-extension`, module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its canonical coefficient objects.
- `def-weil-pbc-proetale-site`, Mathlib
  `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt` and `AlgebraicGeometry.Scheme.ProEt.topology`.
- `def-weil-completed-integral-coefficients`, module
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, the completed sheaf and its specified
  quotient projections (reexported actual completion declarations).
- `lem-coef-derived-system-evaluation-calculus`, module
  `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, `CoefficientDerivedSystemCalculus`,
  `CoefficientEvaluationCompatible`, `coefficientBaseChangeHom`,
  `coefficientSequenceDerivedEvaluation`, `coefficientSequenceInternalHom`,
  `coefficientFiniteInternalHom`, `coefficientIntegralInternalHom`,
  `coefficientSequenceTransitionAdjoint` and `coefficientSequenceNormalizationIso`.
  `pullbackTensorCalculus` selects exactly this recorded calculus.
- `lem-coef-semilinear-derived-sections`, module
  `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and
  `SemilinearDerivedSectionsData`, especially `homEvaluation`,
  `HomReductionFormula` and `TensorComparisonModel`. Its generic system category
  specializes definitionally to `coefficientSequenceModules`; a server-compiled
  probe checked that identity with `rfl`. The concrete statement above uses that
  existing coefficient category rather than copying generic system data.

Further reused existing constructions are in
`Sheaf.Paper.CompletedPullbackTensorComparison` (`pullbackTensorCalculus`, actual
sequence inverse image/derived functor, system tensor comparison, finite evaluation
and quotient isomorphisms) and `Sheaf.Paper.DerivedAutomorphismHomEvaluation`
(`podSystemHomComparison`, `podFiniteHomComparison`, `podKInjectiveHomModel`,
`podCompletedRingMap`, `podCompletedModuleInverseImage`,
`podCompletedDerivedInverseImage`, `podOrdinaryLimitReindexing`,
`podLimitReindexing`, `podReductionReindexing`). The latter module's existing
`podHomReductionSquare` assumes a constructible pair, and its fiber assertion
normalizes both inputs. Neither states this unrestricted node, so no `existing`
record is appropriate. Its definitions, however, are precisely the canonical
notions required here and are reused without duplication.

Import and DAG ownership repair: the published module containing these helper
constructions belongs to the downstream theorem
`lem-pod-derived-automorphism-hom-evaluation`. That theorem cites this item in
`proof_deps`, so it cannot serve as their statement dependency. The new definition
node `def-pod-system-hom-reindexing-maps` re-exports precisely the existing
canonical maps and their uniqueness/law/normalization helpers with
`existing: true`. The item now cites that node and all six additional owners
listed by the maintainer: `def-pur-completed-pullback-tensor-comparison`,
`def-sf-adic-closed-reindexing-maps`, `def-pur-hom-complex`, `def-pur-sheaf-hom`,
`def-weil-proetale-iso-sectionwise-inverse-image`, and
`def-coef-semilinear-system-models`. No downstream theorem edge is added. A
read-only traversal of both statement and proof edges confirms that none of the
newly cited owners has a path back to this item. The current Lean import graph
remains unchanged and acyclic.

### Sources and edge cases

Read the complete node and each statement dependency with its recorded Lean
signature/docstring, the actual sequence/evaluation/tensor implementations, and
the current blueprint under `literature/blueprint/latest/`,
`sec-poincare-duality/sk-thm-frobenius/prop-pod-dual-tate-data-compatibility.proof.md`,
Step 5. The node's nine-step refinement supplies the precise simultaneous-system
and total-limit maps; its listed Stacks tags anchor those constructions.

Checked g = identity: all maps are the specified identity-reindexing comparisons,
not an additional identity hypothesis. Checked zero inputs and empty schemes:
there is no nonemptiness, rank, or nonzero-object assumption. Checked m = n:
`h : n ≤ m` includes equality, the normalization inverse and scalar-extension
identifications still have their actual types. Checked arbitrary shifts and
unbounded complexes: Hom is a product over every integer p and no boundedness or
levelwise K-injective assumption occurs. Checked noncartesian second inputs:
its transition is used forward only. Checked noncartesian first inputs: only
fiber invertibility/full inverse-first-transition assertions require cartesianness;
the system comparison and ambient beta square remain unrestricted. Checked
arbitrary ambient complexes outside the constructible subcategory: beta is never
inverted and no completeness condition is introduced.

No `STATEMENT-DISPUTED` fault or mathematical correction was needed. The unit
square's ambient type is explained above, rather than introducing a spurious
system-valued unit.

### Searches

The prescribed msearch searches were run, as were local source searches. No
existing declaration states the whole node.

- LeanFinder: `Reindexing ringed sequence sites preserves derived internal Hom
  evaluation and coefficient reduction`. Eight results included affine-space
  reindexing, `HomologicalComplex.evalCompCoyonedaCorepresentative`,
  `Functor.OfSequence.map` and HomComplex induction sequence declarations;
  no ringed-system Hom/reduction square.
- Loogle: `CategoryTheory.Equivalence, DerivedCategory`: zero results.
  An earlier broader query also included `CategoryTheory.Adjunction`.
- Mathlib grep through msearch: `reindex.*[Hh]om|[Hh]om.*reindex`, in
  `CategoryTheory`: product/reindex projection formulas and ordinary diagram
  reindexing, not this coefficient-system statement.
- LeanSearch: `Exact equivalence of ringed sequence sites preserves derived
  internal Hom and commutes with coefficient reduction and inverse limit
  adjunction`: eight unrelated results, including sheafification units,
  Gamma-Spec, condensed AB4 and LightCondensed internal Hom; no match.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for reindex/Hom patterns
  found the reusable declarations discussed above and the upstream ordinary
  inverse-image Hom comparison, not the full cartesian-first/unrestricted-ambient
  system statement. Searches for this item's id in the upstream Lean source
  found no existing declaration.

### Validation

All compilation uses the authorized `scompile.py` wrapper against the published
live build. Earlier incremental server compiles checked the generic system
specialization, universe levels, representative isomorphism, and full transition
orientations. The final server compile and delivery preflight results are recorded
by the delivery wrapper. Only the two expected `sorry` warnings are permitted.

## Second reading by Q100

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the only review. This report is Q100's own
statement audit, not an independent review.

## New nodes

`def-pod-system-hom-reindexing-maps` is an existing-declaration definition owner
for the evaluation-defined `podFiniteHomComparison` and
`podSystemHomComparison`, the augmentation-normalized `podKInjectiveHomModel`,
the unit/section-normalized finite restriction and system evaluation
comparisons, the projection-normalized ordinary limit comparison, its
resolution-normalized derived `podLimitReindexing`, and the actual adjunct
`podReductionReindexingMap` with its isomorphism `podReductionReindexing`.
Its `lean.declarations` also records each relevant `_existsUnique`, `_laws`,
augmentation/projection helper and `PodLimitResolutionNormalization`; the helper
`PodModules` is included for the generic K-injective model's independent
universes. Already owned completed-ring inverse-image constructions remain
owned by `def-sf-adic-closed-reindexing-maps`, which the new node and item cite.
No file or definition is copied. Its source is current blueprint dual-Tate
compatibility Steps 1, 2 and 5, with the original item's precise system refinement
and Stacks 0GMX, 0A95, 0941 and 07A6. It has the same chapter/unit as the item,
ancestor `prop-pod-dual-tate-data-compatibility`, the item prepended to the
original blueprint via list, and `import_flags: []` because it is reachable
through this item. Its edge cases are the existing definitions' identity g,
zero/unbounded complexes, arbitrary ambient inputs and every positive quotient
index; it introduces no extra hypothesis and no new assertion of the downstream
theorem.

The new node's searches were run during this repair. LeanSearch query
“Canonical internal Hom comparison for reindexing coefficient systems with K
injective Hom representatives and normalized derived limit reduction comparisons”
returned eight generic K-injective/ordinary Hom results, no such package.
LeanFinder query “Scheme isomorphism reindexing coefficient system internal Hom
and derived limit with projection normalized reduction adjunction comparisons”
returned eight scheme-limit, affine reindexing and condensed Hom results, no
match. Mathlib grep for the five canonical names returned zero hits. The same
names in upstream `lean/WeilConjectures` returned no match; `lean/Sheaf` found the
exact existing `DerivedAutomorphismHomEvaluation` definitions. Searching existing
definition-node records found no owner of these five maps. Nearby
`def-pod-completion-reindex-*` nodes use the distinct isoReduction and
PodCompletionReindex models, while `def-sf-adic-closed-reindexing-maps` owns only
the already cited completed inverse image subset. `blueprint_refs.py search
reindexing` found only `def-mg-determinant-line`, not these notions. The new node's
`mathlib_searches` contains the exact queries, results, dates and verdicts.

## Returned-delivery repair

H2 at immutable head `9f24a391af54`: repaired exactly by the preferred section
1(A) existing-declaration owner plus all six named definition dependencies.
The comparison with current main found no sandbox changes outside the retained
`lean` record before this repair; current main has no Lean record for the item.
The prescribed delivery wrapper refreshes current main and builds the new packet
on that base. The Lean file remains byte-for-byte the returned version, SHA-256
`8871126ac1d8ed44cab1549a6e2310e1951fb94ab48196c133cf94dcc0e1e35c`
(checked against the retained file before delivery). The mathematical
statement was independently accepted clause by clause in the return; no
`statement_change`, new hypothesis, theorem weakening or Lean edit is made.
The six added owners are read through their full recorded definitions and Lean
interfaces. In particular the actual product Hom, slice Hom, sectionwise inverse
image, sequence tensor comparison and generic representative normalization are
not private duplicates. All new node dependencies have been checked against
both DAG edge kinds for a path to the item; none closes a cycle.

The final validation reruns `scompile.py`, the `deliver2.py --no-push` preflight
and compilation, and actual delivery for this repaired packet. No global build,
direct repository edit, Git command or independent-worker claim is made.
