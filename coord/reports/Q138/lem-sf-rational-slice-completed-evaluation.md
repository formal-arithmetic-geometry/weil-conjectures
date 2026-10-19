## Worker report

The delivery states `lem-sf-rational-slice-completed-evaluation` in
`Sheaf.Paper.RationalSliceCompletedEvaluation`, with main declaration
`WeilConjectures.IntegralOnSlice.rationalSliceCompletedEvaluation`.
All theorem proofs are `sorry`; every definition supplies actual data. No source
statement was corrected and no definition node or dependency module was added.

The statement needs a fairly substantial comparison interface: a bare assertion
that the source and target objects are isomorphic would not identify their
completion units or their evaluation morphisms. Its helper declarations therefore
record the chain maps and the equations that specify these comparisons.

The source is the node's main-20261015 blueprint unit
`sec-six-functors/sk-prop-sf-dualizable-biduality/_section.md`, read locally,
together with the node's ten-step restriction/completion proof. The module's main
docstring follows all ten steps and names their DAG dependencies. The auxiliary
reflection and Hom-completeness statements spell out steps 6--7, and the
restriction-completeness statement spells out steps 1--3.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]` |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| Its valuation ring and uniformizer | The recorded `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E`, used by the existing integral operations and `Rational` |
| Scheme X, ell invertible on X | `X : AlgebraicGeometry.Scheme.{u}` and `hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)` |
| Small pro-etale site | The recorded Mathlib `Scheme.ProEt`, with `IntegralOnSlice.Site X none` and `topology X none` |
| Completed integral coefficients | The recorded `IntegralOnSlice.ring`, `rings`, `finite`, `projection`; these restrict the existing completed sheaf and positive finite quotients |
| Object U and restriction to its slice | `B : X.ProEt`; `some B` indexes the actual category `Over B`, with topology `J.over B`; `restrictionModules` uses `SheafOfModules.overFunctor` |
| The same operations with the restricted coefficient sheaves | `level`, `tower`, `completion`, `completedTensor`, `hom` with index `some B`, all imported from the recorded on-slices interface |
| K,M in D^b_c(X,O_E) | `K M : D l E X none` and the two hypotheses `sfIntegralConstructible l E X K`, `sfIntegralConstructible l E X M` |
| Restriction commutes with derived reduction | `CompletedRestrictionComparisons.reductionIso` is a natural chain isomorphism, evaluated on every `Good` representative; `good` states preservation of the flat-term K-flat class |
| Positive exponents and their maps | The imported index `n : ℕ` means exponent `n+1`. `reduction_generator` fixes the map on the sheafified tensors `s ⊗ x`; `reduction_transition` and `reduction_unit` retain the quotient transitions and the canonical augmentation |
| Restricted K,M are derived complete | The main theorem explicitly concludes `IsComplete l E X (some B)` for both restricted inputs. This is the recorded `RoosComplete` predicate on the actual augmented slice tower. `restrictionComplete` also supplies the completeness proofs needed for successive restriction |
| Natural completed-tensor comparison | `tensorIso : completedTensor ... U ⋙ r ≅ r.prod r ⋙ completedTensor ... V`; `tensor_completion` ties it to the specified completion and ordinary-tensor comparisons |
| Natural derived-internal-Hom comparison | `homIso : hom ... U ⋙ r ≅ r.op.prod r ⋙ hom ... V` |
| First comparison identifies the shifted cones on the countable products | `product_projection` fixes the product map by its restricted projections. `roos_fst` and `roos_snd` specify both coordinates of the actual `CochainComplex.mappingCocone` of `1-s`. `completion_model` relates that chain isomorphism to the derived comparison through the published `completionComparison`; `completion_unit` preserves its actual `(c,0)` unit |
| Ordinary tensor and Hom comparisons are canonical | `GlobalModel` binds them to `RingedSliceEvaluationNormalized`, including its pure-tensor, local-Hom-family, localization and K-injective normalization equations |
| Preserve the coefficient object | The last clause of `Normalized` fixes `coefficientIso` to `restrictionCoefficientIso`: restriction of the rank-one module, followed by the single-degree-zero derived comparison |
| Preserve the completed coefficient-unit constraint | `CoefficientUnit` is the explicit equality between restricted `restrictionCompletedRightUnit` and the slice constraint after `tensorIso` and `coefficientIso`. The theorem asserts it for every complete input |
| Identify the actual completed evaluation | `restrictionCompletedEvaluation` applies the inverse of precomposition by the specified completion unit to the existing `ordinaryEvaluation`. `Evaluation` is the commuting square, including the coefficient-dual transport in `restrictionEvaluationSource` |
| Compatible with V -> U | `RestrictionArrow X (some B) (some C)` is literally `C ⟶ B`; its module functor is Mathlib `overMap`. `Coherent` gives the composition equations for tensor, Hom, completion and coefficients, using the derived image of the sectionwise identity module comparison. The main theorem also states `Evaluation` for the restricted pair along every such arrow |
| Identity cases | `restrictionId` and the identity half of `Coherent` retain the ambient and all slice identities; their comparisons equal the identity transports on tensor, Hom, completion and coefficients |
| Pass to scalar localizations at the uniformizer | `Rational` and `q` are the already recorded raw scalar localization and tensor-with-one functor. `restrictionRationalHom` is base change of the actual O_E-linear Hom map; `restrictionRational` is the resulting functor between the two localizations |
| Restriction carries the image of evaluation to the slice image | `RationalEvaluation` is the explicit localized commuting square, asserted for every direct slice and every successive restriction of the given pair |

`reductionIso` is written after restoring the completed coefficient action by the
actual projection, exactly as in the Roos tower. Its specified generator formula
also retains the finite quotient action: multiplying `s` by a finite coefficient
on either side gives the same generator formula. Thus it is not a comparison of
unrelated underlying abelian-group reductions.

The ambient and slice operations already use independent site object/Hom sizes
`t+1` and `t`, and coefficient/module size `max u (t+1)`. All new restriction helpers
retain those independent parameters. The final constructible statement uses a
common ambient universe `u` for E and X, matching the recorded
`sfIntegralConstructible` interface; in particular it never turns the pro-etale
site into a `SmallCategory` or equates its object and morphism universes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, its topology.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, and its reexported completed
  coefficient sheaf, projections and quotient rings.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `Site`, `topology`, `ring`,
  `finite`, `projection`, `rings`, `Mod`, `D`, `Cx`, `Good`, `generator`, `level`,
  `transition`, `tower`, `augmentation`, `roos`, `completion`,
  `completionComparison`, `completionUnit`, `duality`, `hom`, `completedTensor`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `overMap`, `overMapUnitIso`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, whose
  global branch reuses `IsDerivedCompleteUnrestricted` and slice branch is
  `RoosComplete` on the augmented quotient tower.
- `Sheaf.CategoryTheory.ScalarLocalization`: `CategoryTheory.ScalarLocalization`,
  its tensor Hom modules, `composition`, `localization` and category structure.
- Additional already-landed statement dependency `lem-sf-rational-thick-evaluation`,
  module `Sheaf.Paper.RationalThickEvaluation`: only the existing helpers
  `linear`, `coefficient`, `ordinaryPhi`, `ordinaryEvaluation`, `phi`, `psi`,
  `Rational`, `q` are used. Its thick-locus theorem is not applied or assumed.
- The proof dependency `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`
  supplies `RingedSliceEvaluationComparisons`, `RingedSliceFlatRestriction` and
  `RingedSliceEvaluationNormalized`, read with their full representative formulas.
  Other recorded proof-dependency modules are explicitly imported without
  `public`, as required by the stage contract.

Searches performed:

1. `msearch.py ... leanfinder "restriction to a slice of a ringed site commutes
   with completed derived tensor internal Hom and evaluation"`: eight hits,
   mostly light condensed internal Hom and scheme restriction formulas; none
   states the completed comparison.
2. `msearch.py ... loogle "SheafOfModules.overFunctor,
   DerivedCategory.mapDerivedCategory"`: no hits; the latter identifier is not
   recognized by Loogle. The actual recorded exact-functor API was then read in
   `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and its upstream
   companion, where the namespace is `Functor`.
3. `msearch.py ... grep "overFunctor|overMap"
   Algebra/Category/ModuleCat/Sheaf`: five hits in `PushforwardContinuous.lean`,
   used directly for restriction, maps and coefficient-unit normalization.
4. `msearch.py ... leansearch "Restriction to a slice commutes with derived
   internal Hom"`: eight hits; none gives the completed pro-etale statement.
5. `rg` of upstream `WeilConjectures` for completed tensor/evaluation and slice
   evaluation, and `grep -rn` for the exact item id: no exact declaration.
6. `rg` of `lean/Sheaf` for the same notions found
   `IntegralDerivedOperationsOnSlices`, `DerivedCompleteOnSlices`,
   `RationalThickEvaluation` and the normalized ringed slice-evaluation model.
   These supply the notions but no existing declaration states the combined
   reduction/Roos/completed-evaluation compatibility of this node.
7. Read all seven statement-dependency node statements and their Lean records or
   Mathlib matches, then opened the actual recorded source declarations. There
   is no repair note for this item in `coord/repair-notes`.

Edge cases checked in the statement:

- `n=0` means the first positive quotient (uniformizer exponent one), not a
  missing or zero-th quotient.
- Zero inputs and the empty scheme/site are allowed: no nonemptiness,
  nonzero-object, bounded representative, or local finite-projectivity hypothesis
  has been added.
- A slice need not itself have a constructible input or a new amplitude bound;
  only its actual derived-completeness condition is concluded and used.
- Both identity and arbitrary arrows `C ⟶ B` are retained; direct and successive
  comparisons are related by explicit canonical transports.
- All complexes used to normalize operations range over the entire existing
  flat-term K-flat resolving class. A bare existence of arbitrary isomorphisms or
  a check only on perfect generators is insufficient and is not substituted.
- Completion evaluation is fixed by the actual completion unit and existing
  ordinary evaluation; it is not an arbitrary lift of reduction projections.
- Rationalization uses the ambient categories of completed-coefficient module
  sheaves, and raw scalar localization, without Karoubi completion.

No STATEMENT-DISPUTED flag or unresolved node fault remains.

## Second reading by Q138

Author's second reading, with the original node and the complete final module
open; the dispatch brief assigns the independent delivery review to the
maintainer and forbids starting another agent.

I checked the two input predicates, the stalkwise invertibility hypothesis, the
actual over-site coefficients, all positive quotient indices and the two
completeness conclusions. I then followed the comparison source through dual
restriction, completed tensor and coefficient transport to its target and checked
that the evaluation square has the correct direction. The rational square uses
the same arrows tensored with one. The successive-restriction clause uses the
slice pair, and the composition predicate includes the contravariant inverse in
the first argument of Hom; replacing that inverse by the forward transport would
have the wrong type. Identity comparisons are explicitly retained.

The first full record was too expensive to elaborate; its data and normalization
predicates were separated without removing a clause. Compiler feedback also
identified missing explicit derived-additivity propagation and required explicit
endpoint types in localized composition; these interfaces were repaired. The
coefficient comparison uses the real degree-zero single-functor comparison and
the existing `overMapUnitIso`, with its actual implicit ring argument. No change
to the mathematical statement was needed.

Validation: the final module passed `scompile.py Q138
lem-sf-rational-slice-completed-evaluation .../RationalSliceCompletedEvaluation.lean`
in both sandbox and library-path modes, with no errors or unexpected warnings
(final reported times 25.3 seconds and 23.0 seconds). Every named declaration is
listed in the node's `lean.declarations`; its primary signature is copied verbatim
from the final source. The node's only other delta adds the already-landed
`lem-sf-rational-thick-evaluation` to `stmt_deps` for its reused helpers.
