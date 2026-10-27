## What changed

Replaced the sole hole in `WeilConjectures.CoefSupportOpenTensor.supportOpenTensorModel`
by a Lean proof with the original signature and definitions unchanged. Obtain the
coefficient calculi at X and the compactification middle scheme from the existing
`coefficientDerivedSystemEvaluationCalculus`. The native model constructions are
isolated in new one-theorem modules:

- `Sheaf.Paper.CoefSupportPointSectionsModelExistence`: `sectionsModel_exists`, proved by
  the generic tower-evaluation theorem and a smaller scalar-square lemma.
- `Sheaf.Paper.CoefSupportPointSectionsComparisonExistence`: `sectionsComparison_exists`,
  the remaining whole-derived scalar-square construction.
- `Sheaf.Paper.CoefNativeOpenTensorModelsExistence`: `nativeOpenTensorModels_exists`.

The compact-support all-pair transition equation is proved from the existing native
transition theorem and the reduction unit/projection argument already proved privately
in `CompactSupportReductionTower`. The proof imports that module with `import all` and
uses its proved private `compactSupportReductionTransition`, `compactSupportFiniteSquare`
and `compactSupportCompletedSquare`, without changing their source or visibility.
The point-section all-pair equation is a complete calculation: naturality of
`coefTraceTransition`, `SectionsModel.transitions`, functoriality, and the first
transition equation. Both equations include equal levels and nonflat quotient maps.

The point-sections model similarly uses the proved private generic
`coefficientTowerComparison` via `import all Sheaf.CategoryTheory.CoefficientSequenceGlobalSections`.
Its statement is generic in the value category, so it supplies R-module towers directly.
The public abelian-group specialization is not coerced into an R-linear assertion.

New proof imports are private. Existing public imports are preserved. The parent DAG
proof now records this actual construction and the two precise outstanding steps.
No statement or definition was changed, no source-library module was edited, and no
consumer adaptation or change record is needed.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.CoefSupportOpenTensor.supportOpenTensorModel` (1 of 1).
The strict compact-support transition equation and its point-sections counterpart
are proved in Lean, using the supplied calculus and sections fields.
Also proved `WeilConjectures.CoefSupportOpenTensor.sectionsModel_exists`: finite evaluation,
its prescribed unit equation, and every transition follow from the generic proved
`coefficientTowerComparison` for the actual total derived functors. Only its scalar-square
comparison comes from the separate named remaining lemma.

Added exactly two named theorem holes, each in its own new module:

- `WeilConjectures.CoefSupportOpenTensor.sectionsComparison_exists`, node
  `lem-coef-support-point-sections-comparison-existence`.
- `WeilConjectures.CoefSupportOpenTensor.nativeOpenTensorModels_exists`, node
  `lem-coef-native-open-tensor-models-existence`.

This is a decomposition: one original hole closed, two smaller holes added, net -1.
It is not a claim that the mathematical model constructions are finished. There is
no remaining hole in the item module, no hole in a definition, and no arbitrary
witness selected into a definition from an existence theorem. The witnesses are
eliminated only inside the proof of the existential target theorem.

The new statements retain arbitrary schemes/open immersions and unbounded inputs.
They were checked against j = id, the empty open, zero inputs, n = m, and nonflat
quotients: the constructions use identity/zero ordinary module formulas respectively,
and exact vertical evaluation rather than any flatness of horizontal quotients.
The two calculi in the open-model lemma are given; existence of a coefficient calculus,
proper compact support, its transitions and point sections are not restated there.
The scalar-square lemma mentions no finite evaluation, compactification, open tensor
or reduction input.

## No longer needed

No public import was removed; no module or declaration is withdrawn or claimed globally
prunable. Final pruned list: none.

The old parent proof directly listed K-flat resolution, ringed K-flat pullback, derived
pullback, semilinear sections, ringed pushforward composition, sequence sections,
open normalization, slice generators, total tensor and tensor descent. Their work
remains below the existing coefficient calculus/native compact-support theorem or the
new model lemmas. These are factored dependencies, not claims that those modules
can be deleted. The direct parent edges are replaced by the actual calculus,
compact-support transition, coefficient transition and the new model nodes.
The generic derived-pullback construction is needed by the existing calculus, not
reconstructed again in the parent proof. All prior tool approvals are retained.

Direct parent proof dependencies factored below the new/existing lemmas:

- `lem-pc-kflat-resolution`.
- `lem-weil-pbc-ringed-topos-kflat-pullback`.
- `lem-weil-pbc-ringed-topoi-derived-pullback`.
- `def-sp-varying-ring-operations`.
- `def-coef-ringed-sequence-site`.
- `lem-coef-semilinear-derived-sections`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
- `lem-coef-sequence-global-sections-evaluation`.
- `lem-sf-open-tensor-normalization`.
- `lem-sf-ringed-slice-tensor-generators`.
- `lem-sf-ringed-open-total-tensor-kflat`.
- `lem-weil-pbc-site-derived-tensor-descent`.

## Where the brief, the DAG or earlier work was wrong

The existing existential `exists_compactSupportReductionTower` alone does not identify
its evaluation comparisons with the separately named `evaluation` in this item. Its
completed proof does supply exactly the needed reduction-transition and pasting
lemmas; the present proof reuses those proved private helpers via `import all`.
Thus it proves the equation for the actual named composite and evaluation, with no
inference of derived-system equality from finite evaluations.

The existing sequence global-sections theorem has abelian-group values and independently
packaged derived pairs, whereas this item requires the fixed `rightDerivedFunctor`
models with constant-R-module values and their exact unit equations. The proved
point-sections lemma supplies the tower evaluation specialization via the
existing generic tower theorem; the new scalar-square lemma isolates the remaining
R-linear derived composition comparison. The existing open normalization theorem uses
localized-site presentations and independently chosen tensor models; as the existing
item-node interface note already explains, it is not directly a constructor of
`SystemOpenModel` for the supplied `CoefficientDerivedSystemCalculus`. The new open
lemma isolates that representative-preserving transport and finite-evaluation check.
Neither issue changes the mathematical statement or the unit route.

## New nodes

`lem-coef-support-point-sections-model-existence` is now proved: it isolates original
step 4 and uses the existing generic tower comparison for the native finite evaluation
and transition fields. `lem-coef-support-point-sections-comparison-existence` is its
strictly smaller outstanding input: only the R-linear whole-derived scalar square
and its unit equation. Source: Stacks 0D6E and 0941. Its proof explains
why quotient restriction need not preserve K-injectives and why constant-tower
evaluation does. LeanSearch, LeanFinder, Loogle, source/Mathlib searches and blueprint
searches found no theorem at this native interface. It is strictly independent of
open tensors and compact support.

`lem-coef-native-open-tensor-models-existence` isolates original steps 5--6 for any
given open immersion and two coherent coefficient calculi. Source: Stacks 0E8I, 0GL1
and 07A4. Its proof specifies pure tensors, adjoint inverse-unit normalization,
signed total summands, one-K-flat descent, and exact finite evaluation. The documented
searches found the existing localized open theorem but no constructor at these
prescribed native interfaces. It has no compactification, proper image, sections,
reduction-tower existence or transition conclusion. The open-model and scalar-square
modules contain the two sourced theorem statements
with proof `by sorry`; the point-sections model module has a complete proof.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
