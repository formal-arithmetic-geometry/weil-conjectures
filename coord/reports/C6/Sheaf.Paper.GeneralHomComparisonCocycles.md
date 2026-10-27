## What changed

Replaced the single sorry in `WeilConjectures.generalHomComparisonCocycles` by a
proof of all six conjuncts from existing statements and three normalization
substeps. The original public declarations, definitions, signatures and public
imports are unchanged. Added proved private helpers for evaluation naturality,
uncurrying, the identity and composite Hom-comparison equations, and evaluation
existence/uniqueness. The generic identity/composition arguments specialize the
argument already used by `ScalarHomComparisonTower`; they do not require the Hom
comparison to be invertible.

The finite cocycle and finite evaluation laws use
`finiteCoefficient_derivedHom_change`. Integral invertibility uses
`IntegralHom.comparison_isIso`; its comparison agreement follows by injectivity of
the fixed transpose. Ordinary scalar evaluation and both substantive field
transport clauses use `basicOperationsCoefficientReduction`, on the identity of X.
The residue-field invertibility instance follows from the characteristic hypothesis.
The scalar agreement proof expands the completed maps, factors the map on the two
Hom arguments, applies the ordinary Hom square and cancels the ordinary comparison
isomorphism. Its canonical completed Hom isomorphism gives the required IsIso.

Added three proof imports and one import for existing integral comparison
invertibility. Added the three new modules listed below and updated the original
node's proof route. No target or adopted-source declaration changes, definition
repairs, consumer adaptations, withdrawals or change records are involved.

## Proved and sorry left

Original item: one hole, in `WeilConjectures.generalHomComparisonCocycles`.
The item now has zero holes. Its proof is a decomposition, not an unconditional
closure of the argument: one upper hole is closed and three lower holes are added.

Every added hole is the entire proof of one public theorem:

- `WeilConjectures.coefficientTensor_normalization`, node
  `lem-sf-coefficient-tensor-normalization`, in
  `Sheaf.Paper.CoefficientTensorNormalization`.
- `WeilConjectures.integralHom_presentation_evaluation`, node
  `lem-sf-integral-hom-presentation-evaluation`, in
  `Sheaf.Paper.IntegralHomPresentationEvaluation`.
- `WeilConjectures.scalarHom_presentation_evaluation`, node
  `lem-sf-scalar-hom-presentation-evaluation`, in
  `Sheaf.Paper.ScalarHomPresentationEvaluation`.

These are tensor-only coherence, integral evaluation normalization, and ordinary
scalar Hom/completion normalization respectively. None repeats the six-conjunct
item. The integral lemma does not assert invertibility; the scalar lemma asserts
neither completeness nor a completed Hom isomorphism. Each supplies a strictly
smaller step that the main proof combines with other existing results.

The generic private helpers contain no sorry. No definition contains a hole.
Existing imported theorems may still use sorry; this delivery does not close them.

## No longer needed

Removed these original private proof imports from the item:

- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`: the needed generic
  closed identity/composition reasoning is proved directly for the actual
  `CoefficientClosedStructure` interface, without a separate monoidal-closed instance.
- `Sheaf.Algebra.Homology.SitePerfectScalarHomComparison`: finite elementary
  agreement is definitional equality in the current interface.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`: field transport is already
  a clause of `basicOperationsCoefficientReduction`; the remaining clauses are
  congruence under the specified functor maps.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` and
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`: the main proof uses the
  fixed calculus and the explicit tensor-normalization substep. Their structural
  facts remain dependencies of the lower normalization nodes.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: the main proof uses the
  existing completion and canonical completed Hom isomorphism API. The finite-free
  comparison remains needed by that API and the scalar normalization node.

Corresponding direct proof dependencies/tool-use entries removed from the original
node are `lem-fix-internal-hom-comparison-composition`,
`lem-fix-site-perfect-scalar-hom`, `lem-pur-semilinear-scalar-localization`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-weil-finite-free-completed-scalar-comparison`,
`lem-coef-integral-hom-reduction` and `lem-coef-integral-finite-extension`.
The last two modules remain public imports because existing definitions use their
interfaces; their existential theorems are not used to choose arbitrary witnesses.
None of these modules is withdrawn, and no whole-library pruning is claimed: some
remain transitive dependencies or statement dependencies. The unit's route remains
through the original general-Hom node.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies contain presentations, evaluations and coefficient
comparison results, but do not directly provide the simultaneous normalization of
their choices against the fixed closed calculus. A presentation witness alone
cannot be substituted into an equality with a differently chosen fixed
adjunction. The new substeps explicitly isolate that normalization, choose source
and target presentations jointly, and use the fixed natural adjunction on every
ambient input. Normalization restricted to K-flat pairs is not used to identify an
arbitrary adjunction on a non-flat input.

The current finite elementary agreement is already definitional, so it needs no
site-perfect Hom theorem. Raw rational and common-stage Hom comparisons are
already explicit clauses of `basicOperationsCoefficientReduction`; a separate
localization argument here would duplicate those clauses. No existing statement
was weakened or marked disputed.

The normalization statements were checked on identity coefficient extension,
identity quotient, the first positive exponent (index zero), zero inputs, empty
sites and unbounded ambient inputs. No quotient-flatness assumption is introduced;
K-flat models compute the derived changes of rings. The scalar ordinary functors
are related by a natural isomorphism, not asserted definitionally equal.

## New nodes

`lem-sf-coefficient-tensor-normalization` records the identity and consecutive
coefficient tensorator equations with the actual restriction-adjoint mates, and
the three associator squares. Its proof in words computes the maps on K-flat pure
tensors, identifies the normalized units/mates, and descends the equations.

`lem-sf-integral-hom-presentation-evaluation` records the existence of one integral
presentation and compatible reduction presentations whose comparisons uncurry to
the fixed reduced evaluation. Its proof in words transports the fixed adjunction
by Koszul symmetry, uses the representative evaluation and scalar-unit
normalizations, and computes the resulting transpose.

`lem-sf-scalar-hom-presentation-evaluation` records jointly normalized ordinary
scalar Hom presentations and the natural ordinary scalar functor isomorphism,
together with its compatibility with the two completion transformations. Its
proof in words compares the coefficient maps by finite projections, ordinary
tensor units and Hom evaluation, then the finite quotient and Roos coordinates of
the completion maps.

All three nodes descend from the current blueprint's general-Hom evaluation
sentence through `lem-sf-general-hom-comparison-cocycles`; they carry full Lean
statements, sources, searches, dependencies and prose proofs. No change record is
needed because no existing definition or statement changed.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
