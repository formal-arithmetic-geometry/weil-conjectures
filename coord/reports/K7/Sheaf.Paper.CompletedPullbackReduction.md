## What changed

CompletedPullbackReduction now proves output completeness using the intrinsic
completion comparison and joint constant-coefficient presentation, and proves
functoriality by scalar-adjunction naturality. CompletedPullbackReductionCoherence
proves the transition square, normalization isomorphisms and compatibility,
three-index cocycle, and equal-index unit, assuming only invertibility of the
specified finite arrows. Its projection calculation uses a K-injective strict
tower and the ordinary limit equation; all its helpers are proved.

The existing public supporting declarations move to CompletedPullbackReductionData,
publicly re-exported by their original module. FiniteQuotientOrdinaryComparison,
FiniteQuotientTransitionCompatibility and CompletedReductionFiniteEvaluationNormalization
redirect imports to this data module to break the proof dependency cycle.

Of the 34 existing supporting declarations, 33 retain their signatures. The generic
composite-counit helper now accepts explicitly supplied functors and comparisons
between arbitrary categories. Three new natural transformations package the native
complex counits. The published model map uses these native counits in the same
four-factor formula as before. Their naturality proofs reuse the universal counit's
naturality. This avoids repeated conversions through large abelian-category data.
The normalized finite maps, projection arrows and target theorem retain their
statements and mathematical meanings. Supporting proofs use explicit adjunction
and tensor equations and abstract fully faithful descent witnesses.

The two derived normalization predicates retain their original component equations,
now expressed through generic normalized-descent predicates. Their model natural
transformations are public constructions with the specified component maps.
This shares the typed formulas between construction and normalization, reducing
repeated conversion checks. The generalized composite helper is the only old
public signature changed; its construction users are in Data, and the compatibility consumer proves
its generic component formula.

The transition-compatibility consumer uses the model natural transformations
directly in its square, and proved private component lemmas for the two remaining
component facts. Its projection naturality calculation uses the native
reduction-tower counit. The extracted interface retains the original instance
choices. Its signature is unchanged. The new coherence module uses normal transparency
settings; inherited overrides there have been removed.

## Proved and sorry left

The sole original hole, AlgebraicGeometry.Scheme.completedPullback_reduction,
is replaced by a complete assembly from the strictly smaller finite-arrow clause.
The new AlgebraicGeometry.Scheme.completedPullbackReduction_coherence is fully
proved, as are the parent's output-completeness and naturality arguments.

One hole remains: AlgebraicGeometry.Scheme.completedPullbackReductionArrow_isIso
in CompletedPullbackReductionArrowIsIso, attached to
lem-weil-pbc-completed-pullback-reduction-arrow-isIso. It asserts only the finite
projection arrows' invertibility, without output completeness, naturality,
normalization, cocycle or unit conclusions. Its docstring gives the unit-reduction
and projection-inverse argument, including the zero ideal/ring and empty-tuple
cases. This is a decomposition: the original hole is replaced by the smaller finite-arrow
obligation. No other delivered declaration contains sorry.

## No longer needed

No module is withdrawn. The old private proof imports move with the existing
finite constructions into the data module. FiniteQuotientTransitionCompatibility
is imported only by the coherence proof; the parent has no direct use of it.
The parent no longer separately invokes strict-tower normalization, flat model,
projection-formula or perfect-Koszul calculations: finite-arrow invertibility is
the remaining subproblem that needs those comparisons. They are not claimed as
pruned globally, because the remaining subproblem still depends on them.
The experimental IntrinsicCompletionUnitFiniteReduction proof is retained only in
scratchpad and is not imported or delivered; no unused new hole is introduced.

The parent no longer invokes these original declared dependencies directly:

- def-weil-pbc-complete-coefficient-datum and
  def-weil-pbc-projection-formula-arrows: the assembly uses the existing intrinsic
  completion comparison and the smaller finite-arrow statement.
- lem-sfb-successive-derived-quotient-normalization: used by the proved coherence
  module instead of a separate calculation in the parent.
- lem-weil-pbc-completed-constant-sheaf-reduction,
  lem-weil-pbc-ordinary-finite-evaluation-transition,
  lem-weil-pbc-derived-finite-transition-normalization, and
  lem-weil-pbc-derived-finite-evaluation-normalization: the first three remain
  supporting constructions in Data; the normalization interface remains a proved
  consumer and is not an additional hypothesis of the assembly.
- lem-weil-pbc-flat-coefficient-reduction-adjunct,
  lem-weil-pbc-flat-scalar-koszul-tower-comparison,
  lem-weil-pbc-pulled-reduction-normalization-comparison,
  lem-weil-pbc-pulled-reduction-strict-tower-comparison, and
  lemma-weil-pbc-adic-completion-reduction: deferred to the strictly smaller finite
  invertibility argument; no global withdrawal is claimed.
- lem-weil-pbc-ringed-koszul-completion-reflector: the completeness proof instead
  uses ConstantCompletion.koszul_quotient_reflector through the joint constant
  coefficient presentation.

## Where the brief, the DAG or earlier work was wrong

The retained attempt had two provisional component holes, incomplete DAG metadata,
and no successful data-module compile after a compile-service disk failure.
The coherence component is now proved, its hypothesis is explicit, all new
signatures are recorded verbatim, and the old supporting-node attachments follow
the declarations' actual new module. The previous disk failure no longer occurs.
No immutable target statement, source-library declaration, or unit route changes.
Validation encountered transient missing upstream build artifacts and a timed-out
private-overlay rebuild of ConstantCompletionEquivalence, which this packet does
not modify. These are distinct from the module conversion costs repaired above.

## New nodes

lem-weil-pbc-completed-pullback-reduction-arrow-isIso is the sole remaining finite
invertibility step of the parent argument; its proof is not assumed by the
completeness or naturality arguments.

lem-weil-pbc-completed-pullback-reduction-coherence records the fully proved
conditional quotient-coherence step, strictly below the full parent conclusion.

def-weil-pbc-completed-pullback-reduction-functor records the existing completed
pullback functor and its moved auxiliary declarations in the new data module;
it constructs no new mathematical object. Change record:
coord/changes/K7-completed-pullback-finite-interface.md.

## Forced adaptations

No module held by another group is changed. The three unclaimed lower consumers
(FiniteQuotientOrdinaryComparison, CompletedReductionFiniteEvaluationNormalization,
FiniteQuotientTransitionCompatibility) import CompletedPullbackReductionData instead of
the parent, which the coherence proof now needs through FiniteQuotientTransitionCompatibility
(otherwise an import cycle). FiniteQuotientTransitionCompatibility also adapts proofs only
to the repackaged normalization predicates; all signatures are unchanged.

Reviewer correction (2026-10-26): IntegralAugmentedQuotientTowers uses the private
`projection_surjective` through `import all Sheaf.Paper.CompletedPullbackReduction`; after
the move it failed with `Unknown identifier projection_surjective` (the published original
compiles). The parent now keeps a private copy of that lemma, so the importer compiles
unchanged.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
