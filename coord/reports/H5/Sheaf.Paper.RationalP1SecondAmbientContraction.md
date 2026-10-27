## What changed

Replaced the proof hole of `rationalP1_second_ambient_contraction` by a Lean
assembly of two separate geometric equations. The unit normalization predicate is
opened, its HEq witness is converted to an equality, and the literal unit formula
is factored. The unchanged counit arrow and its normalization are passed to the
trace-tail statement. The section/class prefix factors through a forward p2
projection. The trace-tail equation then cancels that forward projection against
the inverse projection/exchange word and the pulled counit. Tensor functoriality
and cancellation of the canonical derived-functor comparison give exactly the
original scalar expression, without applying either integration identity. The final
cancellation is proved once in `assemble_second_unit` at a generic condensed
coefficient, using the fixed module-object interfaces. The interface takes M and
the pulled counit arrow explicitly, so specialization keeps their types folded.

Added five modules: `RationalP1SecondPullComparison` explicitly constructs the
canonical pullback/twist comparison and forward projection;
`RationalP1SecondDiagonalInsertionFactor` states the section/class factorization;
`RationalP1SecondTraceReordering` states the diagonal-free trace-tail equation;
`RationalP1AmbientTail` constructs the class-free unit tail and proves its
factorization at a generic coefficient;
`RationalP1SecondTraceEquation` packages exactly the trace equality in a
one-field proposition at a generic coefficient, and proves the generic assembly
`assemble_second_unit` from that field and the insertion equation.
Only private proof imports are added to the item. All existing signatures,
public imports, and definitions are unchanged.

The comparison construction uses actual tensor and shift isomorphisms, Cartesian
Tate comparisons, and the self-square pullback comparison. It introduces no data
chosen from an unproved existence assertion. The forward projection has no
invertibility hypothesis. In particular no separate p2 projection-isomorphism
hole is needed for the assembly.

Validation: all six modules compiled on the project server. The final generic
assembly, trace statement and parent compiled in 18.4 s, 50.7 s and 56.1 s.
Profiling options and temporary probe modules have been removed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.RationalP1.rationalP1_second_ambient_contraction`
(node `lem-sfb-rational-p1-second-ambient-contraction`). Its proof is complete
relative to the following two new named statements, each with its own module,
node, source, and proof in words:

- `AlgebraicGeometry.ProEtale.RationalP1.second_diagonal_insertion_factor`
  (`lem-sfb-rational-p1-second-diagonal-insertion-factor`). This has no trace,
  counit, inverse exchange, inverse projection, completed reference, localizing
  hypothesis or integral. It is the section/projection part of the argument.
- `AlgebraicGeometry.ProEtale.RationalP1.second_trace_reordering`
  (`lem-sfb-rational-p1-second-trace-reordering`). This has no diagonal insertion,
  diagonal class, supported-source map or integral in the equation. It is the
  exchange/tensor and trace-base-change part of the argument.

Also proved `AlgebraicGeometry.ProEtale.RationalP1.unitComponent_factor`, the
generic literal factorization of the existing unit formula, and
`AlgebraicGeometry.ProEtale.RationalP1.assemble_second_unit`, the generic
categorical assembly of the two equations.

One original hole closed; two holes added; zero holes remain in the item itself.
This is a decomposition, not a net reduction in holes. The comparison and
ambient-tail modules have zero holes; the trace-equation interface also has zero
holes. Neither remaining statement is the original contraction under a renaming
or a repackaging of its normalization hypotheses.

Edge cases: K=0 makes all displayed maps between zero objects; an empty base
makes all of the relevant module categories trivial. No nonzero-object,
nonempty-base, odd-prime, or bounded-complex hypothesis is used. The even-shift
sign in the trace-tail proof plan also applies at l=2. The insertion equation is
stated for an arbitrary normalized coefficient diagram and arbitrary K, without
a constructibility or reference hypothesis.

## No longer needed

No existing import is removed, and no module is withdrawn or globally pruned.
The parent's proof dependencies now consist of the ambient-composite definition,
the two new step nodes, the proved ambient-tail factorization, the explicit comparison construction, and
the trace equation interface. Its prior generic coherence, Tate, reference, and coefficient
normalization dependencies remain needed in the new steps and their explicit
comparison construction; they are not claimed as pruned.

The prior proof dependencies
`lemma-nagata-projective-space-base-change-proper` and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` are not separately
invoked in the new assembly. The normalization predicates already supply the
three fixed invertibility witnesses. Composition/section comparisons remain in
the existing definitions and in the section-coherence argument. This does not
withdraw their library modules or declarations.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change is claimed. The prior node grouped the
trace-tail calculation and the section/insertion normalization into one large
step. The new split separates these independent equations and specifies their
common forward projection as a concrete construction. This makes the remaining
obligations strictly smaller than the previously twice-split contraction.

The generic ringed section and exchange theorems do not directly rewrite the
present internal-module expressions: their normalized transport, the Cartesian
Tate comparison on q*K(1)[2], and trace base change still have to be checked. These
are the work recorded in the two new statements. The analogous tower-system
triangle factorization uses different categories and presentations and is not a
directly applicable lemma for this item.

## New nodes

`def-sfb-rational-p1-second-pull-comparison` attaches the five explicit
constructions `ambientPullbackComparison`, `secondDiagramPushIso`, `pullTwistIso`,
`secondPullComparison`, and
`secondForwardProjection` in `Sheaf.Paper.RationalP1SecondPullComparison`.

`lem-sfb-rational-p1-second-diagonal-insertion-factor` attaches the insertion-only
equation in `Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor`.

`lem-sfb-rational-p1-second-trace-reordering` attaches the diagonal-free tail
equation in `Sheaf.Paper.RationalP1SecondTraceReordering`.

`def-sfb-rational-p1-ambient-tail` attaches `ambientExchangeInverse`, `unitTail`
and the proved factorization `unitComponent_factor` in
`Sheaf.Paper.RationalP1AmbientTail`. These generic wrappers avoid expensive
unfolding of the concrete projective-line site.

`def-sfb-rational-p1-second-trace-equation` attaches the exact one-field
proposition `SecondTraceEquation` in `Sheaf.Paper.RationalP1SecondTraceEquation`.
It takes an arbitrary derived object M and a tail-shaped arrow f. It also attaches
the proved generic categorical assembly `assemble_second_unit`. The proposition
is an elaboration interface for the displayed trace equation, with no
mathematical reduction or additional assumption claimed for the packaging itself.

No change record is required: no existing interface, statement, definition or
public import changes, and no other existing module is edited.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
