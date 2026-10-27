## What changed

Replaced the sorry in `Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor` by a
categorical composition proof with the original signature. The proof derives the change
of diagonal tensor presentation from the existing first-factor projection naturality
and a new equality of the two pullback section comparisons. It proves coefficient
naturality of the fixed left projection directly from the native mate and signed
braidings, uses naturality of the diagram's pushforward comparison, and assembles the
class insertion by tensor composition and cancellation in the proved private
`insert_class` lemma. The proved private `diagonal_insertion_from_section` does
this for arbitrary M and a map t with the specified diagonal restriction; the
assigned theorem then specializes it to M=q*K(1)[2]. This avoids elaborating
the entire categorical calculation repeatedly over the concrete rational twist.

Added proof imports of `RationalP1ProjectionNaturality`, `RationalP1SecondPullSection`,
and `ProjectiveSupportedSectionProjection`. The existing public import is unchanged.
The two component modules state the remaining identities with their source and
complete proofs in words. A third new module defines the one-field proposition
`PullSectionCompatibility`, whose field is exactly the diagonal restriction equation.
The proposition keeps that equation abstract during specialization to concrete
coefficients; it introduces no new mathematical condition or hole. No definition or existing public statement changes.

The item was initially absent from lean/ and was read from its rework quarantine path.
Its source and dependencies were subsequently restored in the shared source during
this session. The sandbox preserves its original declaration and DAG attachment.

Validation: `lcompile.py --all` accepted all four sandbox modules in import order.
The original theorem signature was checked against the restored source, and the
DAG proof dependencies match the uses of its proof steps. Profiling options and
all temporary diagnostic modules were removed before delivery.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.RationalP1.second_diagonal_insertion_factor`
(node `lem-sfb-rational-p1-second-diagonal-insertion-factor`) by a complete Lean proof
from the two component statements. No sorry remains in the assigned module.

Added two holes, each in a public theorem with an entire `by sorry` proof:

- `AlgebraicGeometry.ProEtale.RationalP1.second_pull_section`, node
  `lem-sfb-rational-p1-second-pull-section`, in `RationalP1SecondPullSection`.
- `AlgebraicGeometry.ProEtale.RationalP1.supported_section_projection`, node
  `lem-sfb-projective-supported-section-projection`, in
  `ProjectiveSupportedSectionProjection`.

This is a decomposition: one original hole closed, two component holes added, net -1.
It is not a complete proof of the geometric compatibility identities. All private
helpers in the assigned module are proved; there are no holes in definitions.

## No longer needed

None. No existing import or unit step was removed. The original ringed projection
coherence and module/ringed comparison dependencies occur below the new supported
section identity. Rational Tate and derived pullback composition coherence occur below
the new diagonal pullback equality. Their work is still needed, rather than pruned.
The new nodes separate these components instead of repeating the entire insertion
identity with a renamed theorem or repackaged hypothesis.

## Where the brief, the DAG or earlier work was wrong

The archived proof plan groups substantial normalization transport into two prose
steps. Its claimed use of the ringed section theorem does not directly supply a theorem
in the fixed internal-module functor names. Similarly, the root-normalized Tate
comparison does not directly supply its derived diagonal restriction equation. The two
new statements isolate exactly these components. The existing public
`projection_section_normalization` has integral coefficients and finite-type/localizing
hypotheses, so it does not cover the rational coefficient and arbitrary Y here; its
more general categorical argument is private. The new proof plans instead use the
unrestricted `derived_homEquiv`, `projection_comparison`, `delta_comparison`, and
`composition_comparison` clauses of `ModuleRingedComparison`, whose signatures do
not impose those field-setting restrictions. The combination with the arbitrary
class delta is now an actual Lean proof. No mathematical statement is disputed.

## New nodes

`lem-sfb-rational-p1-second-pull-section` states only the equality of the two derived
pullback identifications on the diagonal. It contains no tensor projection, diagram,
supported source, class map or trace. The item derives the tensor-map equality from it
using existing projection naturality; this derivation is proved rather than split off.

`lem-sfb-projective-supported-section-projection` is the section/projection identity
on the supported regular coefficient source. It holds for arbitrary commutative
condensed coefficients and arbitrary unbounded M, and has no rational coefficient,
field, Tate twist, class delta or trace map. Its source normalization is the one already
specified in Diagram; it introduces no arbitrary witnesses or map data.

Both statements were checked on zero objects and empty schemes; their equations reduce
to the same unit and composition coherence equations, without a nonzero or nonempty
hypothesis. No change record is required: all existing statements, definitions and
public imports remain identical, and no other existing module is edited.

`def-sfb-projective-pull-section-compatibility` records the actual one-field proposition
used by the first component. Its field is the same section equation written above;
it has no data choice or proof hole. The categorical proof uses its `comm` field. The functors and section isomorphisms
are explicit parameters, so specializing the equation does not reconstruct their
large derived-category interfaces.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
