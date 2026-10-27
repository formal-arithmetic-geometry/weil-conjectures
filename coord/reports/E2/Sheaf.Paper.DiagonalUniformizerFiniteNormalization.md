## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_finiteNormalization`
by a complete assembly proof, preserving its signature and public imports.
The proof constructs the canonical finite right-derived model from
`canonicalDiagonalRightDerived`, checks its full cochain-unit normalization,
derives the supplied ordinary square with the proved `diagonalExactSquare_exists`,
and gets the positive unit/Chern splitting from the proved `geoP1Cohomology` at
exponent `n + 1`. It then assembles the independently stated class and trace
comparisons into the original `FiniteDiagonalComparison` predicate.

Added three obligation modules, each with one named theorem, a source, a proof in words,
and a matching node. The coefficient-model theorem concerns only ordinary
coefficient and root-line comparisons; it has no completed arrow, Family,
ScalarCompatibility, class equation, trace equation or derived model in its
statement. The class theorem proves only the Cartier-arrow equation for supplied
endpoints; the trace theorem proves only the trace equation for supplied models,
a supplied full-unit square and a supplied positive splitting. No new theorem
has the original conclusion, and none merely repackages its hypotheses.

Added generic ordinary comparison structures in
`Sheaf.Paper.DiagonalFiniteOrdinaryComparisons` to store the same supported-source
and ordinary direct-image maps and normalization equations without repeating
their large concrete types. They contain no choices and no holes.

Added `Sheaf.Paper.DiagonalFiniteArrowEquations`, with two real irreducible
predicates at generic coefficients and the proved
`finiteDiagonalComparison_of_equations`. The module also contains `FiniteTracePresentation`, which groups the supplied
right-derived model, canonical-unit equation, normalized square and positive
splitting together with its hom equation, without changing any field.
`FinitePresentedTraceEquation` names the same trace equality after projecting
the supplied presentation, again at generic coefficients.
The predicates are exactly the existing
class and trace equality clauses, without changing their endpoints or maps.
Profiling the concrete Cartier statement showed 41.5 seconds of kernel type
checking (52.6 seconds total, after an earlier timeout). Naming its equality
at generic coefficients and assembling generically prevents repeated expansion
of the large concrete quotient constructions. No transparency option was disabled. Further profiling showed serialization
cost in the concrete statements; the generic source, ordinary-square and trace
presentation structures retain their exact fields while avoiding repeated
concrete type expressions.

The main proof uses private imports of the three new obligation modules and
the proved generic construction `Sheaf.Paper.DiagonalFiniteTracePresentation`.
The latter privately imports `GeoP1Cohomology`, `CanonicalDiagonalRightDerived`
and `DiagonalCompletedPushSquare` and performs those three construction steps
at generic coefficients; its first isolated compile took 7.2 seconds. No existing dependency module or
public interface was changed. The item node now follows this actual proof.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_finiteNormalization`.
Its assembly contains no `sorry`. The new generic theorem
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.finiteDiagonalComparison_of_equations`
is fully proved, with zero holes. So is
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.finiteTracePresentation_exists`.
This is a decomposition of one hole into three,
not a complete proof of the geometric normalization and not a net hole reduction.

Added exactly three holes, each with body `:= by sorry`:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_finiteModels`
  (`lem-diagonal-uniformizer-finite-models`).
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_cartierReduction`
  (`lem-diagonal-uniformizer-cartier-reduction`).
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_traceReduction`
  (`lem-diagonal-uniformizer-trace-reduction`).

There are no other new holes and no definitions or instances containing holes.
The canonical-model construction, its unit equation, the normalized derived-square
construction, the selection of the already proved positive splitting, and the
assembly are real Lean proof steps, outside the three remaining obligations.

Edge cases checked when formulating the new statements: n = 0 still means the
positive exponent l, not exponent zero; the quotient is always by pi^(n+1),
with no unramifiedness or ramification-index divisibility hypothesis; the
explicit annihilation by l^(n+1) suffices. The empty scheme and the zero
coefficient ring give zero objects and unique maps and do not require an
extra nonemptiness assumption. The two arrow lemmas retain the underlying
source or direct-image normalization, respectively; their comparison maps
are not arbitrary unnormalized isomorphisms.

The main proof caches its residue-ring and condensed-ring instances locally.
Diagnostics showed repeated inherited ring-instance conversions; the declaration
uses a bounded `maxHeartbeats 800000`. The 60-second compile limit is unchanged.

Validation: all seven delivered Lean modules compiled through `lcompile.py`.
The final item compile took 12.8 seconds. Its sole warning asked for a comment
justifying the local heartbeat setting; that comment is now present. The delivery
tool performs the final compilation and axiom checks.

## No longer needed

The original public imports are preserved and no module is withdrawn.
The item no longer directly imports `GeoP1Cohomology`,
`CanonicalDiagonalRightDerived` or `DiagonalCompletedPushSquare`: these proof
imports moved to the generic trace-presentation helper that performs their steps.
All three modules remain needed in the proof closure. No mathematical
branch of the unit route is pruned. The integral- and finite-root arguments
remain needed by the new ordinary-model obligation. The Cartier and finite
projective-line arguments remain needed by the separate arrow reductions.

The existence theorems `diagonalTower_limit` and `diagonalTower_trace` need not
be invoked to construct completed arrows or traces here: the hypotheses already
supply the specified completed arrow and the entire Reference, including its
completed traces. Their defining interfaces remain in the statement's existing
import closure. The original direct proof dependencies have been redistributed
to the three smaller obligations, rather than advertised as pruned modules.

## Where the brief, the DAG or earlier work was wrong

The original third proof step combines a class comparison with a trace
comparison and the construction of a full-unit derived direct-image square.
The existing canonical right-derived construction and the exact-equivalence
square theorem already supply the last part; there is no need to introduce
another hole for right derivation. The remaining normalized coefficient-model
and arrow-comparison bridges are not themselves supplied by the stated
root-map, Cartier-class or projective-line theorems, so they are exposed as
strictly smaller obligations instead of leaving a hole inside the assembly.
No statement was marked false, weakened or changed. The unit route is preserved.

The ordinary-model proof plan uses the existing finite-discrete constant-ring
and common sectionwise encoding constructions as generic tools. It also uses
`lem-amb-tate-root-projection-reduction` as a generic root-tensor reduction
lemma, with the necessary transport from its ordinary constant-coefficient
presentation to the existing internal quotient line. These tools do not replace
a geometric step of the diagonal unit. They are cited in the new node for the
next worker; their declarations were read before introducing that obligation.

## New nodes

`lem-diagonal-uniformizer-finite-models` states only the construction of the
three ordinary realizations, the two quotient-line endpoints, the supported
source and the ordinary projective-line direct-image comparison. It is independent
of all completed-arrow and trace data, and its ordinary square is derived in the
item proof using an existing proved theorem.

`lem-diagonal-uniformizer-cartier-reduction` states only the finite image of
the specified completed diagonal arrow after source and target comparisons have
been supplied. It has no trace equation or realization-existence conclusion.

`lem-diagonal-uniformizer-trace-reduction` states only the finite image of the
specified completed trace for a supplied normalized finite square and a supplied
positive unit/Chern splitting. It does not require a completion specification,
a cycle-system specification or an IsDiagonalLimit proof, and it has no class
comparison or model-existence conclusion.

All three inherit the item's chapter and unit and point to paragraph (1) of
`det-prop-diagonal-tower-coefficients`. Blueprint searches for finite normalization,
quotient lines, trace reduction, unit/Chern, finite quotient coefficients and
Cartier scalar reduction found no duplicate blueprint statement. The searches
and their actual results are recorded in the nodes and the launcher search log.
There is no change record because no existing statement, definition, interface,
or dependency module was changed.

`def-diagonal-finite-arrow-equations` records the two explicit equality predicates
used to keep concrete quotient types small. All predicates have real bodies; the presentation is an ordinary structure.
neither introduces objects, witnesses, axioms or hidden proof assumptions.

`lem-diagonal-finite-comparison-assembly` records the fully proved generic
assembly from the supplied data and the two equality predicates to the unchanged
`FiniteDiagonalComparison`. Its proof unfolds the predicates and fills each
field directly. It is an additional proved helper, not an additional hole.

`def-diagonal-finite-ordinary-comparisons` records the supported-source and
ordinary direct-image comparison structures. They retain the exact maps and
normalizations already required by the original predicate and choose no witnesses.

`lem-diagonal-finite-trace-presentation` records the fully proved construction
of a canonical finite trace presentation from an ordinary normalized square.
It carries out the canonical-model, full-unit-square and positive-splitting
steps at generic coefficients and introduces no hole.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
