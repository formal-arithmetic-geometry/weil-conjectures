## What changed

Proved AlgebraicGeometry.ProEtale.purityTraceTranspose_baseChange in
lean/Sheaf/Paper/TraceTransposeBaseChange.lean. All existing public signatures,
definitions, docstrings and public imports are unchanged.

The private proved helper trace_mate derives transpose compatibility with an
invertible exchange from homEquiv_naturality_right, naturality of mateEquiv and
unit_mateEquiv. Apply it to the actual etale exceptional adjunctions and the
inverse compact-support exchange. Its mate, followed by the canonical unit
comparison, is definitionally dualizingComplexBaseChangeMap. Naturality of
purityTracePullbackComparison then transports the equality along the retained
representative isomorphism e to the original pro-etale input L.

The existing node's proof, proof_deps and proof_origin now record this shorter
formal calculation; obsolete top-level tool_uses approvals are removed. No new
modules, nodes, definitions, statements or consumer adaptations are introduced.
The unit's smooth-purity and model-agreement route is retained: this proves the
same trace comparison inside its existing step and changes no unit-level result.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.ProEtale.purityTraceTranspose_baseChange
(lem-pur-trace-transpose-base-change). Added zero holes; zero sorries remain in
the delivered module. The private trace_mate is proved in full.

Validation: a diagnostic copy differing only by `set_option profiler true` compiled
successfully in 40.9 seconds against the current published library. The actual
delivery contains no profiling options and no lines over 100 characters. The
final deliver3.py checks compile the delivery and its axiom probe and run server
preflight. The theorem is proved from the existing library interfaces; no claim
is made that all transitive dependencies are already sorry-free.

## No longer needed

Removed these six proof-only imports:

- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
- Mathlib.CategoryTheory.Adjunction.Basic
- Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
- Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
- Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

The first is unused; the Mathlib adjunction API is already publicly available
through the unchanged statement imports. The other four interfaces need not be
invoked because the statement already retains an etale representative and defines
the transpose and dualizing map using the actual etale adjunction and exchange.

The revised proof does not require separate applications of
thm-sf-ambient-adjoint-class (SpecifiedExceptionalClassHom),
thm-cbc-finite-level-proetale (CanonicalFiniteLevelCompactSupportBaseChange),
def-cbc-exchange-map (LowerShriekPlusBaseChange), or
lem-weil-pbc-adjunct-counit-identity (the Mathlib counit characterization).
The first two obsolete top-level tool_uses entries are removed. Instead the
existing proved etale exchange invertibility theorem and Mathlib unit-mate
identity perform the calculation directly. The separate modules of def-pur-co-smoothness
(CohomologicalSmoothnessFiniteComparison) and def-weil-exceptional-inverse-image
(ConstructibleExceptionalAdjunctionCoefficients) are also unnecessary: the
unchanged definitions use the existing comparison-coordinate and etale APIs. Removing a direct
import here makes no assertion that its module is unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route defect was found. The original plan used larger
transported Hom and compact-support interfaces than the Lean statement needs:
the retained representative and canonical coordinate definitions allow the formal
mate calculation directly. The earlier candidate was unverified when remote
compilation stopped responding. Once compilation responded, its helper needed
association before congrArg; matching the statement's compactification bindings
corrected the shifted introductions; the final transport needed Iso.app_inv and
a final rfl. These proof errors are repaired without changing the statement.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
