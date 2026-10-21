## What changed

Restored lean/Sheaf/Paper/ContinuousIntegralExchangeTargetAdjunct.lean from its
authoritative quarantine archive, repairing the missing module recorded in
coord/rework.tsv. Retained the complete proof of
AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_target_adjunct,
all private helpers and all original imports. Wrapped long lines and replaced one
flexible simp in private bounded_counit_hom by an explicit simp only list.

The proof uses the generic mate/counit identity, restriction of the derived counit,
scalar pull-comparison naturality, composition coherence on the two paths of the
commutative square, cancellation of the outer isomorphisms, and the specified
base-change adjunct formula. This is exactly the existing DAG route; its node,
Lean attachment, proof dependencies and unit realization remain unchanged.

Change record: coord/changes/F4-restore-integral-exchange-target-adjunct.md.

Validation: the restored item compiles through lcompile.py without errors or
warnings (41.8 seconds). A temporary probe containing the archived
ContinuousIntegralExchangeEquality consumer also compiles against it (3.9 seconds).
The target-adjunct theorem and that consumer both have the three standard axioms
and inherited sorryAx from existing dependencies; the restored module introduces
no sorry. A token comparison confirms that all archived source is preserved
modulo whitespace and the one explicit simplification-list proof edit.

The other archived direct consumer, CondensedQbarPullbackCube, was also tested in
a temporary probe. It fails before its square calculation: unknown identifier
finiteCoefficientDerivedToAlgCl (wrapped probe line 121; archive line 117), and
a kernel application mismatch in Mod.monoidalClosed (wrapped probe line 75).
These are defects of that separate quarantined module/dependency chain, not
forced adaptations from this restoration: no interface here changes, and the
restored private diagram helpers have their original signatures and bodies.
No consumer probe is included in the delivery.

## Proved and sorry left

The archive has zero holes. The restored item has zero holes. Holes closed: none;
holes added: none; split-off statements: none. This is a rework restoration of a
complete proof, not a newly closed hole or a decomposition. The public theorem is
integralConstructible_exchange_target_adjunct, node
lem-weil-pbc-continuous-integral-exchange-target-adjunct. Every private helper is
also proved. No sorry remains in the delivered file.

## No longer needed

None. No imports, modules or DAG dependencies were removed. The composition
coherence theorem is used twice, once on each path of the square. The archived
exchange-equality parent still needs the target-adjunct result. The archived
CondensedQbarPullbackCube also uses private generic diagram helpers through
import all; these helpers are preserved.

## Where the brief, the DAG or earlier work was wrong

The live module is missing because it was quarantined, not because its theorem
was withdrawn. The archive already contains a complete proof and zero sorry
declarations; the queue's displayed hole count does not describe that source.
Restoration, rather than another split of the obligation, repairs the assigned
defect. Mathlib search found the generic mate/counit infrastructure already used
by the proof, but no replacement for the entire specified geometric comparison.
No mathematical error or change to the proof route was found.
The separate archived Qbar consumer remains unrepaired as described in validation;
this packet restores only the assigned target-adjunct module.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
