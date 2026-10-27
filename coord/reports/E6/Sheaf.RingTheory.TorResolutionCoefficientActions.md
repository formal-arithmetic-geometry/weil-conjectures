## What changed

Proved both theorems in `Sheaf.RingTheory.TorResolutionCoefficientActions`, preserving
all declaration signatures, public imports, definitions and docstrings.

`ModuleCat.tor_resolution_coefficient_smul` applies
`ProjectiveResolution.leftDerived_app_eq` to multiplication by the coefficient scalar,
composes with the canonical comparison isomorphism, cancels its inverse, and evaluates
the resulting equality of morphisms at the given element. Unfolding the existing
coefficient action identifies the left side definitionally.

`ModuleCat.tor_resolution_coefficient_actions` proves equality of the two R-linear
multiplication endomorphisms using `Algebra.smul_def`. Their images under the same
Tor functor are equal. The second conjunct follows from this restriction formula
and `mul_smul` for the existing B-module structure.

The existing DAG argument and unit route are unchanged; no new dependency is needed.
The supplied `ProjectiveResolution` already includes termwise projectivity, so no
separate basis-lifting construction is necessary in Lean.

## Proved and sorry left

Closed 2 of 2 holes:

- `ModuleCat.tor_resolution_coefficient_smul`
- `ModuleCat.tor_resolution_coefficient_actions`

Both belong to `lem-trf-tor-resolution-coefficient-actions`. No holes remain in the
item, no holes were added, and no statements were split off. The imported coefficient
module still has its separately assigned unfinished proofs; this delivery does not
claim to close those transitive dependencies.

Validation: server compilation succeeds for both complete proofs after removing the
redundant import. `#print axioms` reports the three standard axioms and inherited
`sorryAx` from the unfinished coefficient-module infrastructure; no new axiom
or proof hole is introduced by this packet. The proofs are
uniform in degree, allow zero coefficient rings, and require neither flatness nor
finite bases. No statement, definition, instance, or consumer was changed.

## No longer needed

Removed the redundant private import `Mathlib.CategoryTheory.Abelian.LeftDerived`:
its declarations are already publicly available through `TorCoefficientModule` and
Mathlib's Tor module. All three public imports remain necessary for the statements.
No DAG node or module is pruned. All declared mathematical dependencies are retained:
free modules, tensor products, homology and Tor specify the objects; coefficient
multiplication and resolution naturality give the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The stage-2 observation that the direct private
LeftDerived import was redundant is confirmed. No definition repair, forced
adaptation, change record, or new node is required.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
