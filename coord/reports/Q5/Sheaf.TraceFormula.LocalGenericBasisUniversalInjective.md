## What changed

Completed all three theorem proofs in
`Sheaf.TraceFormula.LocalGenericBasisUniversalInjective`, with their public signatures,
public imports and docstrings unchanged. All helpers are private and proved.

`geometricFibres_domain_baseChange` descends any pair of tensors to a finitely generated
intermediate field. A cardinal bound makes that field small enough to shrink into the
hypothesis universe. A linear retraction over the residue field proves that its tensor
inclusion is injective, without assuming that S is flat. Nontriviality and absence of
zero divisors then descend from the given domain hypothesis.

`maximalIdeal_map_isPrime_of_geometricFibres` identifies the closed fibre with S/mS
using the quotient--tensor equivalence and the equivalence between the residue field at
the maximal ideal and R/m.

`local_generic_basis_universal_injective` follows all three DAG steps. The scheme/ideal
residue-field comparison gives projectivity of S, hence of its finite power. The inverse
of the generic-fibre isomorphism yields a map from N to a power of the residue field;
because mS is contained in q, it extends to N_q. Factoring it modulo m proves injectivity
of the reduction of S^r -> N_q. Apply the stated local universal-injectivity criterion,
then composition, the stated localization theorem, localization and tensor right
exactness, and the stated flat-cokernel theorem. A proved ULift comparison permits testing
modules in arbitrary universes; another helper equates the compatible scalar action with
the explicit Module.compHom action in the statement.

Validation: the complete file compiled cleanly through lcompile.py (21.4 seconds).
The delivery command performs the final compile, axiom probe and preflight.
The rank-zero, zero-module and field-base cases are included by the same constructions;
finite products and empty finite sums require no positivity assumption.

## Proved and sorry left

Closed all 3 original holes:

- `RingHom.geometricFibres_domain_baseChange`
- `RingHom.maximalIdeal_map_isPrime_of_geometricFibres`
- `RingHom.local_generic_basis_universal_injective`

All three belong to node `lem-trf-local-generic-basis-universal-injective`.
No sorry remains in the item. No hole was added; no result was split off.
The four declared proof dependencies are used through their existing interfaces.

## No longer needed

No original import, declared dependency, node or module is pruned: all four original
proof-dependency imports are used. The proof follows the existing DAG route, so no node
update is required. Temporary explicit imports of Mathlib.Algebra.Module.ULift,
Mathlib.LinearAlgebra.Basis.VectorSpace, Mathlib.LinearAlgebra.TensorProduct.Finiteness,
Mathlib.LinearAlgebra.TensorProduct.Pi, Mathlib.LinearAlgebra.TensorProduct.RightExactness
and Mathlib.RingTheory.Ideal.Quotient.Basic were removed because retained imports already
expose those declarations. An exploratory import of Mathlib.SetTheory.Ordinal.Univ was
also removed; the cardinal comparison uses an embedding directly.

## Where the brief, the DAG or earlier work was wrong

No statement correction or route change was needed. The module-level source proof uses
N_p where the DAG uses N_q; the latter argument is valid because mS is contained in q,
and the proof explicitly constructs the required extension from N_q. The universe
transport does not need the more elaborate faithful-flatness argument in the original
proof sketch: the field inclusion splits linearly over the residue field.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
