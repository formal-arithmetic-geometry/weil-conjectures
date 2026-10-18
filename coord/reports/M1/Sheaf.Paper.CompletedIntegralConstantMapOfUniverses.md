## What changed

Proved `WeilConjectures.integralConstantQuotientOfUniverses_compatibility` in
`Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`. Simplify the constant diagram
and the successor map of the inverse sequence, then use preservation of composition
by constant sheafification and by forgetting commutativity. The underlying lifted
quotient homomorphisms agree definitionally. All existing signatures, definitions,
universes, visibility and imports are unchanged.

The complete module compiles cleanly through `lcompile.py` (4.0 seconds).

## Proved and sorry left

Closed one hole:
`WeilConjectures.integralConstantQuotientOfUniverses_compatibility`
(node `def-weil-completed-integral-coefficients`).

One of one original holes proved. Zero holes remain in this module; zero holes
added or split off. No dependency theorem with `sorry` is applied by this proof.

## No longer needed

None. No imports, nodes or modules are removed. The existing public import is
retained as the module's public interface. The proof uses the recorded quotient
and transition constructions directly; no additional dependency is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The attached node is a definition node
with empty proof/proof_deps, rather than a theorem with numbered proof steps.
The existing declaration docstring gives the compatibility argument; the quotient
factor calculation reduces definitionally, so quotient induction is unnecessary.
No route or statement changes and no new nodes are needed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
