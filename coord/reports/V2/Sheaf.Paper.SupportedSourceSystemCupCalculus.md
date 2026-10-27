## What changed

Proved both declarations in `Sheaf.Paper.SupportedSourceSystemCupCalculus` from the existing normalized shifted-tensor morphism calculus. Added proved private helpers for precomposition and shifted postcomposition naturality of B, degree transports, nested cup expansion, and exact pullback of B. All public signatures and definitions are unchanged. The proof works on arbitrary derived morphisms and retains all label, weight, and degree transports.

The algebraic theorem applies the local signed calculus to the original flat source sheaves. It cancels source multiplication isomorphisms, applies the signed associativity/symmetry identities, and transports the coefficient coherence equations through the shift functor. The pullback theorem derives the general B pullback identity from the two-shift coherence square and tensor comparison naturality, then uses precisely the supplied source and coefficient equations.

## Proved and sorry left

Closed 2 of 2 original holes:

- `SheafOfModules.supportedSourceSystemCupCalculus`.
- `SheafOfModules.supportedSourceSystemCupPullback`.

No holes added, no split statements, no `sorry` left in the delivered module. The proofs use the already stated theorems `shiftedTensorMorphismCalculus_local` and `shiftedTensorMorphismCalculus`, which remain separate existing items; this report does not claim their underlying holes closed.

## No longer needed

Removed the private proof import `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints` and the direct proof dependency `lem-pur-derived-tensor-additive-constraints`. Naturality is obtained directly from bifunctoriality and the canonical comparison's naturality. Iterated B has arbitrary derived sources, and its associative identity only requires flatness of the original three source sheaves. No ordinary tensor-flatness or degree-zero comparison is needed in this assembly. This is local dependency pruning; the dependency module remains needed elsewhere and is not withdrawn.

All public imports are retained. No module or declaration is withdrawn. No unit realization or unit proof route changes.

## Where the brief, the DAG or earlier work was wrong

The original Step 1 and Step 2 unnecessarily invoked tensor closure of flat degree-zero sources. The local signed calculus already states associativity for three original flat sources, including its iterated arbitrary-derived-source B expressions. Updated the four proof steps and proof dependencies to match the Lean assembly. No mathematical statement, hypothesis, definition, or source-library declaration changed.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
