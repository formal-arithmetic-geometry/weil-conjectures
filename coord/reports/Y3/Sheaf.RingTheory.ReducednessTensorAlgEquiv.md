## What changed

Proved `Algebra.isReduced_tensorProduct_iff_of_bijective` in
`Sheaf.RingTheory.ReducednessTensorAlgEquiv`, preserving its complete signature and
all existing public imports. Added the private proof import
`Mathlib.RingTheory.Nilpotent.Defs` for `isReduced_of_injective`.

Constructed the scalar equivalence with `AlgEquiv.ofBijective e he`, lifted it
using `Algebra.TensorProduct.congr` with the identity on `A`, and transferred
reducedness along the inverse and forward injective maps respectively. The
existing node's proof and proof origin now name these Mathlib implementations of
its original five steps. No statement, definition, or other module changed.

## Proved and sorry left

Closed the one original hole in
`Algebra.isReduced_tensorProduct_iff_of_bijective`
(node `lem-trf-reducedness-tensor-alg-equiv`). No holes added or split off.
No `sorry` remains in the item or elsewhere in this delivery.

Validation: `lcompile.py` compiled the final module cleanly (exit code 0, 0.9 seconds).

The construction works for the zero algebra `A`, nonreduced `A`, arbitrary
characteristic, independent universes, and the identity scalar map: it uses only
the given algebra equivalence and injectivity, without a nontriviality or
reducedness assumption on `A`.

## No longer needed

None. No imports, nodes, or modules were removed. The three existing dependencies
are Mathlib leaves: the algebra-homomorphism definition, algebra tensor universal
property, and module tensor definition are used by the equivalence construction.
Their implementations are reused through Mathlib rather than restated or reproved.
The proof does not import any holed Sheaf dependency. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. Mathlib already packages the inverse-map construction,
tensor equivalence, and nilpotent injectivity argument, so the original proof plan
needs only a short Lean implementation. Searches with LeanFinder, Loogle, the
logged grep service, and local `rg` confirmed these ingredients; the complete item
was not found as an existing declaration.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
