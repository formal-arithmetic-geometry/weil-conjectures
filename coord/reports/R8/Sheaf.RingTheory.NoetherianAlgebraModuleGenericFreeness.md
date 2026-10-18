## What changed

Proved `Module.noetherian_algebra_module_generic_freeness` in
`Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness`, with its original signature,
universes, hypotheses and visibility unchanged. All public imports are unchanged.
The proof imports only Mathlib; all five private helper theorems are proved.

The proof reduces a finite-type algebra to a polynomial algebra by restricting scalars
along a surjective finite polynomial presentation. It then inducts on the number of
variables. The zero-variable case uses Mathlib's finite-presentation free-localization
theorem over the fraction field. For the successor case, the degree filtration in the
last variable has graded pieces that are quotients of one finite module. Their kernels
stabilize, leaving finitely many modules to which induction applies. After multiplying
their localization elements, all graded pieces are free. Splitting their quotient maps
and constructing the independent sum of their ranges proves freeness of the exhaustive
union. The polynomial filtration is adapted from the proved generic-flatness argument
`exists_flatAway_of_mvPolynomial` in
`WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`; that module is not imported.

Updated the theorem docstring and the assigned node's `proof`, `proof_deps` and
`proof_origin` to describe this actual route. Removed the obsolete normalization
approval from the node's top-level `tool_uses`. No existing statement or definition was
changed; no consumer adaptations or change records are needed.

## Proved and sorry left

Closed the sole original hole:
`Module.noetherian_algebra_module_generic_freeness`
(node `lem-pur-noetherian-algebra-module-generic-freeness`).

Holes closed: 1. Holes added: 0. Actual holes remaining in the delivered Lean file: 0.
No split-offs. The private further-localization, equivalence-transport, exhaustive
filtration, localized-filtration and polynomial-induction helpers are all proved.

The final proof compiled without warnings using `lcompile.py` (36.1 seconds with the
axiom inspection). `#print axioms Module.noetherian_algebra_module_generic_freeness`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the original proof-only imports:

- `Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness`
- `Mathlib.RingTheory.NoetherNormalization`
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization`
- `Sheaf.RingTheory.NoetherNormalizationOverDomain`

Removed these planned dependencies from the node's `proof_deps` and from its proof:

- `lem-zl-noether-normalization-field`
- `lem-zl-noether-normalization-dimension`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-noether-normalization-over-domain`
- `lem-weil-pbc-noetherian-module-prime-filtration`

The corresponding normalization-over-domain entry in top-level `tool_uses` is withdrawn.
The degree-filtration route uses neither Noether normalization, generic Krull dimension,
nor a prime filtration. The normalization modules listed above and Mathlib's associated-prime/prime-filtration
input are unnecessary for this item's proof;
no assertion is made that other parents no longer need them. Mathlib leaves for finite
presentation, principal free localization, finite-type polynomial presentations and
Noetherian stabilization replace this portion of the planned route. The unit
`sk-prop-sf-cbc` has no realized statement or proof-step nodes that this route bypasses.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original dimension-induction plan
is mathematically valid, but the library already contains a proved polynomial-filtration
argument for generic flatness. Upgrading that argument with explicit splittings gives a
complete freeness proof without the planned normalization and prime-filtration inputs.
The updated node and docstring distinguish this route from the cited Stacks proof.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
