## What changed

Proved `WeilConjectures.normalizedIntegralTensorTower` in
`Sheaf.Paper.NormalizedIntegralTensorTower`, preserving its statement and all public imports.
The proof privately imports the finite comparison and transition-compatibility modules,
and accesses their existing proved helpers with `import all`.

For each level choose the normalized finite tensor comparison. Its quotient-compatibility
square defines a tower map by `NatTrans.ofOpSequence`. Each component is an isomorphism;
the finite comparisons' naturality assembles a natural isomorphism in both complexes.
Whisker with the existing equality between the global slice tower and the unrestricted
tower. Finally move an arbitrary finite scalar through the finite comparison and into
the first tensor factor. This proves the required formula before scalar restriction.

Validation: the complete module compiled through `lcompile.py` in 58.9 seconds,
with exit code 0 and no warnings.

## Proved and sorry left

Closed: `WeilConjectures.normalizedIntegralTensorTower`
(node `lem-pur-normalized-integral-tensor-tower`), the item's only original hole.
Added: none. Remaining in the delivered module: none. Split off: none.

## No longer needed

None. All three recorded proof dependencies are used: the finite comparison, its
transition compatibility, and the global slice/unrestricted tower equality. The
unnormalized existential tower theorem does not expose its component equations, so the
proof uses its already-proved finite comparison helper and explicitly assembles the
normalized tower. No module or DAG dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The private helpers already present in the
finite-comparison and transition-compatibility modules provide the finite comparisons
and scalar-linearity equations described by the node. They can be reused through
private `import all` without changing their visibility or duplicating their proofs.
The argument assumes no boundedness, flatness, inhabited site, or nonzero coefficients.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
