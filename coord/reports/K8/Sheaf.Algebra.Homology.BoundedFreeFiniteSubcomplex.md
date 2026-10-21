## What changed

Proved `CochainComplex.exists_bounded_finite_free_subcomplex` in
`Sheaf.Algebra.Homology.BoundedFreeFiniteSubcomplex`, with its statement unchanged.
The proof follows Stacks Tag 0FNR by descending induction with the explicit support
interval [t,b]. It constructs the degree-t submodule from finitely many coordinates
of a free basis and applies the induction hypothesis directly to the differential
images of those generators, together with the original higher-degree elements.
Two proved private helpers construct the finite coordinate submodule and identify
the zero submodule with the rank-zero free module. The node's proof records this
minor simplification. No public declarations or definitions were added.

Validation: the final module compiles through `lcompile.py` in 2.2 seconds,
with no errors or warnings. The original theorem signature and public imports
are preserved, and every Lean line is at most 100 columns.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.exists_bounded_finite_free_subcomplex`
(node `lem-zl-bounded-free-finite-subcomplex`).
Added zero holes and split off zero statements. No `sorry` remains in the delivery.
The helpers `CochainComplex.finite_coordinate_submodule` and
`CochainComplex.bottom_finite_free` are also fully proved.

## No longer needed

No existing imports, dependency nodes, or modules are pruned.
The sole declared dependency `def-weil-abstract-derived-category` is retained.
The source proof's second basis and its coordinate expansion are unnecessary:
the induction hypothesis accepts the finite set of differential images directly.

## Where the brief, the DAG or earlier work was wrong

No statement or dependency was wrong. The second coordinate expansion in steps
3–5 was redundant and has been simplified in the node's proof.
The empty list, elements above the upper bound, negative degrees, and the zero
ring are handled uniformly by the construction, without extra hypotheses.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
