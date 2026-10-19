## What changed

Proved `ProfiniteGrp.finiteExtension_inverseLimit_exact_pro_p` in
`Sheaf.GroupTheory.InfiniteTameInverseLimit` without changing its signature or definitions.
The proof constructs the functor of finite nonempty fibres, applies Mathlib's finite
inverse-system nonemptiness theorem, identifies and closes the kernel, and builds the
normalized topological quotient equivalence. A finite continuous quotient factors through
the image of a coordinate projection, which is a subgroup of a finite p-group.
Added the proof-only import `Mathlib.GroupTheory.PGroup`. Updated the existing node's
proof and proof dependencies, and aligned the theorem's proof docstring with this route.
Retained the earlier attempt's complete proof and checked it against the current source;
the theorem signature and both helper definitions are unchanged.

## Proved and sorry left

Closed: `ProfiniteGrp.finiteExtension_inverseLimit_exact_pro_p`
(node `lem-exc-infinite-tame-inverse-limit`), the module's one original hole.
Added holes: none. Remaining holes in this delivery: none. No split-offs.

Validation: the final proof compiled cleanly through `lcompile.py` in 3.2 seconds.
The delivery dry run also checks its declaration axioms. Explicit anonymous references
retain the three unused transition-surjectivity hypotheses without linter warnings.

## No longer needed

No existing imports removed. The node no longer needs
`lem-galois-closed-subgroup-product-finite-groups`: the existing Mathlib limit construction
already supplies compact Hausdorff profinite groups. It no longer needs
`lem-sfb-compact-hausdorff-surjection-quotient`: the continuous quotient equivalence has
continuous inverse directly by `Continuous.continuous_symm_of_equiv_compact_to_t2`.
The old proof step establishing surjectivity of every kernel projection is unnecessary:
the projection image suffices and is itself a finite p-group. Consequently `hIsurj`,
`hCsurj`, and `hPsurj` are not used in the proof; their existing binders stay unchanged.
No new proof-only Sheaf modules are imported and no new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The original fibre argument unnecessarily required surjective fibre transitions:
Mathlib's finite inverse-system nonemptiness theorem needs only finite nonempty fibres.
The original steps 6 and 8 unnecessarily required surjectivity of kernel coordinate
projections. Factoring through a coordinate image avoids that requirement. These are
simplifications below the unit level; the unit has no realized statement or step on this
node, and its route is preserved. The unchanged theorem covers nonabelian groups, the
trivial finite quotient, and the empty set of restricted coordinates.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
