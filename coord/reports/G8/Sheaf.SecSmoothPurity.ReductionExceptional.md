## What changed

In `lean/Sheaf/SecSmoothPurity/ReductionExceptional.lean`, proved
`AlgebraicGeometry.ProEtale.reductionEtaleTateExtensionMap_isIso` with its existing signature.
The ordinary scalar isomorphism comes from uniqueness of the composed scalar-extension
adjunctions. Its root-generator equation identifies it with the previously specified map.
The derived comparison is computed on the flat degree-zero Tate complex and checked against
the actual chosen derived adjunction, including its single-complex comparison.

The proof includes `N = 0`: invertibility of zero in the global section ring forces the scheme
to be empty, so the Tate sheaf is zero and flat. Positive `N` uses the signed inverse twist.
There is no flatness hypothesis on the coefficient map, and no nonzero-ring hypothesis.

Added proof imports for K-flat acyclicity, sheafified tensor comparison, sectionwise scalar
extension and signed finite twists. Replaced the proof of
`reductionEtaleTateMap_existsUnique` by the generator-normalized adjunction construction.
Added the generic construction `reductionSingleAdjointTranspose` and factored the body of
`reductionEtaleTateExtensionMap` through it without changing its type or value. The change record
is `coord/changes/G8-reduction-etale-tate-transpose.md`; it lists every transitive consumer.
No consumer needs adapting. The existing node records the actual new proof of Step 6.
The scalar-additivity instance is local to the private scalar-proof section.

Validation: the complete sandbox module compiled through `lcompile.py` in 31.6 seconds
with no compiler diagnostics.

## Proved and sorry left

Closed 1 of the 2 original holes:
`AlgebraicGeometry.ProEtale.reductionEtaleTateExtensionMap_isIso`
(node `det-sp-reduction-exceptional`). Added 0 holes and split off 0 statements.

The sole remaining `sorry` is
`AlgebraicGeometry.ProEtale.reductionExceptional_isIso`
(node `det-sp-reduction-exceptional`). It remains exactly the original named theorem with its
original signature and thirteen-step source proof. The geometric constructible adjunction,
normalized projective-line counit calculation, chart pasting, and global isomorphism detection
are not claimed proved by this delivery. This is a partial delivery of one independently
completed hole of a module containing several holes, not a decomposition of the main theorem.

## No longer needed

None of the original imports, declared proof dependencies, nodes, or modules is pruned.
The remaining main theorem still needs its original geometric route. The newly used signed
finite-twist theorem is added as an explicit proof dependency and private import.
Removed the attempted proof import
`WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum`: the standard naturality
equation of the inverse factor comparison suffices, using explicit rewriting through the
functor composition. No unused new proof import is retained.

## Where the brief, the DAG or earlier work was wrong

The prior node said the derived invertibility calculation in Step 6 remained unproved.
That calculation is now formalized. The scalar-extension isomorphism must be identified with
the specified adjoint transpose; merely exhibiting an unrelated isomorphism between the same
objects does not suffice. The proof explicitly identifies their adjuncts through the units.

The finite-Tor comparison and localizing-preservation declarations use different category
presentations from the intrinsic constructible categories of the main theorem. They do not
immediately instantiate the requested `ReductionExceptionalRealization` records. Also,
`exceptional_coefficient_comparison` concerns literal consecutive prime-power quotient rings;
it cannot substitute for the arbitrary finite-ring map in this statement. These interfaces
are not treated as false, and their existing holes are not obstacles to using them; the
remaining work is the actual transport and normalized chart argument.

The continuation metadata reset the split-reference clock to 2026-10-19T18:22:29Z while
the persistent claim records 2026-10-19T00:25:59Z. The existing sandbox work was retained;
this packet adds no holes and does not rely on the reset. No budget file was edited.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
