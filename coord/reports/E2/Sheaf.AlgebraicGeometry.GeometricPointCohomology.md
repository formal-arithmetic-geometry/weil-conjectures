## What changed

Proved `AlgebraicGeometry.geometricPoint_etaleCohomology`. The proof identifies the
spectrum of an algebraically closed field as strictly henselian, uses the existing
strictly henselian sections-to-geometric-stalk isomorphism, and derives exactness of
`Sheaf.Γ` from terminal-section epimorphism preservation. The derived homology comparison
then gives positive-degree vanishing and the natural degree-zero isomorphism.

## Proved and sorry left

Closed the sole sorry, `AlgebraicGeometry.geometricPoint_etaleCohomology`; no sorry was added.

## No longer needed

The previous proof-only imports `Sheaf.AlgebraicGeometry.KInjectiveResolutions`,
`Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`, and
`WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport` were removed. Their nodes are not
needed by this route. The route uses the existing strictly henselian germ theorem and the
existing terminal-section epimorphism instance instead.

## Where the brief, the DAG or earlier work was wrong

The DAG's detailed K-injective and Galois-invariants route is longer than necessary here:
the source library already has the strictly henselian germ theorem, and the derived
right-derived-functor API supplies the required degree comparison.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
