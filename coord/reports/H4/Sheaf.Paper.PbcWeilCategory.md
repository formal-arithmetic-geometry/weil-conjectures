## What changed

Proved six of seven original theorem holes in `Sheaf.Paper.PbcWeilCategory`.
Inherited preadditivity uses Mathlib endofunctor algebras and full subcategories.
The geometric fiber hypotheses use finite-type base change, the source-library
fiber-dimension bound and the characteristic of the finite base field. Private
proved helpers establish additive transport, the cocycle, and literal identity
of the repeated-field transition by cancellation.

Added private proof imports `Mathlib.CategoryTheory.Preadditive.EndoFunctor`,
`WeilConjectures.AlgebraicGeometry.FibreDimension`, and
`Mathlib.Algebra.CharP.CharAndCard`. Existing public imports, signatures,
definition bodies and docstrings stay unchanged. Local transparency settings
avoid expanding the completed coefficient constructions and affect no importers.
This is a partial delivery under the multiple-hole provision of the brief.

## Proved and sorry left

Six original holes closed:

- `CategoryTheory.Endofunctor.IsoAlgebra.preadditive_exists`.
- `WeilConjectures.weilGeometricFiber_coefficientHypotheses`.
- `WeilConjectures.weilGeometricFiber_isNoetherian`.
- `WeilConjectures.weilScalarExtension_additive`.
- `WeilConjectures.weilScalarAssociator_cocycle`.
- `WeilConjectures.weilScalarExtension_refl`.

One original hole retained unchanged:
`WeilConjectures.weilScalarAssociator_exists`, node `def-wf-weil-category`.
No holes added or split off; net hole reduction is six. The cocycle and identity
proofs use the normalization of the original associator existence theorem.

## No longer needed

None. No original import, module or node is withdrawn. The item's original
proof-dependency list was empty. The finite-stage scalar system and common-stage
category route remain. The enclosing unit has empty realized statement and
proof-step lists.

Exploratory imports and proposed new coefficient-coherence modules are omitted.
No direct-image or completed-pullback coherent-family theorem is needed for the
six proofs delivered here.

## Where the brief, the DAG or earlier work was wrong

The definition node has no numbered proof plan. The associator docstring needs
joint coherence of the specified scalar and automorphism comparisons, while the
existing APIs state their individual normalizations. Searches found abstract
mates-pasting tools and an ordinary-pullback coefficient equation with a different
normalized presentation. A separate ambient equation would be needed to connect
these interfaces. The subsequent integral restriction and rational coherence
reflection were written and compiled during exploration, but the concrete Weil
associator application incurred expensive coefficient-definition conversion in
kernel checking. Those exploratory modules are preserved only in scratchpad;
they are not part of the delivery or new obligations. The original named hole
remains visible rather than being moved into an unfinished abstraction.

The identity proof takes a shorter route than its docstring: coefficient identity
and its normalized unitor make the lift idempotent with identity underlying
associator. The commuting equation is e phi = e e phi. Cancel the isomorphisms to
obtain e = id on every pair carrier, then use object extensionality and the
unchanged morphism map to obtain literal functor equality. Repeated fields,
zero objects and empty geometric fibers require no extra assumptions.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
