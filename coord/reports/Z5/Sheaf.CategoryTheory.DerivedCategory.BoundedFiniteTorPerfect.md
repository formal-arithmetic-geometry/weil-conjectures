## What changed

Proved `DerivedCategory.exists_bounded_finite_projective_model_of_torAmplitudeIn` in
`Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect`, with its signature and public
imports unchanged. The proof implements the six steps of the existing node:

1. Finite cycles and their quotient give finite cohomology. Apply the Noetherian
   pseudo-coherence criterion with the original upper term bound.
2. Testing Tor amplitude against the tensor unit gives the cohomological bounds.
3. Apply `exists_finiteFree_model_isStrictlyLE` to obtain a finite-free model zero above `b`.
   The proved generic `CochainComplex.kFlat_of_isStrictlyLE_of_flat` supplies exactly the
   categorical K-flatness needed by `QObjTensorSingleFunctorObjIso`. This is the categorical
   version of the bounded-flat K-flatness step already in the node, avoiding conversion
   through acyclicity. Derived tensor comparison gives universal exactness in degree `a-1`.
4. Apply the stated `Module.Flat.opcycles_of_exactAt`. Show finite presentation of the
   opcycles from its cokernel sequence and finite generation of the differential's range;
   apply `Module.Flat.projective_of_finitePresentation`.
5. Use Mathlib's quotient truncation `P.truncGE a`, transport finite generation and
   projectivity through its term isomorphisms, and invert its quasi-isomorphism under `Q`.
   Check vanishing in each of the three cases below, at, and above `a`.
6. Over a local ring apply `Module.free_of_flat_of_isLocalRing` to the bottom opcycles;
   the higher terms retain their original free bases and zero terms are free.

No new declarations, definitions, statements, DAG nodes, or consumer adaptations were needed.
All unit steps remain unchanged. The mathematical route and dependencies of the existing DAG
node still describe the proof. Added the private import
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` for the categorical K-flatness API.
The final module compiled without warnings in 4.1 seconds through `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.exists_bounded_finite_projective_model_of_torAmplitudeIn`
(node `lem-weil-bounded-finite-tor-perfect`).

Added 0 holes. There are no `sorry`s left in the delivered module and no split-offs.

## No longer needed

Removed these private imports:

- `Mathlib.RingTheory.Flat.Basic`: its flatness API is already available from the retained
  finite-presentation/flatness imports.
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`: use the already-proved categorical bounded-flat
  K-flatness theorem directly, instead of its ordinary-module acyclicity specialization.
  The mathematical bounded-flat K-flatness fact remains needed, so its DAG node
  `lem-pc-module-bounded-flat-kflat` is not pruned.
- `Sheaf.RingTheory.RingPseudoCoherent`: the definition is already publicly imported by the
  two retained pseudo-coherence theorem modules. Its definition node remains needed.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`: the required definitions are
  available through the retained source imports.

No mathematical dependency nodes are removed: the proof follows the existing six-step plan.
No unit statement or step is bypassed. These are removed direct imports, not a claim that the
modules disappear from every target's transitive import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. The source already exposes categorical
K-flatness, quotient truncation and the derived tensor comparison; no new intermediate
statements are necessary. The local clause uses the same explicitly constructed truncation.
The construction also handles zero complexes and zero terms, with no nontriviality assumption
on the ring. No data is chosen from an unproved mere-existence theorem to define a new object.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
