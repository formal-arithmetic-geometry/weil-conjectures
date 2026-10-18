## What changed

Proved `AlgebraicGeometry.proper_geometricallyReduced_globalSections_isSeparable`
in `Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable`, with its
signature and public imports unchanged. The proof follows the existing four-step DAG plan.
It installs precisely `hA.toField` and the canonical `globalSectionsRingHom.toAlgebra`, obtains
finite-dimensionality from `Scheme.finite_globalSectionsRingHom_of_isProper`, and takes the
pullback along the algebraic closure. Geometric reducedness gives reduced global sections of
the pullback. Flat base change gives their pushout square. Naturality of `ΓSpecIso` identifies
the base ring and algebraic closure in that square with the actual fields, and the algebra
pushout equivalence identifies its vertex with the tensor product. Reducedness transports
through this equivalence and tensor symmetry, so the existing finite-extension separability
criterion applies.

Added the proof-only import `WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective`,
which provides the already-proved finiteness theorem and the flat-base-change API used by its
own geometric-connectedness proof. No definitions, statements, other modules, or DAG route
changed. Checked import direction: the added module does not reach this item.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.proper_geometricallyReduced_globalSections_isSeparable`
(node `lem-pc-proper-geometrically-reduced-global-sections-separable`).
Added 0 holes; split off 0 statements. There are no remaining `sorry`s in the delivered module.
The final step uses the existing declaration
`Algebra.finiteExtension_tensor_algebraicClosure_reduced_isSeparable`
(node `lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable`), whose existing
proof remains `sorry` outside this delivery. This is a proof from the stated dependency,
not a claim that the transitive theorem is already axiom-free.

Validation: the complete module compiles through `lcompile.py`; the delivery dry run also
checks the declaration signatures and axioms. No new theorem assumptions or instances are
exported. The field and algebra structures in the conclusion are exactly the original ones.

## No longer needed

Removed the proof-only imports:

- `Sheaf.Paper.EulerCharacteristicWellDefined`: a retired duplicate re-export; the proof
  instead uses the source library's finite-global-sections theorem directly.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`: its finiteness and
  vanishing-of-support declarations are unnecessary for this argument; finiteness of the
  canonical ring map is already proved in `GlobalSectionsBijective`.

No proof-dependency node is pruned: the existing four-step plan is retained, including the
finite-dimensionality part of `lem-pc-euler-characteristic-well-defined`, algebraic closure,
flat base change, qcqs, geometric reducedness, reduced sections, and the tensor criterion.
The other clauses of Euler-characteristic well-definedness need not be used here.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the assigned statement or proof plan. The initial import of
`Sheaf.Paper.EulerCharacteristicWellDefined` pointed to a retired duplicate, while the source
library already supplies `Scheme.finite_globalSectionsRingHom_of_isProper` with precisely the
canonical scalar action required here. LeanFinder returned related geometric-reducedness
facts, Loogle returned no direct separability theorem, and grep found the source finiteness
and flat-base-change declarations; there is no need for a new intermediate statement.

The proof uses no choice of arbitrary data from a sorried existence theorem. Its algebraic
closure and all ring maps, tensor products, and base-change objects are existing genuine
constructions. The final sorried dependency is a proposition and constructs no data.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
