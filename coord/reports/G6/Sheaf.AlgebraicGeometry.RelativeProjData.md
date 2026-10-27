## What changed

Filled the six proofs in `Sheaf.AlgebraicGeometry.RelativeProjData`, preserving every
public declaration signature, public import, definition and instance body. Added proved
private helpers for the homogeneous sheaf projections and locally finite presentations
of sections. Updated the six attached route nodes to describe the actual arguments.

The internal direct-sum argument uses compactness of the affine open and the sheaf
coproduct universal property. The underlying abelian-sheaf forgetful functor preserves
coproducts; sheafification gives locally finite presentations; a finite subcover gives
one finite set of degrees; orthogonal projections and sheaf separation reconstruct the
section. The same projections prove injectivity of recomposition. This argument works
also for the empty affine open and requires no quasi-coherence of the summands.

The irrelevant-ideal argument applies the existing affine-section base-change theorem
only to the total quasi-coherent algebra module. Tensor induction after homogeneous
projection proves membership in the extended ideal. This follows the total tensor
isomorphism in Stacks, Constructions, lemma-proj-inclusion (01NO). Restriction naturality
and the two input algebra equations prove the four remaining elementary assertions.

Added private proof imports of:

- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`;
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
- `WeilConjectures.Mathlib.Algebra.Category.Grp.Colimits`;
- `Mathlib.Topology.Sheaves.LocallySurjective`;
- `Mathlib.Algebra.Category.Grp.EpiMono`;
- `Mathlib.CategoryTheory.Sites.Abelian`.

The compactness calculation is a private lemma for abelian sheaves and is then specialized
to the underlying module sheaf. This avoids changing any type-alias reducibility settings.

Searches used the required remote msearch LeanFinder, Loogle and grep services, as well
as local searches of both library roots and Mathlib. Queries included sections of
coproducts on compact or affine opens, `DirectSum.IsInternal`, and
`HomogeneousIdeal.irrelevant_le`. The source's quasi-coherent affine-section theorem
fits the total algebra directly. Mathlib supplies coproduct projections, ideal generation
by positive homogeneous components, local-surjectivity characterizations, and compact
finite subcovers. No ready-made section-level internal-sum theorem was found.

## Proved and sorry left

Closed six original holes:

- `AlgebraicGeometry.RelativeProjAlgebra.sectionGrade_one`
  (`lem-route-section-grade-one`);
- `AlgebraicGeometry.RelativeProjAlgebra.sectionGrade_mul`
  (`lem-route-section-grade-mul`);
- `AlgebraicGeometry.RelativeProjAlgebra.sectionGrade_internal`
  (`lem-route-section-grade-internal`);
- `AlgebraicGeometry.RelativeProjAlgebra.restriction_mem`
  (`lem-route-restriction-mem`);
- `AlgebraicGeometry.RelativeProjAlgebra.irrelevant_le`
  (`lem-route-irrelevant-le`);
- `AlgebraicGeometry.RelativeProjAlgebra.unit_mem` (`lem-route-unit-mem`).

No holes added or split off. No `sorry` remains in the item or its private helpers.
The complete file compiled through lcompile in 9.9 seconds; an unused simp argument
reported by that run was removed before the delivery checks. All existing public
signatures were also compared verbatim and remain unchanged.

## No longer needed

No existing public import or module is removed; no module withdrawal is claimed.
The original docstring plan of establishing quasi-coherence of each homogeneous
summand and transporting an affine equivalence through its coproduct is unnecessary:
compactness and the coproduct projections prove the section decomposition directly.
The irrelevant-ideal proof likewise does not require separately proving affine base
change for each summand. The route was also compared with the stage-1 plans that landed during this session.
The internal-sum proof does not use these declared dependencies:

- `lem-route-qcoherent-direct-summand`;
- `lem-weil-pbc-quasi-coherent-module-coproduct-closure`
  (`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`);
- `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections`
  (`WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`);
- `lem-route-range-internal-of-bijective-sum`.

The compactness argument proves the needed finite presentations and independence directly,
so no affine quasi-coherent coproduct comparison or separate range lemma is needed.
The irrelevant-ideal proof does not use `lem-route-graded-basechange-irrelevant`:
total tensor induction after sheaf projection proves the ideal inclusion directly.
No withdrawal of any of these nodes or source declarations is claimed. The unit statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

At session start the six route nodes were provisional, with empty proof plans despite
their Lean docstrings describing arguments. Stage-1 refinements landed while this proof
was being written. The delivery preserves those newer statements, statement dependencies,
searches and reviews, and changes only their proof-plan fields to describe the compiled
proofs. The first delivery check detected the stale node snapshots; they were refreshed
before resubmission.
The original internal-sum and irrelevant-ideal docstrings described longer routes;
the new proofs avoid those intermediate constructions without changing any statement.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
