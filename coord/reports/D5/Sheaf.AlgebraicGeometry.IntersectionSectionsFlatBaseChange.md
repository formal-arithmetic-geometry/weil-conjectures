## What changed

Proved both original theorems in
`Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange` with unchanged signatures.
Private helpers establish the inverse-image adjunction unit equation, identity and
composition of section maps, restriction compatibility, reindexing of the same subset,
scalar compatibility, and the pure-tensor associator formula. Tensor induction proves
naturality and iteration for the actual canonical maps.

For bijectivity, use `qc_open_flat_section_diagram` and
`sections_intersection_structure_colimit`. A direct elementwise tensor argument replaces
the module-colimit assembly: every tensor has a representative at one finite stage;
target representatives prove surjectivity; eventual vanishing and stagewise injectivity
prove injectivity. Restricting further to the union of the original and vanishing stages
handles the difference between inclusion of opens and inclusion of finite index sets.
Updated the node's proof and dependencies to this argument, and the theorem docstring.

Added a private concrete algebra restriction map; it is constructed from the actual
restriction homomorphism, with its scalar equation proved, and has no proof holes.
Local irreducibility attributes for `intersectionSheafMap`, `intersectionStructureSheaf`
and `intersectionInclusion` stop repeated expansion of inverse-image sheaf construction.
They are local to this file; exported definitions, attributes and signatures are unchanged.
Removed the two unused private imports concerning module tensor adjunctions and colimits.

Change record: `coord/changes/intersection-sections-local-transparency.md` documents
the local attributes and all 35 downstream consumers. Preflight requested this record
for its conservative attribute-command check; no consumer adaptation is required.

## Proved and sorry left

Closed 2 original holes, with 0 added:

- `AlgebraicGeometry.Scheme.intersectionScalars_map`.
- `AlgebraicGeometry.flat_affine_intersection_sections_base_change`.

No `sorry` remains in this delivery. No intermediate theorem is split off.
The geometric stage-comparison theorem is already proved in the shared library.
The imported intersection-section colimit theorem remains its owner's proof obligation;
this item uses that declared result.
All newly added private helpers are proved.

Validation: the complete sandbox compiled through lcompile.py --all with exit code 0
on 2026-10-23 (33.6 seconds), with no compiler warnings or errors. Checked the existing
sandbox proof and node against the current shared source after the interrupted turn.

## No longer needed

Removed private imports:

- `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`.
- `Mathlib.CategoryTheory.Adjunction.Limits`.

The proof does not use `lem-a1-directed-algebra-tensor-comparison` or its module
`Sheaf.RingTheory.DirectedAlgebraTensorComparison`; the direct tensor representative
argument proves just the required bijectivity without module colimits, a distinguished
linear equivalence, or its uniqueness assertions. The node proof dependency is removed.

The parent no longer needs `lem-weil-pbc-tensor-commutes-with-colimits`; its obsolete
parent `tool_uses` entry is removed. This does not withdraw either declaration or alter
other consumers. The qcqs flat-global-sections dependency remains needed through
`QcOpenFlatSectionDiagram`. Tensor universal-property data remain used in the canonical
maps; the compatibility proofs use tensor induction. No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old assembly was stronger than necessary. Bijectivity needs source representatives
and target eventual equality, but no source eventual equality or module-colimit universal
property. This also avoids the fixed index-universe restriction in the algebra child.
The finite-stage geometry and the unit route are retained. Empty intersection spaces,
zero rings and empty individual opens require no exception in the proof; the nonempty
index hypothesis is used for finite-stage representatives.

Searches used the prescribed msearch leanfinder, loogle and grep services, and direct rg
on the project and pinned Mathlib sources. Loogle found the adjunction unit equation;
no existing full intersection base-change theorem was found. The source read was
Stacks `more-groupoids.tex`, `equation-sections-of-intersection` and the proof of
Tag 0APJ (`lemma-affine-base-change`), together with the current node dependencies.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
