## What changed

Proved `AlgebraicGeometry.Etale.ambientAffineTranslation_lineSquare` by the
horizontal-isomorphism criterion and the coordinate projection equations.
Proved `AlgebraicGeometry.Etale.ambientAffineTranslationTrace` from the existing
universal translation multiplier and affine constant-section zero-detection theorems.
Zero-section rigidity makes the universal multiplier identically one. The specialized
multiplier witness fixes the actual action and trace; sheafification extensionality
makes its scalar map identity and cancellation of the inverse trace proves the equation.
The coordinate vector is specialized by `homOfVector` followed by the tower isomorphism.
No hypotheses or conclusions changed. Empty bases, dimension zero, and A=0 require
no case exclusion in this proof.

Moved the existing concrete definitions and proved coordinate square into
`Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction`, publicly reexported by
the item. Changed the unclaimed `Sheaf.Paper.UniversalTranslationMultiplier` public
import to that construction module, preserving all its declarations verbatim. This
breaks the pre-existing implementation-level cycle between a theorem and its
construction dependency. Change record:
`coord/changes/S6-affine-translation-construction-import-layer.md`.

## Proved and sorry left

Closed 2 of the item's 2 holes:

- `AlgebraicGeometry.Etale.ambientAffineTranslation_lineSquare`
  (now in AmbientAffineTranslationConstruction; existing construction node
  `def-trf-ambient-affine-translation-trace`).
- `AlgebraicGeometry.Etale.ambientAffineTranslationTrace`
  (`lem-trf-ambient-affine-translation-trace`).

Added zero holes and split off zero statements. No sorry remains in the item or
construction module. The adapted dependency retains its one existing hole,
`AlgebraicGeometry.Etale.purUniversalTranslationMultiplier`
(`lem-pur-universal-translation-multiplier`); this delivery does not alter that proof.
The item is proved from that existing stated dependency, rather than claiming its
entire transitive axiom closure is already closed.

## No longer needed

The original proof-only imports are unused by the completed assembly:
`Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange`,
`Mathlib.Topology.NoetherianSpace`, `Mathlib.Topology.LocallyConstant.Basic`,
`Sheaf.Paper.ConstantSheafSectionsLocallyConstant`,
`Mathlib.CategoryTheory.Sites.ConstantSheaf`,
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`,
`Mathlib.Algebra.MvPolynomial.Basic`, `Mathlib.RingTheory.Spectrum.Prime.Topology`,
and `WeilConjectures.Compactification.Noetherian`.
They are removed from the construction and item files as direct proof imports.
Original public dependencies are retained through the construction module's public
imports and the item's public reexport.

The assembly no longer directly needs proof dependencies
`lem-amb-unbounded-compact-support-comparisons` or
`lem-asd-etale-finite-twist-pullback`: the specialized witness already fixes the
explicit Tate/exchange composite. Both remain necessary for the concrete construction
and multiplier theorem, so this is not a claim of global withdrawal.
Likewise the old direct tool entries `lem-amb-affine-space-top-trace`,
`lem-amb-compact-action-base-change`, and
`lem-weil-pbc-constant-sheaf-sections-locally-constant` are subsumed by the existing
multiplier theorem. The DAG proof and proof_deps now match the Lean assembly.
No module is withdrawn or globally pruned. The new construction module retains every
original public dependency, while its proof uses only declarations from that public
closure.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is usable. Its Lean dependency was not importable directly:
UniversalTranslationMultiplier publicly imported the item for definitions while the
item's recorded proof needs that theorem. The existing separate definition node made
it possible to move the implementation without inventing a new mathematical interface.
The plan's final explicit base-change cancellation can be shortened: the theorem's
specialized witness already supplies the scalar conjugation for the exact maps in the
goal, so cancelling its trace inverse suffices.

Searches via msearch leanfinder, loogle and grep found no shorter trace theorem in
Mathlib; local searches found the existing coordinate isomorphism API and sheafification
extensionality. No new mathematical statement or node was needed.

Validation: all three delivery modules compiled through lcompile.py. The final item
compile completed cleanly in 10.2 seconds; the construction and adapted dependency
also compiled. An overlay import-graph check found no cycles. Text comparisons
confirmed unchanged main theorem signature, unchanged moved definition bodies, and
only the required import change in UniversalTranslationMultiplier.

## Forced adaptations

### Sheaf.Paper.UniversalTranslationMultiplier
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
