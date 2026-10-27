## What changed

Proved `AlgebraicGeometry.exists_positiveCopyGradedQuotient` with its signature and
public definitions unchanged. Added the proved general theorem
`AlgebraicGeometry.GradedSheafAlgebra.exists_total` in
`Sheaf.AlgebraicGeometry.GradedSheafAlgebraTotal`: construct the sectionwise graded
ring presheaf, sheafify it, and prove the underlying module coproduct universal
property using local bijectivity. This is a real construction, with no choice of
an arbitrary witness from an unproved existence theorem.

The positive-copy multiplication uses bilinear multiplication maps and explicit
zero/positive degree cases. Existing quasi-coherent coproduct closure and affine
colimit evaluation give quasi-coherence and the canonical affine section-sum
bijection. The canonical symmetric algebra core universal property supplies the
quotient. Submodule-power induction proves homogeneity on every open, and the
lifts obtained by multiplying by the generator of `1_E` prove surjectivity.

Both module and node files are included. All delivered Lean lines are at most
100 characters. The three existing public signatures were compared verbatim
against the shared source and are identical. No source-library declarations changed.
The unit route is unchanged. The current item has no Lean importers; the parent
DAG dependencies and the item attachment are preserved. The public import changes
are recorded in `coord/changes/positive-copy-proof-imports.md`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_positiveCopyGradedQuotient` (node
`lem-trf-positive-copy-graded-quotient`). Added zero holes.
`AlgebraicGeometry.GradedSheafAlgebra.exists_total` (node
`lem-trf-graded-sheaf-algebra-total`) is fully proved. No `sorry` remains in either
delivered module; no unfinished theorem was split off.

## No longer needed

Removed the proof imports `Mathlib.AlgebraicGeometry.Modules.Tilde` and
`Sheaf.AlgebraicGeometry.CoherentFiniteType`.
Removed public imports `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra` and
`WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`; the signature only needs
the canonical symmetric algebra construction. The remaining public imports already provide the direct-sum and coproduct
notions used by the signature. Removed redundant imports of
`Mathlib.CategoryTheory.Limits.Shapes.Products`,
`Mathlib.CategoryTheory.Sites.PreservesSheafification`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`Mathlib.Algebra.Category.Ring.FilteredColimits`, and
`Mathlib.Algebra.Algebra.Operations` where their APIs are already publicly
imported by the other imports. The total-algebra module also drops its unused
`Mathlib.Algebra.Category.ModuleCat.Products` import and the unused additive
restriction helper.

The proof no longer directly needs
`lem-weil-pbc-module-restriction-open-immersion-colimits`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-tilde-free-module`,
`lem-weil-pbc-quasi-coherent-symmetric-algebra`, or
`lem-weil-pbc-symmetric-algebra-graded`.
Existing quasi-coherent coproduct/evaluation theorems replace the affine
construction; the symmetric core universal property and Mathlib submodule-power
induction replace the larger symmetric-algebra and grading results. Their
statement dependencies remain where the unchanged node statement cites them.
No module is withdrawn, and none of these nodes is asserted globally unused.
The old two top-level tool-use approvals are removed because the proof does not
use those tools.

## Where the brief, the DAG or earlier work was wrong

The plan said the homogeneous operations extend to the sheaf coproduct, but the
graded-structure definition only records the homogeneous operations. The added
total-algebra theorem supplies that extension and proves the module coproduct
property. The broader symmetric-algebra existence theorem does not itself pin
the source to the canonical `SymmetricAlgebraSheaf.algebra`; its already-proved
core universal property does, and is used directly.

No mathematical statement was found false. The construction works for the zero
algebra, a noninjective structure map, arbitrary positive degree, and arbitrary
module rank. Degree zero is handled separately throughout. Affine evaluation is
only asserted for affine opens.

## New nodes

`lem-trf-graded-sheaf-algebra-total` records the proved sheafification construction
of the total algebra of any graded sheaf algebra. Its source is Stacks Modules
Section 01CF and Modules on Sites Tag 03DB; its Lean theorem has no
quasi-coherence or finiteness hypothesis and no holes. The Mathlib searches and
full construction proof are recorded in the node. The source and target
statements are strict parts of the positive-copy argument, not a renamed item.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
