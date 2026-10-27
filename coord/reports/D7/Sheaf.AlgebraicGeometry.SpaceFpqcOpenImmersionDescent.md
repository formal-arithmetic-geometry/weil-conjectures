## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_scheme_openImmersion_of_fpqc_cover`
in `Sheaf.AlgebraicGeometry.SpaceFpqcOpenImmersionDescent`, without changing its
signature, universes, public imports or hypotheses. Four proved private helpers
establish compatibility of local open images, injectivity on sections, containment
of every section in the descended open, and existence of sections by fpqc gluing.
The proof applies the existing compatible-open descent theorem, explicitly constructs
the map into the descended open using `IsOpenImmersion.lift`, and proves that map is
an isomorphism by componentwise bijectivity. Both original proof imports are used.

Updated the item's DAG proof to describe the direct cartesian lifting argument for
compatible images and the injectivity-before-gluing argument. No other existing
module or node is changed. No new modules, declarations with postponed proofs, or
nodes are introduced.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_openImmersion_of_fpqc_cover`
(node `lem-sfb-space-fpqc-open-immersion-descent`): 1 of 1 original holes closed.
Zero holes remain in the item, and zero holes are added or split off. All four
private helpers are proved.

The proof uses the existing stated theorem
`AlgebraicGeometry.AlgebraicSpace.existsUnique_section_and_eq_of_fpqc_cover`
(node `lem-a1-algebraic-space-fpqc-sheaf`), whose proof is still `sorry` in the
shared library. This is an existing dependency, unchanged by this delivery.
The compatible-open descent theorem
`AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc` is already proved.

The construction permits empty covering families and empty schemes: joint
surjectivity handles pointwise arguments, and the existing fpqc sheaf theorem
explicitly permits the empty family. No extra nonemptiness, representability or
quasi-compactness assumption is used.

## No longer needed

No imports or modules are removed. Removed the planned proof-dependency
`lem-weil-pbc-open-immersion-base-change` from this node: equality of the local
inverse-image opens follows directly by lifting maps through the two presheaf
pullback squares and using the scheme fibre-product point description. No separate
application of the open-immersion base-change theorem is needed. This does not
withdraw that theorem or its module from the library. Every other stated proof
dependency is used.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned base-change-of-open-immersions input is
unnecessary for this particular compatibility proof. Injectivity of sections is
proved first from local monicity and fpqc uniqueness, then reused to check overlap
compatibility before invoking fpqc gluing. The inherited blueprint unit route is
unchanged; this is the Tag 041X supporting argument already assigned to the item.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
