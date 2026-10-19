## What changed

Proved `CategoryTheory.site_inverse_image_bilinear_adjunction` without changing its
statement, its bilinear-map structure, or its unit-section definition. The transpose
is the explicit two-unit formula. Its injectivity, surjectivity, and naturality are
proved on sections. Three-input uniqueness reflects the two separate additivity laws.

Added `Sheaf.CategoryTheory.Sites.InverseImageUnderlyingAdjunction`, with the explicit
`SiteSectionMultimap` structure and a fully proved finite-input universal property.
Private helpers construct and normalize the underlying-set adjunction comparison from
the proved abelian-object component, Mathlib's lifted adjunction, and uniqueness of
left adjoints. Product sections are identified with tuples using canonical comparisons.
No arbitrary existence witness is used to define any data.

The resumed `lcompile.py --all` check passes for both modules without warnings.
The retained sources were compared with the current shared repository: the original
public declarations and public imports are unchanged, the new node name is unused,
and the dependency declarations still provide the recorded interfaces. A standalone compile of both sources with `#print axioms`
confirmed that both public theorems use only propext, Classical.choice, and Quot.sound.
Both import directions were checked. The original statement's
independent site universes and common value universe are preserved. The empty family
is covered by the same product proof; zero sheaves and the identity site impose no
extra hypotheses. The new underlying theorem is proved rather than left as a split-off.

## Proved and sorry left

Closed the original hole in `CategoryTheory.site_inverse_image_bilinear_adjunction`
(node `lem-sfb-site-inverse-image-bilinear-adjunction`): 1 of 1 original holes proved.
Also proved `CategoryTheory.site_inverse_image_multimap_universal`
(node `lem-sfb-site-inverse-image-multimap-universal`) and all its private helpers.
There are zero sorries in either delivered module. Holes added: zero. Split-offs: zero.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects` and
`Mathlib.CategoryTheory.Monoidal.CommGrp_` from the item module. The new helper imports
the already proved `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian`
component directly. The mixed abelian/ring wrapper node
`lem-weil-pbc-sheaf-algebraic-structures-objects` is no longer needed by this proof,
and its obsolete top-level tool-use entry was removed. Its ring component is not
needed here. The lifted abelian-group-object adjunction remains used inside the new
proved helper node, rather than being a direct dependency of the main theorem.
The size and site conventions remain in the statements. No unit statement or unit
proof step is bypassed. Removed two unused private tuple-map lemmas from retained work.

## Where the brief, the DAG or earlier work was wrong

Earlier sandbox work began with a complete main proof conditional on an unproved
multimap universal property, without a node or report. That universal property is now proved
in full and has a matching node. A misplaced set_option before the theorem caused a
parser error; it was moved before the docstring. Elaboration options in the existing
module are scoped to the helper section or theorem proof. An earlier dry run required
a change record for the private-helper context; that record has been added. No mathematical statement
was disputed or changed. The generic finite-product argument works from the recorded
continuity, right-adjoint, and set-inverse-image finite-limit assumptions; it does not
need to use the additional covering witnesses, which are retained unchanged.

## New nodes

`lem-sfb-site-inverse-image-multimap-universal`: a proved finite-input version of the
underlying-set adjunction, with the actual canonical abelian units. It has no remaining
proof obligations. Its proof uses the existing abelian-object component and Mathlib
lifted adjunction, then the additive finite-product comparison and projection
naturality. The context-only change record is
`coord/changes/B8-inverse-image-bilinear-private-context.md`; it lists all downstream
modules and explains the section-local helper variables and elaboration options.
All existing signatures and public imports are unchanged; the new module is
imported only for the proof.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
