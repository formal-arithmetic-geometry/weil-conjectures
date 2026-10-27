## What changed

Proved `AlgebraicGeometry.ringComplex_cech_augmentation_hom_bijective` from two
strictly smaller localization statements, in the new modules
`Sheaf.Paper.RingComplexCechLocalizedOrthogonality` and
`Sheaf.Paper.RingComplexCechConeFiltration`. Its signature, public import, original
docstring and visibility are unchanged. Added two private proof imports and opened
the namespace of the triangle exactness lemmas. No definitions, other consumers,
targets or source-library modules were changed.

The combining proof constructs the right orthogonal of all shifts of the source.
Mathlib supplies its triangulated and shift closure. Localized-module orthogonality
and the cone filtration put the cone and its shift by minus one in this class.
Exactness on the inverse rotation factors the difference of two lifts through a
zero Hom group, proving injectivity. Exactness on the augmentation triangle lifts
every map to the ring, proving surjectivity. This proof is complete Lean, rather
than a renamed application of the assigned statement.

All three modules compiled together with lcompile.py: cone filtration 4.8 seconds,
localized orthogonality 3.4 seconds, the combining proof 2.9 seconds, exit code 0.
The final packet is checked again by deliver3.py, including its axiom probe.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ringComplex_cech_augmentation_hom_bijective`
(node `lem-weil-pbc-ring-complex-cech-augmentation-hom`). The assigned module has
zero remaining holes.

Added exactly two whole-theorem holes:

- `AlgebraicGeometry.ringComplex_cech_localized_orthogonality`
  (node `lem-weil-pbc-ring-complex-cech-localized-orthogonality`). This concerns a
  single module with invertible multiplication by one ideal element, with no
  target Cech complex or augmentation Hom bijection. It includes all source shifts.
- `AlgebraicGeometry.ringComplex_cech_cone_filtration`
  (node `lem-weil-pbc-ring-complex-cech-cone-filtration`). This concerns the target
  augmentation cone and membership in a strictly full triangulated subcategory.
  It has no source complex or claim about a Hom map.

This is a decomposition: one original hole closed and two smaller holes added,
net minus one hole closed. It is not a proof without sorry dependencies. Each new
hole has a complete proof in words, its source and its own module and DAG node.
There is no data selected from an unproved existence theorem.

Checked edge cases: the empty generating list gives an isomorphic augmentation
and zero cone; for I=0 an element s of I is zero and invertible multiplication
forces the tested module to be zero; I=A forces the model to be acyclic. The zero
ring, repeated generators, and zero or nilpotent localization products all fit.
The shift by minus one in injectivity is the inverse rotation's first vertex.

## No longer needed

No existing import was removed. No node or module is claimed globally pruned or
withdrawn. The assigned proof no longer directly needs
`lem-weil-pbc-localization-flat`: this dependency is retained under the new
localized-orthogonality node, where exact localization is used. The existing
model and abstract-derived-category definitions remain statement dependencies.
The two new theorem modules are precisely the proof imports used.

No scalar-extension, K-flat replacement, ring-map comparison, or completeness
reflector is imported: none is required for this one-ring Hom argument. The unit
route and its realized nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The stated plan is mathematically sound. Its declared dependencies provide the
model predicate and localization flatness, but do not themselves state the
localized Hom vanishing or the augmentation-cone filtration. Those two parts of
the original single proof step are now explicit. The generic theorem
`CategoryTheory.bounded_complex_mem_triangulated`, already proved in
`Sheaf.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage`, supplies
the bounded-complex induction in the cone argument and is recorded as that node's
dependency; it is not duplicated.

The source file was briefly absent from the shared checkout at session start,
while its node and queue entry existed. It appeared during the session, and the
final sandbox file preserves that published X2 file's signature and docstring.
There is no withdrawal or quarantine adaptation.

Duplicate search: searched the current DAG for the Stacks label, 0A6R,
localized orthogonality and cone/localization filtration, plus the blueprint for
local cohomology and localization filtration. The only blueprint search hit for
local cohomology was `det-tf-supported-restriction`, about Frobenius supported
restriction on a curve, not either statement here. The existing
`lem-weil-pbc-ring-complex-cech-augmentation-hom` combines both parts into the Hom
bijection, whereas each new node is strictly one part. The existing
`lem-weil-pbc-ring-complex-cech-scalar-model` concerns extension along a ring map;
`lem-weil-pbc-ring-complex-cech-base-change` concerns a normalized comparison's
quasi-isomorphism. Neither states these localized orthogonality or target-only
filtration assertions. The other 0A6R references are ancestors using these steps.
The existing bounded-complex devissage is used in the remaining plan, not copied.
Mathlib searches ran through msearch.py and are recorded honestly.

## New nodes

`lem-weil-pbc-ring-complex-cech-localized-orthogonality`: source-localization
vanishing and exact extension/restriction adjunction from Tag 0A6R's finite
localization argument. Appending the chosen ideal element to a generating list
makes the contracting homotopy applicable. The node retains localization flatness
and the existing exact-derived-adjunction interface.

`lem-weil-pbc-ring-complex-cech-cone-filtration`: cancel the degree-zero identity
pair in the ordered augmentation cone, use its finite positive localization
terms, and apply the existing bounded-complex triangulated devissage. Transport
across the augmentation-compatible model isomorphism identifies the actual cone.
It is independent of the source-orthogonality node.

No change record is required: no existing statement or definition changed, and no
other group's module was adapted. Only the assigned node's proof, proof_deps and
proof_origin were updated; its statement and attachment are preserved.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
