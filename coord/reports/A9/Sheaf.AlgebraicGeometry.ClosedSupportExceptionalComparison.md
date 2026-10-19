## What changed

Proved `AlgebraicGeometry.ProEtale.closedSupportExceptionalComparison` in
`Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison`, with every existing
public signature and definition body unchanged. Added two fully proved private helpers:
a direct identity-evaluation argument for restricted natural Hom equivalences, and the
conversion from intrinsic bounded constructibility to fixed-module etale origin.

The proof uses the existing `finiteRing_constructibleDerived_origin`, the exact
canonical scalar realization, and `specifiedExceptionalEtale_boundedBelow`. It then
composes the two supplied adjunction bijections with `closedSupportCompactIso`, constructs
an isomorphism and its inverse, proves the witness-normalized uniqueness condition,
and derives the counit equation by naturality. The DAG proof now records these steps.
Added the proof-only import `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`.

Validation: server single-file compilation succeeded with no errors or warnings.
The finite-support argument covers the empty support by finite-set lower/upper bounds;
all categorical arguments apply to zero objects, empty schemes and the zero coefficient
ring. No object is chosen from an unproved mere-existence assertion: etale antecedents
are eliminated only inside proofs, and the comparison is explicitly built from the
supplied bijections.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.closedSupportExceptionalComparison`
(node `lem-pur-closed-support-exceptional-comparison`).
Added 0 holes; split off 0. There are no remaining `sorry` declarations in the item
or added modules. The two new private helper lemmas are completely proved.
Existing imported obligations are used as intended by stage 3; this does not claim that
the target import closure is axiom-free.

## No longer needed

Removed these proof imports:
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: no separate dimension
  bound is chosen; the specified exceptional boundedness theorem supplies the needed bound.
- `Mathlib.CategoryTheory.Yoneda`: direct evaluation at the two identities proves the
  required instance of Yoneda, avoiding construction of a natural isomorphism on an opposite
  full subcategory.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: the comparison uses the actual
  fixed-module compact-support functor and the existing `closedSupportCompactIso` directly.

Removed proof dependency `lem-kun-dimension-finite-type` from this item, since its role is
already encapsulated in `specifiedExceptionalEtale_boundedBelow`. Removed proof dependency
`lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`, replaced by the explicit identity
calculation above. The corresponding modules need no additional work for this item's
proof, although other branches may still need them. No module was withdrawn, and no unit
statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The old DAG proof called the etale-origin properties of B₀ and B explicitly assumed;
the actual statement asserts them. The proof now derives B₀'s origin from its given
intrinsic constructibility and B's origin from the existing specified exceptional
boundedness theorem. The old proof also omitted the finite-ring derived-origin dependency;
this existing node and the existing scalar-realization node are now recorded explicitly.
The latter realization API has the same `def-weil-pbc-proetale-modules` blueprint tag.

The existing finite-ring derived-origin theorem is used as a generic tool from another
unit; its exact essential-image criterion provides the missing conversion. The scalar
realization equivalence is another existing generic interface. These additions require
no new statement or definition and preserve the unit route. The independent reader should
check these additional tool uses; no maintainer `tool_uses` approval was added by this worker.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
