## What changed

Proved both declarations in `Sheaf.AlgebraicGeometry.IteratedTransformQuotientSupport`
without changing their signatures or public imports. The support theorem applies
`moduleStrictTransform_properties` twice, composes the quotient epimorphisms using
the tensor-pullback adjunction, and proves invertibility on the intersection open
by natural isomorphisms of restriction and tensor pullback. A private helper derives
vanishing of restricted kernel sections from naturality of the restriction unit
and injectivity of an isomorphism on sections.

The structure-sheaf theorem identifies the section-normalized adjunction with the
upstream normalized adjunction by uniqueness, applies
`tensorPullbackObjUnitToUnit_isIso` to both projections, and proves the epimorphism
and displayed equality by functoriality and associativity. All four private helpers
have complete proofs. No new public declarations, modules, or nodes were added.
The existing four-step DAG plan is followed unchanged.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Scheme.Modules.iteratedModuleStrictTransform_quotient_support`
  (`lem-trf-iterated-transform-quotient-support`).
- `AlgebraicGeometry.Scheme.Modules.iteratedModuleStrictTransform_quotient_structureSheaf`
  (the same node).

Zero holes remain in the item; zero holes were added or split off. These proofs use
the existing single-transform theorem `moduleStrictTransform_properties`, whose
proof remains an independently assigned dependency.

## No longer needed

Removed the unused proof import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`; no direct-sum or product
preservation result is needed. The epimorphism clause of
`lem-weil-pbc-module-pullback-epi-direct-sum` is used via
`Functor.preservesEpimorphisms_of_isLeftAdjoint`.

All six declared proof dependencies remain used. No DAG node, project module, or
unit step is pruned. The unit route is unchanged. The unit-compatibility theorem
`restrictFunctorIsoTensorPullback_unit` is not needed: naturality of the comparison
isomorphism suffices, while ordinary restriction-unit naturality handles sections.
Its module remains needed for `restrictFunctorIsoTensorPullback`.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect found. Read Stacks `divisors.tex`,
`definition-strict-transform` (Tag 080D), and the proof of
`lemma-strict-transform-composition-blowups` (Tag 080I). The Lean argument realizes
the two successive quotient maps and support calculation in that proof. The empty
complement, zero module and trivial centre cases require no exclusions; the generic
restriction and isomorphism argument applies to them as well.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
