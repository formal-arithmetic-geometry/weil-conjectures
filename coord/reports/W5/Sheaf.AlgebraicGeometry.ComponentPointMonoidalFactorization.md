## What changed

Reduced `AlgebraicGeometry.ProEtale.CondensedRing.component_point_monoidal_factorization`
to one strictly smaller tensor identity, without changing its signature, public imports,
or any existing definition. Its proof now constructs the natural isomorphism and checks
both monoidal axioms. A proved private lemma compares relative and absolute tests on
finite spaces, extends along canonical profinite limits, and takes the adjunction mate.
It proves the canonical mate monoidal by an explicit unit--restriction--counit formula.
A proved private helper verifies monoidality of restriction along a natural transformation.

The new module `Sheaf.AlgebraicGeometry.ComponentTensorNormalization` explicitly
constructs the canonical monoidal structure, the ratio of the canonical and supplied unit
isomorphisms, and its scalar action as an invertible natural correction. No data is chosen
from an unproved theorem. The unit equation of this correction is proved in the item.
Only its tensor equation is left to the new theorem. The item combines that equation
with the canonical factorization using naturality and tensor composition.

Private proof imports use the proved relative-site helpers, the existing absolute
test-object theorem, profinite functor extension, monoidal sheaf restriction, and the new
normalization module. The existing DAG node records the actual comparison and correction.
No other existing library module is changed.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.component_point_monoidal_factorization`
(node `lem-zl-component-point-monoidal-factorization`). The item has zero remaining holes.

Added and remaining hole:
`AlgebraicGeometry.ProEtale.CondensedRing.component_unit_normalized_tensor`
in `Sheaf.AlgebraicGeometry.ComponentTensorNormalization`
(node `lem-zl-component-unit-normalized-tensor`). Its proof is exactly `by sorry`.

This is a decomposition: one original hole closed, one smaller hole added, net zero.
The site comparison, canonical monoidal factorization, explicit invertible correction,
correction unit equation, and assembly are proved. The residual lemma contains no
factorization, point inverse-image functor, or existentially chosen comparison.

Validation: both modules compile through `lcompile.py`; the final delivery preflight
also compiles the packet. The original theorem's binders and conclusion are preserved.

## No longer needed

None of the original dependencies is pruned. No original import is removed, no module
is withdrawn, and no adopted source declaration is changed. The proof uses the original
relative-site route. The new residual theorem does not repeat the assigned factorization.

## Where the brief, the DAG or earlier work was wrong

The original instruction to take a monoidal adjunction mate covers the canonical
inverse-image structure. The theorem actually quantifies over any supplied braided
structure on `componentInverse T`. Lean confirms that its lax tensor maps occur in the
conclusion; these are not definitionally the canonical adjunction tensor maps. Therefore
canonical monoidality alone does not finish the stated theorem. The proof explicitly
corrects the unit by its scalar ratio and isolates the tensor-normalization equation.

Slice restriction is a continuous direct image in the current implementation; no strong
monoidal instance was assumed for it. Instead the proof checks the slice counit directly.
The relative-site theorem is already proved, and its universal property gives the needed
limit comparison on underlying schemes. Empty tests remain included; no nonemptiness or
weak contractibility hypothesis is introduced.

Source checked: Hemo--Richarz--Scholbach, the paragraph before (4.1) and the factorization
sentence after (4.1), together with the proved relative-test implementation and the
library's monoidal adjunction and continuous restriction APIs. The new node records the
free-test and finite-clopen-generator argument for the remaining tensor equation.

## New nodes

`lem-zl-component-unit-normalized-tensor` states just the tensor equation of the explicitly
constructed scalar correction from the supplied braided structure to the canonical
inverse-image structure. Its docstring and node give the free-test presentation argument,
finite clopen separation step, descent through colimits, and empty-test case. The unit
identity and invertibility are already supplied by explicit constructions and proved
code. This is a substep of the original node's second proof step, in the same unit.
There are no statement or definition change records because existing interfaces stay
unchanged.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
