## What changed

Reduced `AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek` to the
constructibility step of its existing native Brown argument. The proof extracts
the native localizing adjunction from
`AlgebraicGeometry.nativeWeil_localizing_brown_adjoints`, uses the established
containment of Weil complexes in both hulls, restricts its right functor using
`AlgebraicGeometry.nativeBrownRight_preserves_weilComplex`, and applies Mathlib's
`Adjunction.restrictFullyFaithful` to obtain the actual constructible adjunction.
The two comparison isomorphisms are identities: these full-subcategory functors
retain the actual ambient objects and morphisms and the same compactification.
The theorem's signature and every public import and definition of the adopted
source module are unchanged.

Added private proof imports of `Mathlib.CategoryTheory.Adjunction.Restrict` and
`Sheaf.WeilSheaf.CompactSupportBrownConstructibility`. The latter new module
states only preservation of constructibility by an already supplied localizing
right adjoint. Its docstring and new node give the free-induction/Yoneda argument.
This is step 3 of the original plan, rather than another assertion of existence
of the desired constructible adjunction. Updated the parent proof and dependency
list to match the restriction proof.

## Proved and sorry left

Original item: five holes. One upper hole closed by decomposition, zero holes
closed without a new postponed step, one hole added, hence net zero holes closed.

The complete restriction proof replaces the hole in
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`
(node `thm-sf-weil-compact-direct-image-right-adjoint`).

The four existing holes left unchanged are:

- `AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual`
  (`lem-sf-weil-verdier-biduality`).
- `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`
  (`lem-sf-weil-upper-shriek-verdier-conjugate`).
- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`
  (`lem-sf-weil-verdier-exchange`).
- `AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso`
  (`lem-pur-weil-smooth-dualizing-complex`).

The one new hole is the entire public named theorem
`AlgebraicGeometry.nativeBrownRight_preserves_weilComplex`
(`lem-sf-native-brown-right-constructible`). No definition contains a hole.
The existing proofs of lisse biduality, the lisse Hom--tensor formula,
constructibility of Verdier duality and triangulated exactness are preserved.

## No longer needed

No existing imports, declarations or modules were removed or withdrawn.
No mathematics is claimed globally pruned. The parent's free-derived resolution,
induction comparison and geometric Brown constructible comparison dependencies
now occur in the new preservation node, where their argument is needed; the
formal restriction in the parent does not use them directly. The native Brown
adjoints and framework dependencies remain in the parent. No unit route is
bypassed (`sk-prop-sf-biduality-general` has no realized steps).

## Where the brief, the DAG or earlier work was wrong

The Verdier-exchange node's declared dependencies
`Sheaf.Paper.NativeWeilDualizingHomTransposition` and
`Sheaf.Paper.WeilCompactStructureTensorComparison` already reach the item module.
The former imports it directly; the latter reaches it through
`Sheaf.Paper.NativeCompactProjectionFormula` and
`Sheaf.Paper.DerivedWeilOperations`. They cannot be proof imports of this module
without a cycle. Those other declarations and their nodes were not changed.

The exceptional-adjoint statement does not assume absolute separatedness of X or
Y. The existing `NativeExceptionalForgetful.Space` interface assumes both, so its
representing-counit theorem cannot directly prove this general declaration.
The reduction retains exactly the existing hypotheses, including
quasi-separatedness of the target, and follows the native localizing plan.

The new preservation statement was checked on empty schemes and identity maps:
the localizing right adjoint is unique up to natural isomorphism, so these reduce
to the zero functor and identity restriction, respectively. Arbitrary choices of
the hull preservation proof do not change its functor or maps. No assumption that
all localizing objects are constructible is made.

## New nodes

`lem-sf-native-brown-right-constructible` isolates the constructibility part of
step 3 of `thm-sf-weil-compact-direct-image-right-adjoint`. It takes an actual
localizing adjunction as input and asserts only that its right functor sends
native Weil inputs to native Weil objects. Its proof plan compares the forgotten
right adjoint with the geometric one via the free-derived adjunction and the
induction comparison, then applies geometric constructible preservation and
exact conservative forgetting. It introduces no chosen adjoint or dualizing data.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
