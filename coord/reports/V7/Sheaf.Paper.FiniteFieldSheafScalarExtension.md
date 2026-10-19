## What changed

Proved `AlgebraicGeometry.Scheme.finiteFieldSheafScalarExtension` with its existing
statement and public definitions unchanged. Added proof-only imports of
`Sheaf.Paper.ProEtaleConstantModuleEncoding`,
`WeilConjectures.SixFunctors.ProEtale.ScalarExtension`, and the new, fully proved
`Sheaf.Paper.FiniteFieldLocalTensorModel`. Updated the DAG proofs to match Lean.

Exactness follows by conjugating the existing scalar adjunction through the
constant-module encoding equivalences. Naturality of the constant-section unit
proves the restriction square. Field flatness and the proved source-library
sheaf scalar-extension theorem give finite-limit preservation; the adjunction
gives finite-colimit preservation. The proof retains the original stratification
and covers, proves the tensor models finite, transports constructibility through
isomorphisms, and uses short-complex homology comparison and preservation of zero
objects for the unchanged cohomological interval.

The new local-model theorem is proved in full. Explicit tensor/restriction Hom
equivalences and module sheafification give the tensor adjunction in the actual
site universes. Naturality of the ring inverse-image unit gives the restriction /
direct-image square; conjugation gives the inverse-image tensor comparison.
For slice restriction, Mathlib's `overPushforwardOverAdj` and naturality along
the product projection give the analogous comparison. Finally, constant modules
are left adjoint to constant-scalar sections at the terminal site object.
Naturality of the constant-ring unit and uniqueness of left adjoints identify
extension of a constant module with its constant tensor model. Apply the slice
extension functor to the supplied local isomorphism and compose these comparisons.

## Proved and sorry left

Original holes: 1, in `AlgebraicGeometry.Scheme.finiteFieldSheafScalarExtension`.
Closed holes: 1, that declaration. Added holes: 0. Remaining holes in the item: 0.
The new `AlgebraicGeometry.Scheme.finiteFieldScalarExtension_localModel`, node
`lem-sf-finite-field-local-tensor-model`, is also proved; it is not a split-off
obligation. Every private helper is proved, and no definition contains a hole.
This is a proof from existing library declarations, some of which still depend
on existing `sorry`s; it is not a claim that the whole dependency closure is closed.

Both modules are checked by the server compiler and by the required delivery gate.
Edge cases: zero modules, empty schemes or slice objects, nonfinite local models,
identity field maps, unbounded complexes, and one-degree cohomological intervals
require no extra hypotheses. The local theorem works for arbitrary scheme maps
and fields, with no finite-field assumption.

## No longer needed

Removed the following original direct proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (available through statement imports).
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `Sheaf.Paper.ProEtaleConstructibleSheaf` (available through statement imports).

The proof no longer uses `lem-pc-sites-module-sheafification-tensor`,
`lem-pe-constant-left-module-inverse-image`,
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`, or
`lem-sfb-localized-site-tensor-restriction`. Their generic interfaces are replaced
by proved adjunction comparisons at the actual independent site universes.
The parent's obsolete direct tool-use entries for the first three were removed.
The finite-basis / finite-biproduct construction and
`def-weil-proetale-geometric-stalk` are also unnecessary: field flatness gives
exactness and finite local tensor models give finiteness directly. No existing
public import or source module was withdrawn. Inverse-image and constructibility
definitions remain needed through the existing statement imports; only their
redundant direct proof imports were removed. Whole-library pruning is left to
the maintainer's import-closure calculation.

## Where the brief, the DAG or earlier work was wrong

The older plan verifies finite stalks after choosing a basis. The coefficient
universe constructibility predicate already asks for finite local constant
models, so no stalk calculation is needed. Older generic tensor interfaces
identify the site object and Hom universes. This site has object universe u+1
and Hom universe u; the delivered private tensor adjunction keeps these distinct.

The existing Lean conclusion places the complex assertion inside the preceding
F / constructibility quantifiers, and places the vanishing assertion inside the
final degree quantifier. The proof preserves that exact signature. The unit has
no realized statement or proof steps to bypass. No statement is disputed.

## New nodes

`lem-sf-finite-field-local-tensor-model` records the proved local tensor-model
comparison in `lean/Sheaf/Paper/FiniteFieldLocalTensorModel.lean`. It is strictly
smaller than the parent: it asserts no exactness, constructibility, finiteness,
homology or boundedness. It is fully proved and leaves no work for another group.
The retained LeanSearch, Loogle and grep searches found no matching declaration.
No definition or existing statement was repaired. The change record
`coord/changes/finite-field-scalar-extension-proof.md` documents the new helper and
the proof-only import changes requested by the resumed preflight.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
