## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.proEtaleProjectionMateSlicePresentation`
with an explicit construction from the existing `ringedProjectionRestriction` package
and two strictly smaller statements. All existing declarations and public imports keep
their statements and visibility.

The source and target natural isomorphisms are composites of tensor restriction,
direct-image restriction and pullback restriction, followed by the native-to-global
model identifications. Their naturality comes from whiskering natural isomorphisms,
not a pointwise choice. The local mate is explicitly the adjunction unit followed by
the tensor comparison and counit, with its component equality proved by unfolding
the actual `derivedProjectionFormulaMate`. Its shift compatibility follows from the
second tensor-comparison shift square and functorial shift instances. Pullback is
triangulated by exact derived factorization. The compatible shift on its right
adjoint makes the right adjoint triangulated by Mathlib's triangulated-adjunction
result. Finally the global comparison equation, functoriality of restriction and
the supplied `ProjectionCompatible` equation give the required equation of actual
arrows. No restriction data is selected to define any public object.

Added proof imports of `RingedProjectionRestriction`,
`ProEtaleProjectionGlobalComparison`, `RingedProjectionTensorExact`, and Mathlib's
triangulated adjunction API (which also supplies the shift-adjunction API). Added two new modules, one theorem per
module, with source, complete proofs in words, and matching DAG nodes. Updated
only the assigned node's proof route, proof dependencies and proof origin.

Validation: `lcompile.py --all` compiled all three modules without warnings:
`ProEtaleProjectionGlobalComparison` in 2.9 s, `RingedProjectionTensorExact` in
1.5 s, and the assigned module in 23.0 s. Checked that the original structure,
theorem signature and public imports are unchanged, both new node signatures
match their Lean declarations, and the proof-dependency lists equal the unions
of the proof-step uses. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.proEtaleProjectionMateSlicePresentation`
(node `lem-weil-pbc-proetale-projection-mate-slice-presentation`).
There are zero sorry occurrences left in the assigned module.

Added two holes, both named public theorems with proof exactly `by sorry`:

- `AlgebraicGeometry.Scheme.proEtaleProjectionGlobalComparison`
  (`lem-weil-pbc-proetale-projection-global-comparison`): comparison of the two
  global models and their counit mates, without any slice or exactness assertion.
- `AlgebraicGeometry.Scheme.ProjectionRestriction.ringedProjectionTensorExact`
  (`lem-weil-pbc-ringed-projection-tensor-exact`): exactness of one fixed-factor
  tensor functor with its representative-normalized shift, without a morphism of
  ringed sites, a projection mate, or a slice.

Thus this is a decomposition: one original hole closed and two smaller holes
added, rather than an axiom-free proof of the full dependency closure. The existing
restriction theorem and its dependencies are used as stated, including their open
proofs. Neither new theorem is the assigned statement under another name: the
nontrivial natural-transformation, shift, restriction and equation assembly is
proved in the assigned module.

## No longer needed

No existing public or private import was removed, and no module is withdrawn.
Removed the redundant newly added proof import `Mathlib.CategoryTheory.Shift.Adjunction`:
`Mathlib.CategoryTheory.Triangulated.Adjunction` publicly supplies it.
No global module pruning is claimed. The source library is untouched.

The old direct proof dependency on `lem-weil-pbc-ringed-projection-mate-exact`
is avoided: its public interface uses a same-universe `RingedTensorCorner`, while
our ordinary slices keep objects in universe u+1 and morphisms in universe u.
Only fixed-factor exactness remains as a new native-size obligation; the mate's
shift compatibility and right-adjoint exactness are proved formally here.

The old direct dependencies on `lem-weil-pbc-localization-universal-property`,
`lem-weil-pbc-resolving-representative-whiskering`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and
`def-weil-pbc-proetale-operations` are not needed for the final assembly. The
normalization statements still cite the resolving and operation theory where
needed; these are relocated proof obligations, not claims that their modules
are globally unused. `def-weil-proetale-inverse-image` and
`def-weil-pbc-ringed-derived-restriction` remain statement dependencies.
The blueprint unit's statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The restriction package already supplies the actual equation between canonical
global and local mates, so this equation need not be split off again. Its tensor
models differ from the native models accepted by the assigned theorem; equality
of their normalization data is a separate global comparison argument.

`ProjectionRestriction.Local` records additive instances as fields; consumers of
its tensor comparisons must install those fields locally. The ordinary restriction
is still the exact `overFunctor.mapDerivedCategory`, so proof irrelevance identifies
it with `ringedDerivedRestrictionGeneral`. No definition or statement repair is
made. The source package preserves the independent native site universes.

Read the current blueprint's perfect-projection-formula proof and Stacks Tags
07A4, 07A6, 0B56 and 04IF. The model-comparison assertion was checked with identity
models, identity scheme morphisms and zero E; it imposes no invertibility of the
projection mate. The tensor assertion was checked at zero E, the coefficient ring,
and arbitrary shifted resolving complexes; its conclusion uses precisely the
normalized shift, so it does not assume exactness for an arbitrary shift choice.

Searches through msearch (LeanFinder, Loogle and grep), and direct rg in Mathlib,
WeilConjectures and Sheaf found the private `matePublishedExact` and the public
`kFlat_fixed_tensor_triangulated` and `derived_tensor_shift_descent`. The former
is tied to `RingedTensorCorner`; the latter two supply the intended argument for
the remaining fixed-factor normalization step. No existing declaration was copied
or replaced by a duplicate public definition.

## New nodes

`lem-weil-pbc-proetale-projection-global-comparison` is the global-only comparison
of supplied native tensor and operation models with a normalized global package,
including the actual counit-mate square. Its source is Stacks 06YU, 07A4, 07A6 and
0B56. Resolving full faithfulness, adjoint uniqueness and counit normalization are
the recorded proof route. It has no slice or exactness conclusions.

`lem-weil-pbc-ringed-projection-tensor-exact` extracts the fixed-factor tensor
exactness needed on the native ordinary slice from the fixed K-flat tensor and
normalized shift descent theorems (Stacks 06YU, 07A4, 0FNH). It contains no
projection, pullback, direct image or restriction data. Its representative shift
normalization retains the connecting-map content of triangulatedness.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
