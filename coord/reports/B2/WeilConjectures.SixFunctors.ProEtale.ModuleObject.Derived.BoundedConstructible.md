## What changed

The item now derives ordinary direct-image preservation from boundedness and constructible
homology, and builds its monoidal instance from the proved coefficient-unit calculation and
tensor closure. The internal-Hom instance is reduced by finite truncations in both variables.
This closes all three original proof bodies by decomposition.

The boundedness proof is a finite truncation induction, reduced to an upper bound for the
direct image of a constructible sheaf in degree zero. Its lower bound is proved directly
from bounded-below/unbounded right-derived compatibility. The tensor proof uses two finite
truncation inductions, reduced to tensoring constructible sheaves in degree zero. The
truncation argument specializes the already proved `DerivedCategory.prop_of_bounded` theorem
to constructible module objects; no duplicate induction remains.

For internal Hom the second-variable functor is triangulated by adjunction from derived
tensor, with its induced shift compatibility. The first-variable argument is an explicit
finite amplitude induction using `exists_distinguished_ihom_pre`. Its base case allows
single sheaves in each degree, avoiding a separate contravariant shift structure. The zero
case follows by currying from tensor with zero, and the truncation top term is identified
with the appropriate single cohomology sheaf. This is a genuine combination of smaller
inputs, rather than a renamed original assertion.

The coefficient-specific triangulated closure is proved for every constructor of
`IsEllAdicFinitenessCoefficient`: continuous finite extensions, integral subextensions,
the bounded-image algebraic closure, and supplied closed unit balls. It uses the existing
proved Serre and local-triviality APIs. The coefficient-unit calculation is also proved.
The helper proofs themselves use no `sorry`. `#print axioms` for the
truncation specialization, coefficient-specific triangulation, and coefficient-unit theorem
reports only `propext`, `Classical.choice`, and `Quot.sound`.

`CondensedFieldContinuousRealization` replaces its public `MorphismDefs` import with
`UpperLowerStar.Defs`, `ConstructibleSheaf.ProEtaleModule.Def`,
`ProEtaleModuleConstructiblePullback`, and
`ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`, eliminating the import cycle through this item. Its declarations and proofs are
identical. The returned delivery was refused because four modules used the removed
transitive export `constructible_of_iso`. The realization module now publicly imports
the defining pullback module as well, preserving that exported API while removing the
cycle-causing base-change dependency. Each named consumer also directly imports
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback` privately:
`BoundedConstructibleHomPreservation`, `EllAdicBoundedTriangulated`,
`Sheaf.Paper.ConstructibleCokernelsExtensions`, and `Sheaf.Paper.IntegralConstructibleKernels`.
The latter two were copied from the current shared source and changed only by this import;
they are unclaimed. No consumer declaration or proof changes. The change record lists
all transitive consumers and the four direct-import repairs. Every import in the item added
for these proofs is private. All existing declaration signatures remain unchanged.

The return at head `182ee533b` identified two further import consumers. This repair adds
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` directly and privately to
`Sheaf.Paper.ContinuousModuleEncodingScalarExtension`, and
`WeilConjectures.AlgebraicGeometry.Sites.Kummer` directly and publicly to
`Sheaf.PoincareDuality.CompatiblePrimitiveRoots`. The latter supplies the actual root sheaf
used by the public `tateRootsSystem` definition. Both modules are unclaimed. The scalar-extension module already had a private helper
named `tensorHomEquiv`; importing the required defining module exposes the public
`SheafOfModules.tensorHomEquiv`, so Lean rejects that private name collision. The helper
is renamed to `scalarExtensionTensorHomEquiv` and its one call is updated. Its type and
body are unchanged. All public signatures and proof bodies remain unchanged apart from
that helper reference. The roots module also directly imports `WeilConjectures.Mathlib.AlgebraicGeometry.Limits`
and `WeilConjectures.Mathlib.AlgebraicGeometry.Restrict` privately. Compilation against the
reduced import closure showed that its existing proofs need
`Scheme.isEmpty_of_subsingleton_Γ` and `Scheme.isUnit_ι_appTop_basicOpen` from those modules.
Its declarations and proof bodies are unchanged; only these three imports are added.

## Proved and sorry left

Original item: three holes. All three original holes are closed by decomposition:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`;
- `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`;
- `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`.

Four holes are added, one named public theorem per module:

- `AlgebraicGeometry.ProEtale.CondensedRing.constructible_single_rightDerivedLowerStar_upper_bounded`
  (`lem-sfb-dc-lower-star-single-upper-bounded`). It still needs the single-sheaf
  finiteness calculation: integral completion/reduction and uniform finite-level bounds,
  rationalization continuity, finite-subextension descent, and the finite torsion comparison.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_constructible`
  (`lem-sfb-dc-lower-star-constructibility`). It still needs the constructible-homology
  part of that argument for the actual ambient module-object direct image, including the
  coefficient-model identifications. The complete coefficient-by-coefficient argument is
  in its docstring and node.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_single` (`lem-sfb-dc-tensor-single`). It still needs the
  local tensor calculation on a common stratification and presentation cover: finite-free
  field models, two-term DVR cyclic resolutions, exact pullback comparisons, and detection
  of the resulting global cohomological bounds and local presentations.

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_hom_single` (`lem-sfb-dc-hom-single`). It still needs the
  single-sheaf internal-Hom finiteness argument: the integral cohomological criterion and
  local derived completeness, followed by rationalization and finite-field descent with
  evaluation-normalized scalar comparisons. Its first input is a single sheaf in any
  degree and its second input is a sheaf in degree zero, strictly smaller than the original
  closure assertion for two arbitrary bounded constructible complexes.

The two additional consumer adaptations introduce no holes; only the scalar-extension
private helper name and its reference change alongside the imports.
Thus four holes remain in delivered Lean files, all new. Net original holes closed minus
added is -1. These are decompositions, not three axiom-free proofs of the original
preservation assertions.

Completed helper proof bodies include `boundedConstructible_tensor_unit`,
`boundedConstructible_tensor_closure` (from the single-sheaf input),
`boundedConstructible_hom_closure` (from the single-sheaf input),
`boundedConstructible_rightDerivedLowerStar_bounded` (from the single-sheaf upper bound),
`isTriangulated_boundedConstructible_ellAdic`, `prop_of_boundedConstructibleModule`, and
`isClosedUnderIsomorphisms_boundedConstructibleModule`.

## No longer needed

No imports or nodes are pruned in this repair. The previously removed imports are restored
because `MorphismDefs` publicly imports this item and downstream modules use declarations
provided through the item's original import surface. The helper imports used by the item are
also retained. This is required by the import-pruning gate and preserves the existing public
API for all listed consumers.

## Where the brief, the DAG or earlier work was wrong

The landing refusal was caused by pruning imports from the item that are part of the
public dependency surface of `MorphismDefs` and its consumers. Restoring the exact
original imports fixes the refusal without changing any declaration or proof.

Repair of the return at head `182ee533b`: add the two defining modules directly to the
consumers named by the landing import-pruning gate, as requested. The earlier gate-pass
report below describes the previous delivery base; the newly fetched base requires these
two further imports. Validation for this retry: all fifteen delivery modules compile together in import
order with no errors or warnings, within the single-file limit. The roots module
compiles in 21.7 seconds; the scalar-extension module compiles after its private-helper
rename. The required dry run passed at `fa4d78c53a` with review class CODEX.
A separate local replay of the source import-pruning gate is still running at
submission; it has not reported findings. The required compile and dry run have passed.
The independent landing check remains authoritative for the complete source graph.


Repair of the return for delivery head `75269cf1e`: the previous consumer compilation
did not satisfy the source import-pruning check. That check identified four uses of
`constructible_of_iso` whose path through `MorphismDefs` would disappear. The repair
adds the defining module as a direct private import to all four listed consumers, as
requested, rather than restoring the import cycle. Two are new helper modules already
in this delivery; the two existing Paper modules retain their current source, signatures,
visibility, and proof bodies exactly. No additional holes are introduced by this repair.

Historical tool-failure notes in the inherited report have been removed: the current
launcher no longer contains the tracked-tool rewrite described there. All thirteen
modules compile without warnings and within the single-file limit. The previous repaired
dry run passed preflight with review class CODEX (commit `2a4bc85158`). Its earlier
source import-pruning check passed, but did not cover the new consumers reported by
the landing at head `182ee533b`. The two existing Paper modules
have been checked textually against current shared source: their sole change is the
one direct private import. The four retained obligations are unchanged by this repair.

Several planned coefficient comparison/heart nodes have no `lean` attachment in the current
checkout, while other inputs are stated for `SheafOfModules` rather than the item's
`Mod (Sheaf ...)` category. For example, `lem-sfb-integral-lfp-constant-model-comparison`,
`det-lem-int-integral-heart-triangulated`, `det-cor-coefficient-heart-ii-triangulated`,
`def-sfb-rationalization-equivalence` and `sk-thm-sfb-qlbar-two-colimit` have no `lean` record.
This does not make their mathematics false. The proved Serre APIs suffice for the
triangulation step. The remaining finiteness interfaces explicitly retain the actual
module-object categories so that a future proof must supply the required identifications.

No definition, theorem signature, target statement, or coefficient predicate was weakened.
The import repair changes no mathematical data. An initial replacement by `Basic` missed
exports needed by consumers (`upperStar`, `upperStarComp`, and `Mod.finiteFree`), and a later consumer required
`localizationRestrictionLowerStarAdjunction` and `upperStarIsoLocalizationRestriction`;
the combined import-order build exposed these errors. The retained API imports supply these exports; the four direct imports now
supply the additional constructibility API identified by the return. The earlier
single-file consumer compiles did not validate the changed dependency overlay. Edge cases checked in the remaining
statements are zero coefficients, zero modules/complexes, empty schemes, zero free ranks,
and integral torsion; the ell-adic tensor hypothesis is retained, so finite nonregular
torsion coefficient rings are not accidentally admitted to tensor closure.

## New nodes

`lem-sfb-dc-lower-star-single-upper-bounded` states the remaining direct-image upper bound
for constructible sheaves in degree zero; it is strictly a special case and only a bound,
not the original complex-level preservation assertion.

`lem-sfb-dc-lower-star-bounded` is the proved finite truncation assembly of these bounds,
using left t-exactness and the triangulated inverse image of the bounded subcategory.

`lem-sfb-dc-lower-star-constructibility` states only the constructible-homology component
of direct-image preservation; its source proof is retained in full.

`lem-sfb-dc-tensor-single` is the original plan's degree-zero sheaf calculation; it supplies
the base case of both fully proved tensor truncation inductions.

`lem-sfb-dc-tensor-unit` is proved by the single-complex/unit comparison and explicit finite
presentations for the regular and zero modules.

The existing `lem-sfb-dc-tensor-preserves` node is attached directly to the proved
two-truncation-induction assembly; no duplicate tensor-closure node is introduced.

`lem-sfb-dc-module-devissage` is the fully proved finite truncation induction, together with
isomorphism invariance. Its proof specializes the existing generic library theorem
`DerivedCategory.prop_of_bounded`; a duplicate interval induction was removed.

`lem-sfb-dc-ell-adic-triangulated` is the fully proved constructor-by-constructor Serre
argument for the actual coefficient predicate.

`lem-sfb-dc-hom-single` is the remaining single-sheaf internal-Hom finiteness input. The
existing `lem-sfb-dc-hom-preserves` node is attached directly to the proved two-truncation
assembly. The first-variable induction uses the existing distinguished internal-Hom
triangle and asks for single sheaves in every degree, so no first-variable shift API or
triangulated contravariant functor is postulated. The second variable uses the generic
truncation theorem and the triangulated right adjoint of tensor.

The existing lower-star, tensor-preservation, and internal-Hom node copies now point to
the declarations and proof dependencies used by the delivery. The change record is
`coord/changes/b2-bounded-constructible.md`.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
