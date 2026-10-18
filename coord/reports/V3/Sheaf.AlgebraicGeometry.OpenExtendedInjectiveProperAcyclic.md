## What changed

Proved `AlgebraicGeometry.Etale.isZero_higherDirectImage_openImmersionLowerShriek_injective`
with its signature and all public imports unchanged. No definitions or consumer modules changed.
The proof forms `V = B ×_D C`, proves that the induced open immersion `t : A → V` has closed
range using properness, and uses the already proved clopen comparison `t_! ≅ t_*` to preserve
injectivity. Two private, fully proved helpers handle positive-degree injective vanishing and
the homology/single-functor identifications for module-valued proper base change.

Over C, restriction of `k_!J` identifies with `t_!J` by open-extension composition and the
fully faithful adjunction unit. Over its complement, the pulled-back support is disjoint,
so the existing open/closed vanishing theorem gives the zero sheaf. Proper base change
and the geometric-point conservativity criterion combine these two cases.

Updated the item's DAG proof, proof dependencies and proof origin to this route. Recorded the
existing source-library clopen comparison as a new node, without introducing a Lean module
or another declaration. The original theorem docstring records a valid longer proof plan;
the inline comments and revised DAG describe the actual shorter implementation.

Validation: the complete and finally pruned Lean module compiled through `lcompile.py`
without warnings or errors (31.5 seconds for the final compile). The delivery gate also
probes all declarations and their axioms. An overlay dependency traversal found no cycle
through either the revised item or its new comparison node; four existing reachable
cycles in spectral-sequence/derived-exchange records are unrelated to the new edges.
The non-Cartesian hypothesis is preserved: t need not be an isomorphism. Empty source,
empty C, zero J, and the zero coefficient ring are handled by the same argument. No
underlying-abelian injectivity hypothesis is used. No arbitrary witness data is chosen.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isZero_higherDirectImage_openImmersionLowerShriek_injective`
(node `lem-cbc-open-extended-injective-proper-acyclic`).

Holes added: 0. Split-offs: 0. Sorries left in delivered Lean modules: none.
Both private helpers are completely proved. This is a proof from existing library results,
including proper base change; its pre-existing dependencies may still rest on project holes.
It is not a claim that the entire transitive closure is now sorry-free.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.AlgebraicGeometry.TorsionAssembly`
- `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`
- `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`

No public import was removed. The finite-comparison module remains imported for the proved
geometric lemma `disjoint_range_of_closedPoint_not_mem`, not its finite-pushforward comparison
or extension-by-zero stalk formula.

Removed proof dependencies and their obsolete top-level tool approvals:

- `lem-weil-pbc-module-abelian-derived-direct-image-comparison` and
  `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`: direct module-valued
  proper base change avoids forgetting coefficients.
- `lem-weil-pbc-proper-immersion-closed`: only the closed range of the proper t is needed;
  no closed-immersion structure is constructed.
- `lem-weil-pbc-etale-sheaf-clopen-product` and
  `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`: the proved clopen comparison directly
  identifies extension by zero with the injective-preserving right adjoint.
- `lem-weil-pbc-extension-by-zero-stalks`: no stalk formula for extension by zero is invoked.
- `lemma-weil-pbc-torsion-assembly` and `Sheaf.AlgebraicGeometry.TorsionAssembly`: the current
  source library already gives module-valued proper base change for torsion coefficient rings.
- `sbc-prop-extension-by-zero-and-arbitrary-base-change` and
  `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`: inside C composition and
  the adjunction unit identify the restriction; outside C disjoint-range vanishing suffices.
- `lem-kun-stalks-of-cohomology` and `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`:
  exact inverse image commutes with homology, and module geometric points detect zero.

These removals concern this item's proof edges; they do not assert that other parents no
longer need these modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken dependency was found. The DAG's abelian-sheaf and clopen-product
route is valid but longer than the current library APIs require. Its named dependency
signatures were read before selecting this shorter route. The unit record
`sk-prop-sf-cbc` has no bound realized steps, and the source's proper/open injective-acyclicity
argument is retained; no unit statement or step changes.

The reader should record the generic tool use `thm-weil-pbc-bounded-below`: its existing
module-coefficient declaration `isIso_baseChange_of_isProper_of_isAddTorsion_ring` is used
only on the two actual Cartesian pullback squares. This is exactly the proper-base-change
input the original approved torsion-assembly route used, with the abelian conversion
removed, and does not replace compact-support base change by its own conclusion.
The other newly named dependencies are the existing closed disjoint-range vanishing,
the existing open-extension composition isomorphism (no coherence theorem is needed),
and exact-functor homology compatibility. No new tool approvals were written by the worker.

## New nodes

`lem-cbc-clopen-extension-zero-comparison` records the already proved generic declaration
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range` in
`WeilConjectures.SixFunctors.Etale.LowerShriek.Proper`. It introduces no Lean declaration
and no hole. Blueprint searches for clopen and extension by zero, and local DAG searches,
found no node for this exact comparison; the clopen-section derived direct image has
additional section data and a different conclusion. Three remote Mathlib searches were
run and recorded; the match is in the source library, not Mathlib. Its proof uses a cover
by the immersion and its open complement, the adjunction identities on the first piece,
and disjoint-support vanishing on the second. Empty components and zero coefficients
are allowed. No change record is needed because no existing signature or definition changes.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
