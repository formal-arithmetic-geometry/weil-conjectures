## What changed

Proved both arbitrary-complex proper direct-image theorems in
`Sheaf.Paper.ProperIndConstructibleUnbounded`, preserving their statements. The proof uses
canonical truncation triangles, the stated bounded-below theorem, eventual stabilization
of two cohomology towers, and transport of constructibility and amplitude along the actual
truncation projection maps.

Added two fully proved modules. `Sheaf.CategoryTheory.RoosEventuallyConstant` proves the
Milnor projection is invertible for eventually invertible cohomology transitions.
`Sheaf.AlgebraicGeometry.ModuleObjectPostnikovRoos` constructs the canonical lower
Postnikov tower and cone and proves its derived direct image is a homotopy-limit cone.
Its proof transfers exact countable products through the existing internal/sectionwise
module equivalence. It constructs a distinguished triangle for 1-T, factors the canonical
cone through its first object, and uses eventual Milnor projections to prove this factor
is an isomorphism. The derived adjunction then transports the entire cone.

All three modules compile with no errors or warnings through lcompile.py --all.
No existing definition, public signature or visibility was changed; the finite coefficient
universe is explicitly fixed to the universe already determined by its statement.

## Proved and sorry left

Closed both original holes (2 of 2):
`AlgebraicGeometry.ProEtale.proper_indConstructible_unbounded` and
`AlgebraicGeometry.ProEtale.proper_indConstructible_unbounded_padicAlgCl`
(node `det-proper-unbounded-window-arbitrary`).

Added zero holes. No sorry remains in any delivered module. In particular the retained
split-off `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward_postnikov_roos`
is proved in the retained sandbox (node `lem-module-object-postnikov-roos`), as is
`DerivedCategory.isIso_homology_map_cone_leg_of_eventually_isIso`
(node `lem-roos-eventually-constant-projection`). Private helpers `roos_epi`,
`roos_zero_leg`, `lower_postnikov_isHomotopyLimit`, `exact_products`,
`truncation_step_isIso`, `unbounded_of_postnikov`, and `coefficient_unbounded` are proved.

These proofs use the project's stated bounded-below and truncation-closure dependencies;
their own remaining axioms, if any, remain obligations of those existing declarations.
No object is selected from an unproved existence theorem.

## No longer needed

Removed the item's proof imports:
`Mathlib.CategoryTheory.Monoidal.Mod`, `Sheaf.CategoryTheory.SheafTensor`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
`Sheaf.Algebra.Homology.LowerTruncationStepTriangle`,
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
`WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit`,
`Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`,
`Sheaf.AlgebraicGeometry.ProEtaleLeftComplete`, and
`Mathlib.CategoryTheory.Limits.HasLimits`.

The new Postnikov module also needs no direct imports of
`Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`,
`Sheaf.AlgebraicGeometry.ProEtaleLeftComplete`,
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`, or
`Sheaf.CategoryTheory.SheafTensor`.

The nodes `lem-pc-derived-lower-truncation-step-triangle` and
`def-pur-sheaf-inverse-limit` are unnecessary for this argument: the canonical
T-structure triangle gives the transition, and the Milnor calculation constructs
its inverse directly. The strict-complex left-completeness comparison
`det-pe-left-complete-iso` and specialized derived-product result
`det-pe-products-derived` are also unnecessary here: exact products transfer across
the existing equivalence, and the general derived-product API and the proved Milnor
calculation establish left completeness directly. The obsolete top-level `tool_uses` entries `det-pe-products-derived`,
`det-pe-left-complete-iso` and `lem-pc-derived-lower-truncation-step-triangle` are removed.
Their underlying exact-product node `det-pe-products-exact` is still used. These pruning statements concern this
proof route; other library consumers may still need those modules.

The original structural module, sheaf tensor, module pushforward and Grothendieck
nodes are supplied transitively by the existing derived-functor interfaces rather
than reapplied in the item. The unit's Postnikov/Milnor route is retained.

## Where the brief, the DAG or earlier work was wrong

The retained report described only one closed hole and a still-holed Postnikov
comparison. Both original holes and that comparison are now proved. The finite
coefficient instantiation required an explicit existing coefficient universe; it
was not a false theorem or an intrinsically slow proof. An omitted
`open scoped CategoryTheory.Obj` caused the internal ring monoid instance to be
unavailable in the new module; restoring the scope resolved it.

The direct Postnikov proof avoids comparing localized strict-complex truncation
cones: construct a Roos triangle and prove its comparison to the canonical cone
is a cohomology isomorphism. This is the same unit-level left-completeness and
Milnor argument with fewer intermediate dependencies. Tail invariance ensures
that no surjectivity of early transitions is assumed; N=0 and zero objects cause
no exception.

Updated the original theorem docstrings to describe the implemented four-step proof,
and corrected obsolete step references in the node. The public theorem signatures
match current shared sources verbatim.

Earlier dry runs were rejected by the split-off timing rule or delayed in managed
worktree queues. No launcher tools or shared-repository files were modified.

## New nodes

`lem-module-object-postnikov-roos` records the canonical Postnikov cone and the
fully proved module-object direct-image comparison for arbitrary commutative condensed
coefficients and scheme morphisms, with the countable-product cohomology assertion. Its dependencies and proof
now record exact-product transfer and the direct Milnor argument.

`lem-roos-eventually-constant-projection` records the fully proved general
cohomological Milnor stabilization theorem, including its tail reduction and
explicit recursive section of 1-T. No change record is needed: existing public
interfaces are preserved and both modules are new.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
