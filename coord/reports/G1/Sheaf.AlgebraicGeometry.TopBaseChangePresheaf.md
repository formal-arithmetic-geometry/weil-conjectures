## What changed

Replaced the body of `AlgebraicGeometry.top_base_change_presheaf` by an assembly of
`derivedAdjunction_topEdge`, the proved derived-square transpose, and a separate
ordinary coefficient-map/local-class comparison. The statement and four existing
construction bodies are preserved. Local irreducibility prevents broad rewriting
from expanding the resolution and tensor constructions. Proved private equations
for `topBaseChangeClass_source`, `topBaseChangeClass_eq`,
`restrictedDirectImageMap_unit`, and `topBaseChangeAdjoint_eq` keep the final
assembly in the named constructions. No existing construction body is changed.
Proved generic `conjugate_comp` and `transport_class_equation` lemmas handle
associativity and the final factor transports without rewriting inside module
constructions. Constructor equations respect transparency; only the necessary final
definitional transports permit unfolding. The adjoint definition alone retains its
original unfolding settings. Module aliases are transparent for instance search, and
proof bindings are retained with `cleanup.letToHave false`.

The canonical total/classical comparison is now the constructed public definition
`schemeSingleCohomologyComparison` in the new local-class module. Its type fixes the
derived universe and its body uses the original ringed-space comparison. This avoids
an incorrect default small-universe instance when applying the comparison directly
to a scheme-module pushforward. Both the local-class statement and the item proof
use this same comparison. The item selects the edge from the existing uniquely
specified top-edge theorem, then uses its defining properties directly.

The sandbox-wide compilation passed after these changes. A subsequent diagnostic
compilation, retaining proof bindings, compiled the item in 35.8 seconds and the
local-class module in 10.1 seconds; the transpose module reused its artifact. The
profiler setting and all temporary heartbeat limits are removed from the packet.
Earlier delivery attempts pushed nothing after compile timeouts; the delivery runs
the normal compile checks again.

The separate importer check compiled with all three sandbox modules and verified
all five existing public declarations. Its axiom output contains the standard
axioms and admitted theorem dependencies, consistent with the remaining named
hole and the imported existing holes. The importer compiled in 3.1 seconds and
is a temporary probe, removed from the delivery. The local-command change record
also documents the zero-downstream-consumer audit.

Added `Sheaf.AlgebraicGeometry.DerivedSquareUnitMap`: its square comparison is the
right-adjoint mate of the pinned pullback square, its coefficient map applies Rf to
the ordinary h-map and the canonical single direct-image comparison, and its theorem
identifies the transpose of the specified module base-change map with this map. The
private four-adjunction calculation uses the conjugate-equivalence counit identity,
naturality, and the hom-equivalence inverse law. The tensor single comparison uses
the existing canonical single transpose and cancels the unique left-adjoint comparison.

Added `Sheaf.AlgebraicGeometry.DerivedSquareLocalClasses`, which restricts any h-map
by the actual restriction adjunction, constructs the universe-pinned canonical
comparison, and states its local-cocycle equation. This is
stated without a derived-pullback input, tensor-pullback unit, or cohomological upper
bound. Its proof plan uses the existing normalized direct-image square mate and
pasted-unit declarations, then the same injective-resolution roof as moduleCohomologyFMap.

## Proved and sorry left

The original hole in `AlgebraicGeometry.top_base_change_presheaf`
(`lem-weil-pbc-top-base-change-presheaf`) is closed by a complete assembly from named
statements. `AlgebraicGeometry.derivedModuleBaseChange_transpose`
(`lem-weil-pbc-derived-square-unit-map`) is proved, with no new hole in that module.

One new hole remains: `AlgebraicGeometry.derivedSquareUnit_localClasses`
(`lem-weil-pbc-derived-square-local-classes`). Its proof body is exactly `by sorry`.
The hole contains the independent ordinary h-map/local-cocycle roof comparison,
not the derived transpose or top-cohomology adjunction argument. In particular it
has no top-degree bound, derived-pullback comparison, or base-change delta.

This is a decomposition: one original hole closed and one lower hole added, so the
net hole decrease is zero. The item module itself has zero remaining holes.
No definition or private helper contains a hole. Imported existing holes, including
`derivedAdjunction_topEdge`, are not changed by this packet.

## No longer needed

Removed these private proof imports from the item module:

- `WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`;
- `WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology`;
- `Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf`;
- `WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`;
- `WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives`;
- `WeilConjectures.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`;
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`;
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.

The general ringed-topos composition node
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is no longer needed by this
argument. The local roof instead uses the already stated scheme-specific normalized
square lemmas `lem-sc-derived-direct-image-square-mate` and
`lem-pc-normalized-direct-image-square-unit`.

The arbitrary nonempty composition comparison
`lem-pc-derived-direct-image-composition` and its module
`WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded` are not used.
The construction here fixes the right comparison directly as the pinned mate.
Its obsolete top-level `tool_uses` entry is removed from the item node.

The local section, sheafification, restriction, injective-resolution and h-map nodes
remain needed either by the top-edge theorem or by the new local-cocycle theorem.
Removing their direct imports from the item does not claim these modules are globally
unreachable. The module-pullback composition node remains indirectly needed by the
pinned pullback square; the explicit restricted coefficient uses restriction units.
The direct bounded-below-to-K-injective step
`lem-weil-pbc-bounded-below-injectives-kinjective` is replaced by the existing
`Functor.isGE_rightDerivedFunctor_obj_singleFunctor` theorem; it is not needed as
a separate step of this proof. The resolution-existence node remains in the local
roof plan. The predicate `def-pc-derived-module-base-change-map` is not invoked:
the proof computes the actual delta construction. The derived-adjunction,
derived-base-change, derived-direct-image, and presheaf-sheafification nodes remain
in the definitions or transpose/top-edge dependencies, rather than as separate
steps in the item. No existing source-library declaration is removed, changed,
or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The plan's statement that the normalized composition represents the desired roof
requires a normalization theorem, not merely the `Nonempty` comparison returned by
`derivedDirectImageComposition`. Existing proved normalized-square and unit-pasting
lemmas supply the appropriate interface. The remaining local comparison also requires
transport between the specified total-derived local classes and the specified
classical restricted-resolution classes; a generic naturality slogan alone does not
supply that equality in Lean.

The flat base-change resolution-section theorem cannot be applied here: it requires
flatness of the base and upper arrows, while this item allows arbitrary scheme maps.
No flatness assumption has been added. Checks of degree zero, identity squares, zero
coefficients and empty opens agree with the new general h-map statement. The roof
inverts only the section-cohomology isomorphism of an injective replacement, and the
main theorem inverts only its specified kappa; no class map or delta is inverted.

## New nodes

`lem-weil-pbc-derived-square-unit-map` records the proved derived square transpose and
its two explicit constructions, with the four-adjunction and single-module calculations.
It retains the pinned adjunction and pullback-composition normalization.

`lem-weil-pbc-derived-square-local-classes` records the independent ordinary h-map roof
comparison on inverse-image opens, together with the explicit restricted h-map and
canonical total/classical comparison constructions. Its statement introduces arbitrary coefficients
and a locally specified edge. Its docstring and node give the full resolution proof
and cite existing statements for the normalized square, restriction, section
quasi-isomorphism, independence of choices, and sheafification comparisons.

The two existing scheme normalized-square statements are generic tools for the
roof calculation, not a replacement of a proper-base-change unit step.

Every existing public statement, construction body and public import is unchanged.
The static checker nevertheless classifies the new local attributes and elaboration
commands as an interface change. They are documented in
`coord/changes/G1-top-base-change-presheaf-proof-environment.md`, including the
verbatim old/new signature and command blocks and the consumer audit. There are
zero current downstream Lean modules; the DAG parents remain attached. No consumer
adaptation is needed. The inherited proper-base-change unit route is retained.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
