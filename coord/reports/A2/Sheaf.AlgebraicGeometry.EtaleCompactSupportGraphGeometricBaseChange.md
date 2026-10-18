## What changed

The assigned theorem keeps its existing signature and public imports. Its proof now
transposes the two specified graph comparisons under the pulled-back derived adjunction,
uses the counit law of the prescribed proper exchange, and applies an exact-derived
projection rectangle. The added import is proof-only.

Five supporting modules implement the argument:

- `EtaleCompactSupportGraphProjection`: actual homotopy and localized projections, and
  the complete transpose identity for the specified derived comparison. The constructed
  projections have generic component formulas, which avoid expanding structural identity
  transformations in the scheme-specific proofs.
- `ExactDerivedNaturalTransformation`: a constructed exact-derived natural transformation,
  its normalization and composition/whiskering laws, and preservation of projection rectangles.
- `EtaleCompactSupportGraphProjectionTermwise`: a constructed sheaf projection and complete
  proofs identifying its homotopy and derived images.
- `EtaleCompactSupportGraphSheafBaseChange`: the remaining ordinary-sheaf graph rectangle.
- `EtaleCompactSupportGraphProjectionBaseChange`: the complete descent of that rectangle and
  normalization of all exact-versus-left-derived inverse-image comparisons.

All new definitions are actual formulas or localization lifts. No data is chosen from an
unproved existence theorem. No existing definition, statement, visibility or target changes;
there are no consumer adaptations. The preflight-required record for local proof
annotations is `coord/changes/a2-graph-base-change-proof-annotations.md`.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.Etale.compactSupportGraphDerivedComparison_geometric_baseChange`
(node `lem-asd-compact-support-graph-geometric-base-change`). The assigned module has zero
remaining holes, versus one initially.

Added exactly one hole:
`AlgebraicGeometry.Etale.compactSupportGraphSheafProjection_baseChange`
(node `lem-a2-compact-support-graph-sheaf-base-change`). Its proof is exactly `:= by sorry`.
This is a decomposition, with one hole closed and one added, net zero; it is not claimed
as a complete proof of the original theorem. The new obligation has no complexes,
localization, total derived functors or proper derived direct image. It asks only for the
clopen-graph rectangle on ordinary sheaves. The remaining work is to compare the pulled-back
graph and complementary opens, prove equality of their identity/zero restrictions, and
identify the specified sum and open-extension comparisons by mate pasting. Its docstring
and node give the complete mathematical argument, including empty fibers and the zero ring.
A separate compiled scratch calculation verifies the useful clopen ingredient: the ordinary
direct-image base-change map is invertible for a cartesian square of clopen immersions.
It follows by cancelling the invertible open-extension exchange and clopen comparison in
`openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app`. This does not yet identify
the entire graph rectangle, so it is not added as an unused library lemma.

The other new public results are proved without additional holes:
`compactSupportDerivedComparison_leftDerived_transpose`,
`compactSupportGraphProjectionOnHomotopy_termwise`,
`compactSupportGraphDerivedProjection_termwise`,
`compactSupportGraphDerivedProjection_baseChange`, and all normalization, composition,
identity, isomorphism, whiskering and projection-square lemmas for
`CategoryTheory.Functor.mapDerivedCategoryNatTrans`.

Validation: the six delivered modules compiled together in import order. The sole
new hole is the named sheaf theorem above. The assigned signature is byte-for-byte
unchanged; the six node signatures match their Lean declarations, and their dependency
closure is acyclic. The original direct consumer `EtaleCompactSupportGraphDerivedIso`
compiled unchanged against the delivered modules (5.8 seconds). The second dry run
passes normal compilation of all six modules and the stage-3 preflight, with review
class CODEX. The proof-annotation change record resolves the first preflight failure. Its separate projection axiom probe exceeded 60 seconds. An import-based
`#print axioms` check of every new public declaration then completed in 4.5 seconds:
the projection, termwise identities and exact-derived transformation API depend only
on `propext`, `Classical.choice` and `Quot.sound`. The sheaf obligation and its derived
base-change assembly additionally depend on `sorryAx`, exactly as reported above.

## No longer needed

None. No original public import is removed and no original dependency becomes globally
unnecessary. The original plan's geometric sum exchange, conjugacy and mate-pasting inputs
remain in the sheaf obligation; localization and the specified unbounded exchange remain
in the proved assembly. They are used through the new nodes rather than asserted as a
single unformalized derived calculation. The blueprint unit route stays unchanged.

The broader `EtaleCompactSupportGraphCoherence` theorem cannot shorten this proof: it imports
this item through `EtaleCompactSupportGraphDerivedIso`. Neither is added as a dependency.
No stalkwise detection of derived morphisms, boundedness or finiteness argument is used.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The first dry run required a change record for local proof
annotations; that record is included even though the theorem interface is identical.
SGA 4 XVII 6.2.11 is the finite-type comparison background, not a
claim about unbounded complexes over arbitrary schemes. The arbitrary-scheme sheaf step
uses the explicit clopen graph argument of Stacks 0F4L and the general etale sum exchange
of 03S6; the unbounded descent is the formal localization argument written here.

The plan accurately describes the route, but its degreewise-descent
and transposition sentence needed explicit normalization work: the chosen total left-derived
inverse-image adjunction and the exact termwise functor are connected by specified isomorphisms,
not definitional equality. The delivery proves those identifications and keeps their directions.
The geometric component calculation remains the single ordinary-sheaf obligation above.

Mathlib searches found localization, derived-counit and mate APIs, but no normalized
exact-derived natural-transformation rectangle or compactification graph base-change theorem.
Repository and blueprint searches found no independent equivalent node. Existing
`openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app` handles the clopen-extension
comparison and is useful for the remaining geometric calculation, but does not itself
identify the pulled-back compactification graph and all of its pasted comparisons.

## New nodes

`lem-a2-exact-derived-natural-transformations` attaches the constructed natural-transformation
API and its proved rectangle theorem to `Sheaf.CategoryTheory.ExactDerivedNaturalTransformation`.

`lem-a2-compact-support-derived-projection` attaches the constructed homotopy/localized
projections and the proved derived-adjunction transpose identity.

`lem-a2-compact-support-termwise-projection` attaches the constructed ordinary-sheaf
projection and the two proved termwise identities.

`lem-a2-compact-support-graph-sheaf-base-change` is the sole remaining hole. It isolates the
clopen graph identity before complexes and derived adjunctions; the source is Stacks 0F4L
and 03S6, with the specified comparisons identified by mate pasting (0E46 and 0E47).

`lem-a2-compact-support-graph-projection-base-change` attaches the proved descent and
normalization of the sheaf rectangle to the exact-derived projections.

All five nodes inherit chapter `sec-smooth-purity`, unit `sk-prop-sf-cbc` and the original
blueprint ancestor, and record three kinds of Mathlib search. The original node's proof,
proof dependencies and proof origin now follow the Lean argument. The local proof annotation change record is
`coord/changes/a2-graph-base-change-proof-annotations.md`; it records an identical
public signature and no change to target meanings.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
