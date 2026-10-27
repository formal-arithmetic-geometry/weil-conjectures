## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.PurityTransport.integralComparison`
by the construction from a normalized finite root diagram and preservation of the
chosen Tate limit cone. Postcomposition transports the limit structure, and
`IsLimit.conePointUniqueUpToIso` constructs the integral comparison with its
projection equations. The proved private helper `pullNormalized_unique` uses
faithful module forgetting and cancellation of the scalar comparison. It identifies
the finite witnesses of any competing comparison; `limit.hom_ext` proves uniqueness.

Added private proof imports of `TransportRootTower` and `TransportTateLimit`.
The latter proves its limit step from finite-level representability, using proved
generic private helpers of `NativeIntegralTateTowerLimit` via a private `import all`.
It lifts the represented diagram, applies geometric base change of its affine
limit, reflects from set sheaves to abelian sheaves, and reflects through module
forgetting. The final scalar comparison is the actual `extendScalarsIsoComapInv`.
The native public theorem for its different O_E diagram is not used.

Preserved all existing signatures, definitions, public imports and file options.
Updated the item's proof route and added three nodes for the new modules.

Validation: the final `lcompile.py --all` run compiled all four modules, with
times 28.6 s, 4.0 s, 45.4 s and 46.4 s respectively. All are within 60 s.
Checked node attachments, proof-step dependency unions, blueprint tags and
100-character Lean line widths. No source-library declaration is changed.

## Proved and sorry left

One original hole closed: `AlgebraicGeometry.ProEtale.PurityTransport.integralComparison`.
Its proof body is complete. The private `pullNormalized_unique` is proved.
`scalarPull` is unchanged and has no hole. The new
`AlgebraicGeometry.ProEtale.PurityTransport.tateLimitCone` is also proved from
finite-level representability and existing categorical/geometric helpers.

Two holes added, one per new module:

- `AlgebraicGeometry.ProEtale.PurityTransport.normalizedRootTower`, node
  `lem-pur-transport-normalized-root-tower`: finite root pullback compatible with
  the power transitions, with no assertion about inverse-limit objects.
- `AlgebraicGeometry.ProEtale.PurityTransport.tateLevelRepresentation`, node
  `lem-pur-transport-tate-level-representation`: finite etale representation at
  one level, with no transition, base morphism or inverse-limit comparison.

This is a decomposition: one original hole closed, two smaller holes added;
net proof progress is -1 (one hole becomes two). There are zero holes in the item
module and two across the delivery. No definition contains a hole. The imported
`rootComparison_existsUnique` is pre-existing and unchanged.

## No longer needed

None of the original imports or declared dependencies is pruned. The item originally
imported only `TransportRoot`, which its statements and `scalarPull` still need;
its original node had no proof dependencies. No module is withdrawn or unit bypassed.
The limit-cone statement needs only upstream `TateTwist.ProEtale` publicly;
its two additional imports are private proof imports.

The local-basis results in `PoincareDuality.CompatibleIntegralRootBases`,
`IntegralTateBasis` and `IntegralTateLocalLine` do not directly give the normalized
global comparison and are not imported. The different O_E tower theorem
`spIntegralTwist_inverseImage_isLimit` is not used; only its generic proved private
helpers are reused.

## Where the brief, the DAG or earlier work was wrong

The item's definition node had an empty proof and empty proof dependencies despite
its theorem hole. Its docstring describes substantive geometric steps without
supplying their Lean declarations. The delivery states the smaller missing facts
and writes the categorical arguments combining them.

Read the current blueprint
`sec-smooth-purity/sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.proof.md`,
paragraphs "Roots of unity" and "The integral twist", together with
`sec-proetale-coefficients/sk-def-sp-tate-twist/def-coefficient-twists-detailed.md`
and the current `sk-thm-purity-transport` statement. The integral argument uses
representability and geometric base change, without assuming that inverse image
preserves unrelated infinite limits.

Edge cases checked: level zero is the zero root module and its underlying set sheaf
is represented by the base itself; the empty scheme has only the unique maps.
Arbitrary base morphisms and exactly the item's residue-field invertibility
assumptions are retained. Identity morphisms give the canonical identity transports.
No finiteness or geometric assumption on the base is added.

## New nodes

`lem-pur-transport-normalized-root-tower` attaches
`AlgebraicGeometry.ProEtale.PurityTransport.normalizedRootTower` in
`Sheaf.SecSmoothPurity.TransportRootTower`. Its proof in words uses finite etale
root representability, strong monoidal inverse image and exponentiation.

`lem-pur-transport-tate-level-representation` attaches
`AlgebraicGeometry.ProEtale.PurityTransport.tateLevelRepresentation` in
`Sheaf.SecSmoothPurity.TransportTateLevelRepresentation`. Its proof in words
identifies the free integral root level with the root sheaf and uses the relative
root scheme. This is a one-level existence assertion only.

`lem-pur-transport-tate-limit-cone` attaches
`AlgebraicGeometry.ProEtale.PurityTransport.tateLimitCone` in
`Sheaf.SecSmoothPurity.TransportTateLimit`. Its Lean proof uses represented-diagram
limit preservation and reflection through the forgetful functors. All three nodes
inherit the item's chapter and unit and record the required searches. No existing
interface changes, so no change record is needed.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
