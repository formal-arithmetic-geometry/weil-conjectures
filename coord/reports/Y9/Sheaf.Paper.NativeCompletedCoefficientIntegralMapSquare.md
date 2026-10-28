## What changed

Proved `coefficient_presentation_integralMap_pull_square` by reducing equality of
sheaf morphisms to their components and applying the new component theorem. Added
`NativeCompletedCoefficientIntegralMapSquareComponent` as the strictly smaller
pointwise finite-quotient substep.

## Proved and sorry left

Closed the original hole in
`coefficient_presentation_integralMap_pull_square`. The component theorem
`coefficient_presentation_integralMap_pull_square_component` remains as one named
`sorry`, recording the finite-quotient pointwise argument that supplies the component
identity.

## No longer needed

No imports or declared dependencies were pruned. The original route through a
simultaneously compatible family was not used because its already published wrapper
imports this module and would create an import cycle; the pointwise component is the
needed lower statement.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan stated the finite-quotient comparison directly at the sheaf
morphism level, but the available parent wrapper imports this module. A direct use of
that wrapper is cyclic, so the proof is split at the component level and assembled by
`Sheaf.hom_ext` and natural-transformation extensionality.

## New nodes

- `lem-sf-native-completed-coefficient-integral-map-square-component`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquare": "4445e2771a3333a315a50e37aa1fe63d857186ca", "Sheaf.Paper.NativeCompletedCoefficientIntegralMapSquareComponent": "24583fa76a84ecb2259a4c5ffefb5479358cf9e0"}, "results": {}, "time": "2026-10-28T10:35:36+0800", "transitive": 0, "version": 1}
```

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
