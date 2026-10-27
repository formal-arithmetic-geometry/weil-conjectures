## What changed

The target module now proves `comparison_invertibility_v` by unfolding `v` and
composing three isomorphisms: the inverse completion comparison on the source,
the finite-free evaluation transpose `homMap`, and the target internal-Hom functor
applied to the completion isomorphisms of `K` and `M`. A new private proof import
and module, `Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomMapInvertibility`,
is used for the isolated middle factor. The target node's proof and proof
 dependencies were updated to match this route.

## Proved and sorry left

The original `comparison_invertibility_v` sorry is closed. One strictly smaller
finite-free component remains as a named sorry:

- `WeilConjectures.IntegralFiniteExtension.homMap_isIso`, node
  `lem-sf-integral-finite-extension-hom-map-invertibility`.

The component states invertibility of the middle evaluation transpose before
completion conjugation; it has no completeness hypotheses and is the finite-basis
calculation described in paragraph 5 of the source proof.

## No longer needed

The target proof does not directly use the original right-adjoint/K-injective and
ringed-topoi proof dependencies; they are retained on the new `homMap_isIso` node,
where the finite-free calculation is isolated. No existing module was withdrawn and
no import was removed from the public interface.

## Where the brief, the DAG or earlier work was wrong

The canonical `scalarHomOrdinary_isIso` theorem in the library applies only to the
canonical ordinary tensor model, whereas this target allows arbitrary normalized
`IntegralHom.TensorPresentation` inputs. It therefore cannot be applied directly.
The finite-free evaluation transpose for those presentations is a separate strictly
smaller obligation; once supplied, the remaining completion conjugation is a direct
categorical composition.

## New nodes

`lem-sf-integral-finite-extension-hom-map-invertibility` records the finite-free
invertibility of `homMap`, the only remaining sorry introduced by this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomMapInvertibility": "c141e1c5074dd09ce52abbf5734ae8ee4d18ea91", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionVInvertibility": "2981a1f19baf936f1bcaa022f34618d978bafbc3"}, "results": {}, "time": "2026-10-28T06:53:22+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
