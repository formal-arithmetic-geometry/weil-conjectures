## What changed

Proved `WeilConjectures.integralScalarTensorChainTower` in its existing module,
with its statement unchanged. Three new, fully proved modules supply the finite-level tensor calculation,
strict tower composition and horizontal coherence of the canonical additive
Roos comparison. The assigned module uses private proof imports; its existing
public imports remain.

The finite calculation uses the existing ordinary scalar associator and the
normalized level comparisons. The Roos calculation uses both cocone coordinates,
so it does not require scalar extension to preserve countable products. The node
now records this argument. No shared definitions or consumer modules change.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.integralScalarTensorChainTower`
(node `lem-pur-integral-scalar-tensor-chain-tower`).
No holes added and no `sorry` remains in the delivered module. All new local helpers
are private and proved. The three new lemmas are also fully proved. No decomposition into remaining
holes is introduced.

## No longer needed

No imported module or DAG node is pruned. Both original public imports remain.
The original plan's finite-freeness/product-preservation argument is unnecessary:
the canonical product comparisons already satisfy horizontal coherence for
arbitrary additive functors and natural transformations.

The private total-map formula in `NormalizedScalarTensorTransitions` is reused
only to evaluate an ordinary total tensor map; this does not bypass a unit's route.
The private extensionality and map-on-section helpers in the existing reduction
and transition modules are likewise used as proved tools, with their module nodes
listed in the proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The earlier node supplied a correct plan but
its claim that finite freeness was needed to commute with products was stronger
than necessary. Horizontal coherence follows from the universal property of the
canonical product comparison, without asserting it is invertible.

The proof keeps arbitrary unbounded inputs and all schemes. Unit coefficients
are used only after applying the scalar adjunction and generator extensionality;
no flatness, constructibility or boundedness hypothesis is added. Zero inputs,
identity extensions and level zero obey the same formulas.

## New nodes

- `lem-pur-integral-scalar-tensor-level-tower`: proved finite-level coefficient
  composition, in `Sheaf.Paper.IntegralScalarTensorLevelTower`.
- `lem-pur-integral-scalar-tensor-tower-composition`: proved strict tower
  composition, in `Sheaf.Paper.IntegralScalarTensorTowerComposition`.
- `lem-pur-additive-roos-horizontal`: proved generic composition theorem for
  additive Roos comparisons, in `Sheaf.Paper.AdditiveRoosHorizontal`.

These are separate proof steps, not copies of the assigned chain theorem. Their
modules separate the completed arguments to control kernel conversion time.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdditiveRoosHorizontal": "2d65c8d51a451a81c342f0af359ac183b2bddab9", "Sheaf.Paper.IntegralScalarTensorChainTower": "46656eba859525c6cea1232e4f61388ab7b27727", "Sheaf.Paper.IntegralScalarTensorLevelTower": "d7a14a6938c921db913a0fc045bc8c5dfd77ea43", "Sheaf.Paper.IntegralScalarTensorTowerComposition": "bdd82cb7407be9e2b1be3dc7cdae73da560a59fa"}, "results": {}, "time": "2026-10-28T00:24:01+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
