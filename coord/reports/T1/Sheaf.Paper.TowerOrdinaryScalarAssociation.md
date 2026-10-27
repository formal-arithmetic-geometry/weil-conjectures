## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.SpTowerClasses.ordinaryScalarAssociation_exists`
with a proof from three separate ordinary-category statements. Its signature,
including all hypotheses, is unchanged. The proof constructs the association
isomorphism by uniqueness of left adjoints with a common right adjoint. Two
proved private helpers establish the comparison's transpose formula and
faithfulness of the recorded integral Forget functor. The coefficient and root
identities follow by transposing, applying Forget, using the two endpoint
calculations, and cancelling the direct-image comparison isomorphism.

Added the proof imports `Sheaf.Paper.TowerScalarUnitAbelianTranspose` and
`Sheaf.Paper.TowerScalarRootAbelianTranspose`. Their common public dependency is
`Sheaf.Paper.TowerRestrictedScalarAdjunction`. The latter also constructs
componentwise abelian direct image (`abPush`) and its adjunction
(`abAdjunction`) directly from the existing geometric adjunction; neither
definition contains a hole or chooses data from an unproved existence theorem.
The parent node's proof, proof dependencies and proof origin now describe this
route. Three new modules and their nodes carry the remaining steps.

Server compilation of all four modules succeeded individually in import order
(approximately 8--16 seconds per file). The final item cleanup explicitly references
four unused hypotheses inside the proof, preserving its statement. No existing
module besides the assigned item is changed. There are no change records or
forced adaptations.

## Proved and sorry left

This delivery is a decomposition, not a net proof gain. It removes the one
existing hole in `ordinaryScalarAssociation_exists` (node
`lem-sp-tower-ordinary-scalar-association`) and adds three holes below it: one
closed upper hole, three added lower holes, net minus two. The assigned module
has zero remaining holes. The private lemmas `forget_map_injective` and
`comparison_transpose` are completely proved.

Every remaining hole added by this delivery is the entire proof of one named
public theorem (all names below have namespace
`AlgebraicGeometry.ProEtale.SpTowerClasses`):

- `restrictedScalarAdjunction_exists`, node
  `lem-sp-tower-restricted-scalar-adjunction`, in
  `Sheaf.Paper.TowerRestrictedScalarAdjunction`. This constructs the normalized
  restriction/direct-image comparison and the target ordinary adjunction. It
  mentions neither the coefficient-unit arrow nor the root comparison nor their
  endpoint equations.
- `scalarUnit_abelianTranspose`, node
  `lem-sp-tower-scalar-unit-abelian-transpose`, in
  `Sheaf.Paper.TowerScalarUnitAbelianTranspose`. This is only the coefficient
  generator calculation after passage to the abelian adjunction. It constructs
  no scalar association isomorphism or restricted scalar adjunction and has no
  root conclusion.
- `scalarRoot_abelianTranspose`, node
  `lem-sp-tower-scalar-root-abelian-transpose`, in
  `Sheaf.Paper.TowerScalarRootAbelianTranspose`. This is only the root calculation
  after passage to the abelian adjunction, using the Kummer middle-map
  normalization. It constructs no scalar association isomorphism or restricted
  scalar adjunction and has no coefficient-unit conclusion.

Each theorem has a source and a complete natural-language argument in its
module docstring and its node. The endpoint statements apply to any comparison
with the specified section normalization; neither assumes the normalized
restricted scalar adjunction from the first theorem. Thus the remaining tasks
are distinct parts of the argument, rather than the association-existence
statement with its hypothesis or conclusion repackaged. Empty charts and zero
sections cause no additional assumptions: the comparison uses identities,
coefficient calculation uses the unit generator, and the root calculation uses
kernel uniqueness and additive/tensor maps.

## No longer needed

No original public import is removed, and no module is withdrawn. There is no
claim of global pruning. The parent proof no longer directly uses
`def-pur-cochain-coefficient-arrows` or
`def-coef-semilinear-system-models` to construct a concrete ringed-pullback
square and balanced tensor associator. Its proof dependencies are instead the
three new statements and `def-sp-tower-class-systems`. The scalar-system
interface remains needed by the new adjunction statement and is not globally
pruned. The unit's own route, integral reduction followed by coefficient
extension with the two normalizations, remains intact.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The prior plan describes the balanced
associator but does not provide the concrete ringed-pullback square required by
the existing `scalarAssociation_existsUnique` interface. The new route isolates
the ordinary adjunction and checks the endpoint maps separately, avoiding a
second construction of that square. Existing generic adjoint-uniqueness lemmas
supply the categorical combination, but searches found no existing specialized
normalized tower adjunction or either abelian endpoint calculation.

The invertibility and Chern-normalization hypotheses remain in the original
signature although this ordinary-category argument does not use them. No
faithfulness assertion about derived evaluation is introduced.

## New nodes

`lem-sp-tower-restricted-scalar-adjunction` records the normalized ordinary
restriction/direct-image comparison and scalar adjunction. Its proof first
constructs the comparison on sections, then proves full faithfulness of
forgetting integral residue scalars by locally lifting scalars to integers, and
then composes the natural Hom bijections. Its Lean attachment also records the
concrete definitions `abPush` and `abAdjunction`.

`lem-sp-tower-scalar-unit-abelian-transpose` records only the coefficient-unit
transpose calculation. Its proof uses the two normalized scalar adjuncts,
coefficient pullback on the generator, and integral unit normalization, extending
from locally constant integer scalars by sheaf separatedness.

`lem-sp-tower-scalar-root-abelian-transpose` records only the root transpose
calculation. Its proof identifies the integral Kummer kernel map from the
specified middle map and then uses scalar-unit and tensor/line evaluation
normalizations on root generators.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.TowerOrdinaryScalarAssociation": "b9042ffe726e9b2560d0cbe6573a14f0e628797d", "Sheaf.Paper.TowerRestrictedScalarAdjunction": "a4cf8fbb0efdf77d25b4a6ad60fa67e2f3fd6116", "Sheaf.Paper.TowerScalarRootAbelianTranspose": "39715a9399f9b458307ba4e3429761c9ce7bf5ad", "Sheaf.Paper.TowerScalarUnitAbelianTranspose": "7197dfee19bd058a4a0ce77e680028f70fa6645c"}, "results": {"Sheaf.Paper.TowerChernOrdinaryScalarPullback": {"hash": "ca1b891a82f29bd183913ad0bdba9c7316d20d9c", "status": "OK"}}, "seconds": 165, "time": "2026-10-27T23:49:41+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
