## What changed

Replaced `WeilConjectures.IntegralHom.reductionTower_tensor_models`'s hole with a
complete assembly proof. It constructs the existing strict principal Koszul tower
from the actual completed uniformizer, chooses a representative of K by localization
essential surjectivity, and uses the canonical K-injective replacement of G.
A proved private `homTower_representatives` establishes naturality of the Hom
representative comparisons on an arbitrary diagram of K-injectives, using the
existing localization factorization and the inverse localized Hom augmentation.
The main proof proves the two-term support and both unit-term identifications
using the actual cone and single-complex APIs. It transports the given e to the
Hom representative and applies the same ordinary reduction model twice.

Added `Sheaf.Paper.KInjectivePrincipalTensor` with a complete proof of
`isKInjective_tensor_principalKoszul`: the tensor-cone isomorphism and the tensor
right unitor reduce it to the closure of the right orthogonal of acyclics under
distinguished triangles. This includes arbitrary scalar, zero scalar, unbounded
K-injective input, n=0, and the empty scheme. Added
`Sheaf.Paper.IntegralReductionKoszulModel` for the remaining ordinary reduction
comparison, with its complete proof plan. Existing signatures and public imports
are unchanged; no adopted source-library file is changed.

Single-file validation: the main assembly compiled cleanly in 14.0 seconds,
the proved K-injective tensor helper in 11.9 seconds, and the remaining statement
module in 4.4 seconds. Delivery runs the final compile and axiom probes.

Change record: `coord/changes/H1-integral-hom-tensor-model-helpers.md`.

## Proved and sorry left

Original holes closed: one,
`WeilConjectures.IntegralHom.reductionTower_tensor_models`
(node `lem-sf-integral-hom-tower-tensor-models`). The item has zero textual holes.
This is a decomposition, not an unconditional closure: one strictly smaller hole
is added, `WeilConjectures.IntegralHom.integralReductionTower_koszul_model`
(node `lem-sf-integral-reduction-koszul-model`). That statement contains no Hom,
no simultaneous tower models, and no existential representative choices; it is
exactly the ordinary derived reduction computation on the fixed coefficient tower.
It is used for both I and Hom(A,I). Net holes closed minus added: zero.

The additional theorem
`WeilConjectures.IntegralHom.isKInjective_tensor_principalKoszul`
(node `lem-sf-kinjective-principal-tensor`) is fully proved, with no added hole.
The private `homTower_representatives` is fully proved.
There are no other new or remaining textual sorries in this delivery.

## No longer needed

No existing public import is removed, and no module is withdrawn or claimed pruned.
A K-flat representative of K is unnecessary: the existing internal-Hom factorization
works for any source representative. The main node therefore no longer directly
uses `lem-pc-kflat-resolution`; this result is still needed by the new ordinary
reduction model for refining the given q.

The original main node's direct dependencies
`lem-pod-completed-integral-scalar-regular`,
`lem-sp-completed-integral-projection-divisibility`,
`lem-a1-principal-koszul-strict-replacement`,
`lem-weil-integral-reduction-tower-well-defined`, and
`lem-pur-derived-change-of-rings` are replaced at that level by the single ordinary
reduction model. Their mathematics is still needed beneath that model and is not
claimed globally pruned. `def-coef-hom-representative-evaluation` is replaced as a
direct proof dependency by `def-pur-derived-internal-hom` and the independent-universe
Hom quasi-isomorphism node, matching the actual constants used by the proof.
No signed tensor-Hom exchange or completeness theorem is imported for this proof.

## Where the brief, the DAG or earlier work was wrong

The stated plan named ingredient declarations but had no declaration assembling
the actual quotient transitions with the arbitrary-representative Koszul model.
The remaining node states precisely that step. The K-injective finite-cone step
was also unstated; it is now proved in this delivery. The source representative
need not be K-flat, so that part of the original plan was stronger than necessary.
The original theorem statement is unchanged, and the unit route is preserved.

## New nodes

`lem-sf-kinjective-principal-tensor` records the proved finite-free tensor closure
of K-injectives. Its proof uses the existing tensor-cone isomorphism, tensor unit
isomorphism, and Mathlib's triangulated right orthogonal. Source: first paragraph
of the current `lem-coef-integral-hom-reduction.proof.md`; Stacks 08J7 and 070G.

`lem-sf-integral-reduction-koszul-model` records the sole remaining ordinary
reduction model on the fixed strict principal coefficient tower. Its three proof
steps use flat-term K-flat refinement, the existing strict replacement and scalar
normalization, and localization invariance in the other tensor variable. Source:
the same first paragraph; Stacks 06YY, 08J7 and 07A6. LeanSearch, LeanFinder,
blueprint search and source searches found no exact existing statement for either
new node; the searches are recorded in each node.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReductionTowerTensorModels": "15b4489325348c7337cfcba8e3a5585e0b42a81b", "Sheaf.Paper.IntegralReductionKoszulModel": "6c54dec01f56e73ba8cf6d33ed4185ddacbb2ff8", "Sheaf.Paper.KInjectivePrincipalTensor": "1f9d7574a15e9b501ae57cd1ab7bd16fd801c362"}, "results": {"Sheaf.Paper.IntegralHomReductionTowerTransition": {"hash": "e78be063cd943a7cb4f81fcc2f8506a60ce1c9fe", "status": "OK"}}, "seconds": 130, "time": "2026-10-28T10:37:22+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
