## What changed

The tensor presentation theorem now obtains the generic closed symmetric monoidal derived structure and packages its tensor comparison together with two explicit split-off field statements. The main theorem is proved by constructing `TensorPresentation` from the adjunction and evaluation witnesses. The proof imports only the reduction-model definitions, the generic closed symmetric monoidal theorem, and the two field modules.

## Proved and sorry left

The original `tensor_presentation_exists` sorry is closed (1 of 1). Two strictly simpler field statements remain as named split-off theorems:

- `tensor_presentation_adjunction` in `Sheaf.Paper.IntegralHomTensorPresentationAdjunction` (sorry; node `new-sf-integral-hom-models-exist-tensor-adjunction`).
- `tensor_presentation_evaluation` in `Sheaf.Paper.IntegralHomTensorPresentationEvaluation` (sorry; node `new-sf-integral-hom-models-exist-tensor-evaluation`).

## No longer needed

The prior direct proof imports for site-derived tensor descent, scalar internal-Hom adjunction, ringed internal-Hom exact restriction, global-sections RHom, and independent K-flat resolutions are no longer needed by this route and were removed from the item module. The generic closed symmetric monoidal theorem and reduction-model definitions remain required.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the tensor-Hom adjunction and representative evaluation as one directly constructible field. The available generic theorem supplies the closed structure and a right-tensor adjunction; the required presentation records a left-tensor adjunction transported through symmetry, together with a separate representative evaluation normalization. These are therefore recorded as two strictly simpler split statements.

## New nodes

- `new-sf-integral-hom-models-exist-tensor-adjunction`: adjunction field required by `TensorPresentation`.
- `new-sf-integral-hom-models-exist-tensor-evaluation`: signed representative evaluation and comparison-square field required by `TensorPresentation`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomTensorPresentation": "9d22c18b340793ca0c074e02f43a39a91dc998d8", "Sheaf.Paper.IntegralHomTensorPresentationAdjunction": "60ec8dec764a28dc22e260124b02dd371ee9d4cd", "Sheaf.Paper.IntegralHomTensorPresentationEvaluation": "1903b202a6a7ce3a07fbc16b63e1e61126e3e245"}, "results": {"Sheaf.Paper.IntegralHomModelsExist": {"hash": "0b8abf2fceaad79febc3ab025a333a597e4ccdd3", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T08:38:30+0800", "transitive": 0, "version": 1}
```

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
