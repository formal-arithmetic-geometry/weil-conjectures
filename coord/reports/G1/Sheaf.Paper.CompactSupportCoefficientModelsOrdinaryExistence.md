## What changed

Copied the assigned module into the sandbox and proved
`compactSupportCoefficientModels_ordinary_exists` by a direct sectionwise tensor
balancing construction.  The proof builds the module comparison from the
sectionwise pushout, checks restriction compatibility on pure tensors, and
transports it through presheaf sheafification and the extension-existence
identifications.  The displayed generator formula is proved by the sectionwise
balancing equation.  The one remaining coefficient-ring pushout is exposed as
`completedConstantSquare_isPushout` in the new module
`Sheaf.Paper.CompletedConstantSquarePushout`.

## Proved and sorry left

Closed `WeilConjectures.compactSupportCoefficientModels_ordinary_exists` (one
assigned `sorry`).  Added one strictly smaller `sorry`:
`WeilConjectures.completedConstantSquare_isPushout`, the sectionwise completed
constant coefficient pushout (node `new-completed-constant-square-pushout`).
This is a decomposition: one hole closed, one added, net zero.  The local
tensor-balancing proof and its two helpers have no holes.

## No longer needed

The delivered ordinary comparison does not directly use the previously planned
adic-basis-limit or completed-integral-finite-free declarations; those remain
proof dependencies of the split pushout node.  The unused proof import `Sheaf.Paper.RamifiedQuotientSectionPushout` was removed
after copying the general balancing proof.  No original import was removed.
The tensor-cancellation APIs are used by the local sheafification proof.

## Where the brief, the DAG or earlier work was wrong

The original proof step bundled the ring pushout and the sheafified tensor
comparison into one basis argument.  The existing library already supplies all
of the sheafification and tensor-balancing machinery, so the genuinely missing
part is the sectionwise completed coefficient pushout.  The DAG has been updated
to record that smaller split and the actual imports and proof route.

## New nodes

`new-completed-constant-square-pushout` —
`WeilConjectures.completedConstantSquare_isPushout` in
`Sheaf.Paper.CompletedConstantSquarePushout`.
Its statement is the sectionwise pushout of the constant map, the two
constant-to-completion maps, and `completedCoefficientMap`; its proof is the
finite-basis/compatible-reduction argument described in the theorem docstring.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence": "25c366fb9d337136da1712745c964d938e66e150", "Sheaf.Paper.CompletedConstantSquarePushout": "3b94c12b4c4c4fd009ef0f992df66e2579974ffc"}, "results": {"Sheaf.Paper.CompactSupportCoefficientModels": {"hash": "b802a913c8d344956667b3d4e8e833177a8f7f8e", "status": "OK"}}, "seconds": 99, "time": "2026-10-28T10:23:26+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
