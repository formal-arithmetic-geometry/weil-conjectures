## What changed

Copied and repaired `Sheaf.Paper.ConstantCompletionFlatAndQuotientsQuotient` in the sandbox. Added
`Sheaf.Paper.ConstantCompletionQuotientKernel` as a strictly smaller kernel component. The main
proof now proves sectionwise surjectivity by transporting a set-theoretic section through the
constant sheaf and delegates only the kernel equality to the named split-off theorem.

## Proved and sorry left

Proved `CategoryTheory.ConstantCompletion.flat_and_quotients_quotient`'s sectionwise
surjectivity component. One sorry remains in
`CategoryTheory.ConstantCompletion.constant_quotient_kernel`, the kernel component split off
in node `new-e4-constant-completion-quotient-kernel`.

## No longer needed

The original proof-plan dependency `lem-weil-pbc-sectionwise-adic-algebra-limit` is no longer
used by the Lean proof or by the split-off kernel node. The proof uses only
`Sheaf.Paper.ConstantCompletionBasic` and the new kernel module.

## Where the brief, the DAG or earlier work was wrong

The existing DAG step described the full sectionwise adic tower argument, but the quotient map
in this item is directly induced by the coefficient ring quotient. Its surjectivity has a short
constant-sheaf proof, so the tower theorem is unnecessary for this component. The kernel part
is a separate local-to-global statement and is recorded as a new node.

## New nodes

`new-e4-constant-completion-quotient-kernel`: kernel identity for the section map of the finite
constant quotient, with its proof currently split off as the sole remaining sorry.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionFlatAndQuotientsQuotient": "ff853abce395463f9409bb2595e1c33f7ace629a", "Sheaf.Paper.ConstantCompletionQuotientKernel": "dce03ab8d48f7c21344f0ad9128975ab4bd4177b"}, "results": {"Sheaf.Paper.ConstantCompletionFlatAndQuotients": {"hash": "2a480b27a0b0954e775bcd29ac3fa2c9268b0f6a", "status": "OK"}}, "seconds": 10, "time": "2026-10-28T04:16:06+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
