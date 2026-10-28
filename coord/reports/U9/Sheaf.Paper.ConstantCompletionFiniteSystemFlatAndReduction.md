## What changed

Proved `CategoryTheory.ConstantCompletion.finiteSystem_flat_and_reduction` with its
statement unchanged. Only the assigned Lean module and its own DAG node are changed.

The flatness proof uses the already proved private `ringSectionsFlat` helper from
`Sheaf.Paper.ConstantCompletionFlatAndQuotientsFlatness`, through a proof-only
`import all`. For each quotient ring, the supplied scalar tower and naturality of the
sheafification unit give an identity linear equivalence from the supplied quotient
module structure to the canonical quotient-section module structure. This transports
the existing flatness result without choosing or replacing any module structure.

For reduction, `flat_and_quotients_quotient` identifies the surjective maps from
sections of the constant A-ring sheaf to the finite levels and their kernels.
The quotient cone equation identifies their composite with the actual transition.
Mapping its kernel across the surjection gives exactly the ideal extended from
`I^(n+1)`. When `m <= n`, both this ideal and the transition kernel vanish; when
`n <= m`, the kernel formula is immediate. The inverse tensor-quotient equivalence,
the equality of these ideals, and the first isomorphism theorem give an A-algebra
equivalence, hence the required linear equivalence. Its pure-tensor formula reduces
to A-linearity of the actual transition.

Added only proof imports of the existing flatness-helper module, the existing
constant-quotient theorem module, and `Mathlib.RingTheory.TensorProduct.Quotient`.
The DAG proof, proof dependencies, and proof origin now describe this argument.
No definition, existing public signature, instance, attribute, or public import changes.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ConstantCompletion.finiteSystem_flat_and_reduction`
(node `new-p4-constant-completion-finite-system-flat-and-reduction`).

No holes remain in the item. No holes, declarations, or modules were added elsewhere.
Holes closed: 1. Holes added: 0. Split off: 0.

## No longer needed

No original imports were removed and no whole modules were withdrawn.
The item's previous node had no declared proof dependencies to prune.

The finite-presentation tensor-comparison argument in the original proof plan does
not need to be formalized anew for this item: the already proved constant-quotient
kernel formula and Mathlib's tensor-quotient equivalence give the finite-level
reduction directly. The inverse-limit conclusion of
`lem-weil-pbc-sectionwise-adic-algebra-limit` and the completed-flatness conclusion of
`new-h2-constant-completion-flatness` are not used in this finite-level proof.
Their modules retain their other consumers, and the former also supplies the adic
term and transition definitions already used by the unchanged statement.

## Where the brief, the DAG or earlier work was wrong

The original proof sketch is mathematically valid but omits existing proved library
ingredients. Its empty proof-dependency list hid both the constant-module flat-section
theorem and the constant-quotient kernel theorem. The proof now reuses these results,
so no fourth decomposition of the obligation is needed.

The scalar-tower hypothesis is used explicitly to compare the arbitrary supplied
quotient module structures with the canonical ones. No nontriviality, proper-ideal,
or nonempty-site assumption is introduced; the argument also covers the zero ring,
the zero and unit ideals, equal indices, and both orders of the two indices.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionFiniteSystemFlatAndReduction": "c45e512afc7b6cd9d23026b4ab34580bad774b79"}, "results": {}, "time": "2026-10-28T10:22:49+0800", "transitive": 0, "version": 1}
```

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
