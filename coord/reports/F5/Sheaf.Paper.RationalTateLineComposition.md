## What changed

Filled `AlgebraicGeometry.ProEtale.RationalP1.lineComparison_comp` in
`Sheaf.Paper.RationalTateLineComposition`, preserving its statement and public import.
The proof follows the existing normalization route in full:

- Transpose the module compositor and its maps to their underlying abelian adjuncts.
- Prove coefficient composition using `condensedPushforwardHom_comp`.
- Prove root composition sectionwise from the normalized restriction maps and
  `Over.pullbackComp_left_fst_fst`.
- Use monoidality of the abelian compositor and the finite projection normalizations
  to prove integral comparison composition.
- Cancel the epimorphic scalar-extension quotient to prove finite rational composition.
- Test on every finite-field coprojection to prove algebraic-closure composition.
- Apply the module adjunction calculation in each coefficient branch.

All auxiliary lemmas are private and proved in this module. A private definition
selects the existing rational or closure abelian map, so the final adjunction
calculation keeps the large coefficient structures folded. Added only proof imports:
module adjunction unit coherence, the monoidal natural-transformation tensor equation,
and access to the existing private normalization lemmas in CartesianCoefficientTwists
and ProEtaleRootsOfUnityInverseImage. The item's node now describes these explicit steps.
The final normalization application reuses the exact coefficient instances and
Cartesianity witness stored in `lineComparison`; its elaboration builds an application
of the proved `linePull_adjunct` helper, which the kernel checks normally. This avoids
re-elaborating the large coefficient data and adds no assumption.

Validation: the prescribed `lcompile.py` single-file compile passed cleanly in
41.2 seconds, below the 60-second limit. The delivered source has no profiling
options or temporary probe modules.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.RationalP1.lineComparison_comp`
(node `lem-sfb-rational-tate-line-comparison-composition`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the item or is
added elsewhere by this delivery. Existing imported declarations are unchanged.

## No longer needed

None. All three declared proof dependencies remain needed. The proof follows the
integral/rational/closure route in the node and keeps the unit's route. No module or
node is withdrawn and no existing import is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The original node's plan suffices without another split.
The integral composition argument uses the joint monicity of the finite projections;
it does not require preservation of arbitrary inverse limits by inverse image.
The statement applies unchanged to identity maps, empty schemes and both coefficient
branches, with no properness or base-change invertibility hypothesis.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalTateLineComposition": "7be2264f1513d073760d64b812dd4425dc4f3fff"}, "results": {"Sheaf.Paper.ScalarP1UnitMateComponent": {"hash": "532c89db1d2eb27a104d3e7c6cbf9d173fdcbc7d", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T10:46:18+0800", "transitive": 0, "version": 1}
```

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
