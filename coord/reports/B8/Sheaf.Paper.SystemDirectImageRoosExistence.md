## What changed

Replaced the hole in `WeilConjectures.systemDirectImage_roosExistence` by a complete
construction of its product and distinguished triangle. The construction uses the
existing `UniverseProof.evaluationData` and `CoreWork.natural_roos` from
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`, through a proof-only
`import all`, for the specified canonical `coefficientConstantTowerLimit`. The
canonical derived-limit unit is invertible on K-injectives. Grothendieck module
sheaves supply the derived products.

For a complex representing the restricted system image, compose the evaluation
factorization with the new restricted-tower comparison. `Pi.mapIso` gives the
product comparison. Naturality at each adjacent arrow proves its commutation with
one minus shift. `Triangle.isoMk` then transports distinguishedness, giving the
projection and boundary explicitly. The first vertex is the actual total
coefficient limit, so the requested final isomorphism is identity.

Added the proof-only import of
`Sheaf.Paper.SystemDirectImageRestrictedTowerComparison`. Its one public theorem
isolates just the identification of the evaluated restricted system tower with the
finite direct-image tower, including its adjacent maps. It asserts nothing about
inverse limits, products or distinguished triangles. The original item statement,
public imports, and all existing downstream declarations are unchanged. Updated
only the existing node's proof, proof dependencies and proof origin.

Validation: both delivered Lean files compile in import order through `lcompile.py
--all`, in 1.4 s and 7.2 s respectively. Neither has a style warning. No other
existing module or interface was changed.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.systemDirectImage_roosExistence`
(node `stage3-weil-system-direct-image-roos-existence`). Its proof body has no holes.

Added one named hole:
`WeilConjectures.systemDirectImage_restrictedTowerComparison`
(node `stage3-weil-system-direct-image-restricted-tower-comparison`), in its own new
module, with its source and full proof in words in its docstring.

This is a decomposition, not a net proof: one hole closed, one hole added, net zero.
The original item now has zero holes; the whole delivery has one. The new lemma is
strictly the tower-identification part of the old argument. The construction of
the actual limit vertex, product, projection, boundary and distinguished triangle,
and the proof that the transported transition is the required one, are completed
in the original module using that lemma and the existing generic results.

## No longer needed

The original proof dependency
`stage3-pur-canonical-tower-roos-comparison`
(`Sheaf.Paper.CoefficientConstantTowerRoosComparison`) is not needed by this proof.
It also controls particular canonical projections, whereas the present existence
statement permits the explicitly transported projection. The generic Milnor
triangle suffices and does not require exact products in the abelian category.
It had not been imported by the original file, so no import was removed. This is
only a dependency removal from this item's proof plan, not a claim that the module
can be withdrawn globally. No module is withdrawn or globally pruned.

The calculus remains a public import because it occurs in the unchanged statement.
All three added proof imports are used: the restricted-tower theorem, the generic
Milnor construction, and the canonical complex-level right-derived-unit API.

## Where the brief, the DAG or earlier work was wrong

The original single proof step combined two different tasks: obtaining the Milnor
triangle for the actual total derived limit, and identifying its evaluated tower
with the particular finite direct-image tower. The first task is already proved
in the library and is now used directly. The latter still requires a simultaneous
comparison that respects the recorded quotient arrows; independent isomorphisms
at each level would not suffice. OrdinaryPullbackEvaluationCalculus gives the
ordinary sectionwise square, and CompletedCoefficientStrictImage gives a generic
derived diagram square in its own coefficient models, but neither directly states
this identification for arbitrary supplied S and the sf transition definitions.

The new lemma retains the original hypotheses, and adds only a representing
complex and its representing isomorphism. Its proof route uses the strong
reductionModel field of S, not a presumed coherence of unrelated evaluation
isomorphisms. Zero complexes, empty schemes, unbounded inputs and arbitrary
morphisms require no exception. There is no statement repair or change record.

## New nodes

`stage3-weil-system-direct-image-restricted-tower-comparison` is attached to
`Sheaf.Paper.SystemDirectImageRestrictedTowerComparison` and
`WeilConjectures.systemDirectImage_restrictedTowerComparison`. Its proof first uses
the simultaneous K-flat reduction model, then the sequence-site scalar
restriction/direct-image square, then the representative characterizations of the
input transitions and derived restriction comparisons, and finally localization
of exact tower evaluation. It is the part before any inverse limit or Roos
triangle is formed. The node records the three Mathlib searches, source, precise
Lean statement, and the existing declared dependencies for these steps.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.SystemDirectImageRestrictedTowerComparison": "ee237ffd1334fdab9b545608141c0cc43fd516f3", "Sheaf.Paper.SystemDirectImageRoosExistence": "6f7349ed81dbc47338d74e3da9a03e5f3fb22775"}, "results": {"Sheaf.Paper.SystemDirectImageRoosEvaluation": {"hash": "48bda4884070da4580f3ccf715ab32c34a6d9190", "status": "OK"}, "Sheaf.Paper.SystemDirectImageRoosPresentation": {"hash": "5618a40ae636091c3f08be3eeada991fbf519eb3", "status": "OK"}}, "seconds": 18, "time": "2026-10-28T12:13:54+0800", "transitive": 0, "version": 1}
```

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
