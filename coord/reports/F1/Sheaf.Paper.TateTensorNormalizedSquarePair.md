## What changed

Replaced the original fixed-pair square hole by a proof from two smaller root-tensor
calculations. The proof constructs the evaluation-model isomorphisms from the supplied
normalizations, transports the ordinary square through the exact single embedding, and
uses the scalar adjunction, the tower transition axiom and naturality in the equality of
towers. Restriction of scalars is proved injective on morphisms between the relevant
single models using fullness and faithfulness of the single embedding and ordinary
restriction. No statement or definition of an existing public declaration changes.

All six delivered modules compiled in import order with `lcompile.py --all`. The
assigned module took 33.5 seconds and the finite-square support took 28.8 seconds;
the other four files took at most 5.3 seconds. Profiling options were removed before
delivery; the delivery tool recompiles the final files.

The two new obligations separate the finite derived mate computation from the ordinary
integral quotient-tower computation. The shared predicate `FiniteRootTransition` gives
an explicit formula on scalar multiples of local root tensors. It includes zero tensor
powers, equal indices, arbitrary coefficient sections and the empty scheme. No data is
chosen in a definition from an unproved existence theorem.

## Proved and sorry left

This is a decomposition, not a net decrease in holes: one original hole is closed and
two strictly smaller holes are added.

Closed: `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensor_normalizedSquare_of_pair`.
Its combining proof and all private helpers have no `sorry`.

Added and still sorry:

- `AlgebraicGeometry.Scheme.PurityIntegralTower.finiteTateTensor_transition_model`, in
  `Sheaf.Paper.TateTensorFiniteTransition`: the finite scalar mate represented on the
  ordinary root generators. It quantifies over no integral line, balanced model or
  abstract adic tower.
- `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensor_balanced_transition`, in
  `Sheaf.Paper.TateTensorBalancedTransition`: an equality of ordinary sheaf maps from
  the generator formula and the two balancing equations. It involves no derived
  normalization or abstract adic tower.

Each remaining theorem has a full proof in words, a source and a matching DAG node.
There are no other new holes and none in any definition or private declaration.

## No longer needed

No existing modules or nodes are withdrawn. The original module had no proof imports
to remove. The original root-sheaf and tensor-product definition nodes remain needed
by the two local calculations, now transitively instead of as a single vague proof
step. The blueprint unit route is preserved. Only proof imports are added to the
original module.

## Where the brief, the DAG or earlier work was wrong

The original proof step described the generator calculation but supplied no Lean
statement expressing its finite scalar mate or its ordinary quotient-transition
square. These are the two new, separate obligations. Existing local root-lifting and
generation results provide the intended ingredients but do not directly state either
calculation for the completed-coefficient presentations used here. The generic
categorical assembly is carried out rather than postponed under a renamed version
of the original statement. No statement has been found false or weakened.

Compilation profiling identified repeated conversion checks in the concrete derived
models. The ordinary finite square and its model isomorphism are in the new proved
supporting module `Sheaf.Paper.TateTensorPairFiniteSquare`. The localized natural
transformation calculation is proved generically in
`Sheaf.CategoryTheory.ExactSingleTransformation`. These changes add no holes and keep
the per-file limit unchanged.

## New nodes

`def-pur-tate-tensor-finite-transition`: explicit ordinary root-generator predicate,
in `Sheaf.Paper.TateTensorFiniteTransitionData`.

`lem-pur-tate-tensor-finite-transition`: finite derived scalar-mate computation,
in `Sheaf.Paper.TateTensorFiniteTransition` (one remaining hole).

`lem-pur-tate-tensor-balanced-transition`: ordinary integral quotient-tower square,
in `Sheaf.Paper.TateTensorBalancedTransition` (one remaining hole).

`lem-pur-exact-single-transformation`: proved localized exact-transformation formula
on any single degree, in `Sheaf.CategoryTheory.ExactSingleTransformation`.

`def-pur-tate-tensor-pair-evaluation-model`: constructive finite-model evaluation
isomorphism, in `Sheaf.Paper.TateTensorPairFiniteSquare`.

`lem-pur-tate-tensor-pair-finite-square`: proved transport of the two root calculations
to the finite-model square, in `Sheaf.Paper.TateTensorPairFiniteSquare`.

There are no change records: only the assigned module and new modules and their nodes
are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.ExactSingleTransformation": "21f30f445e030ba5d13c04b7fa02baa0bca42857", "Sheaf.Paper.TateTensorBalancedTransition": "02eac9ce45d49858222e0c3ff2dae237a4fc3139", "Sheaf.Paper.TateTensorFiniteTransition": "3116787794940082ecb4efe519bd3934fbb354fc", "Sheaf.Paper.TateTensorFiniteTransitionData": "8199747c0bda5d9d6be72271c3969847409f956e", "Sheaf.Paper.TateTensorNormalizedSquarePair": "3ef66fe720456f6d6a04567754eb401ca36ffd4c", "Sheaf.Paper.TateTensorPairFiniteSquare": "aa84cb33cba604bd80158a8c5b398722e9f60b41"}, "results": {"Sheaf.Paper.TateTensorNormalizedSquare": {"hash": "5c88e655ad302df2002923a5cefacf27856e2cb1", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T07:22:02+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
