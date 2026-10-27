## What changed

Replaced the sole proof hole in `Sheaf.Paper.FiniteCoefficientEtaleSliceOrigin`
without changing its statement or public imports. The proof restricts to fixed
coefficients on the chart, descends each cohomology sheaf, and uses the already
proved source-library theorem
`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology`.
It reflects the precise interval bounds through the faithful comparison functor,
uses full faithfulness to identify the descended homology with the chosen heart
origins, and transfers every covering family and finite model along that
isomorphism. Finally it applies the marked constant-model transport statement.

Added `Sheaf.Paper.FiniteCoefficientSliceRestriction`: a concrete composite of
scalar restriction, the existing constant-scalar encoding equivalence, and chart
restriction. Its additivity, exactness, and preservation of vanishing on the
ringed slice are proved. No data is chosen from an unproved existence theorem.

Added separate modules `Sheaf.Paper.FiniteCoefficientSliceHeartOrigin` and
`Sheaf.Paper.FiniteCoefficientSliceModelTransport` for the two remaining steps.
The first concerns one object in the abelian heart and has no derived object or
bounds. The second assumes a marked origin and transports a supplied constant
complex; it asserts no existence of an origin or finite models. These separate
parts do not restate the original bounded derived existence theorem.

All four modules compiled together using `lcompile.py --all`: restriction 9.9 s,
heart statement 8.8 s, transport statement 17.2 s, original theorem 47.1 s.
There were no errors. The original statement has unused binders `hab` and the
arrow `g` inside `hloc`. Their names and types are preserved; the unused-variable
linter is disabled only for this declaration to retain its original signature. No existing module besides the item, and no existing interface, was
changed. No source-library declaration was changed or removed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finiteCoefficient_etale_slice_origin`
(node `lem-weil-pbc-finite-coefficient-etale-slice-origin`). Its complete Lean
proof combines the heart origins, the existing bounded-derived-origin theorem,
reflection of homological bounds, transport of local finite models, and marked
complex transport.

Added two holes, both whole named public theorem bodies with source and complete
natural-language proofs:

- `AlgebraicGeometry.Scheme.finiteCoefficient_slice_heart_origin`, node
  `lem-weil-pbc-finite-coefficient-slice-heart-origin`.
- `AlgebraicGeometry.Scheme.finiteCoefficient_slice_model_transport`, node
  `lem-weil-pbc-finite-coefficient-slice-model-transport`.

Thus this is a decomposition: one old hole closed, two smaller holes added,
zero holes remaining in the item itself, and two in the new modules. It is not
claimed as a net reduction of the sorry ledger. The restriction construction,
its exactness theorem, its three instances, its vanishing theorem, and its
private scalar-exactness helper have complete proofs and introduce no holes.

The new statements were checked on empty charts, zero modules, and the zero
coefficient ring. Heart descent uses finite modules over a finite ring, hence
finite presentation. Complex transport has no boundedness requirement because
its equivalences and constant-functor comparisons are exact and natural in
all differentials, before passage to the derived category.

## No longer needed

No original public import was removed and no module was withdrawn. The new
proof-only imports are the two split modules and the proved source-library
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology`.

The old direct proof dependency
`lem-weil-pbc-finite-ring-constructible-derived-origin`
(`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`, currently quarantined) is
not used: the proved bounded-origin theorem already handles arbitrary
cohomology sheaves in the comparison image, without any constructibility
predicate. The stronger constructible-derived theorem is unnecessary for this
item. This does not withdraw its quarantined module or change its attachment.

The old direct dependencies `def-weil-proetale-constructible-sheaf` and
`pqf-lem-locnoeth-lft` are also unnecessary for this proof. No noetherian
inheritance or intrinsic constructibility predicate enters the new argument.
The finite-level comparison node `prop-weil-pbc-site-comparison-finite-level`
is replaced as a direct dependency by the existing general site comparison
and bounded-origin API. Slice localization, constant scalar encoding, and
ringed derived restriction remain needed, explicitly in the new nodes; they
are not globally pruned. No claim is made that the bypassed nodes are unused
by other targets or source declarations. The blueprint unit's realized nodes
and required route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original route asked for a stronger constructible-derived theorem than this
item requires. A proved source-library bounded-origin theorem already supplies
the derived induction once each cohomology sheaf has an etale origin. What is
still missing is the actual coefficient and slice comparison in the heart and
for supplied complexes, not another bounded-derived existence statement.

The two split statements isolate these missing comparisons. Neither makes the
original choice of a bounded derived origin: the main proof performs that step
using the source theorem, then proves the required bounds and finite models.
No statement is disputed and no target statement or existing definition changes.

## New nodes

`def-weil-pbc-finite-coefficient-slice-restriction` records the concrete chart
coordinate functor and its proved exactness and vanishing API, in the new
restriction module. It contains no sorry.

`lem-weil-pbc-finite-coefficient-slice-heart-origin` records finite local descent
of one module sheaf and the comparison marking, in its own new module. Its
remaining hole is strictly an abelian-heart problem.

`lem-weil-pbc-bounded-heart-etale-origin` attaches the already proved
source-library theorem on bounded derived origin from cohomology origins. The
record notes explicitly that its source theorem holds for arbitrary commutative
coefficients; this proof uses its finite-ring specialization. No new Lean
statement or source edit is made for this node.

`lem-weil-pbc-finite-coefficient-slice-model-transport` records normalization of
a supplied complex model through a marked origin, in its own new module. It
requires neither boundedness nor finite local cohomology and asserts no origin
existence. Its remaining hole concerns natural comparison isomorphisms only.

The original node's proof, proof dependencies and proof origin now follow the
compiled argument. All new nodes keep its chapter and unit. No change record is
needed because only the item's proof and entirely new modules were changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
