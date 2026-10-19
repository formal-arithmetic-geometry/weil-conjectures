## What changed

Proved three normalization theorems in
`Sheaf.Paper.AdicConstructibleFiniteReductions`, retaining every public signature:

- `AlgebraicGeometry.Scheme.adicFiniteOrdinaryUnit_existsUnique`: construct insertion
  by the sectionwise extension/restriction adjunction and sheafification unit;
  naturality and faithfulness give its specified normalization and uniqueness.
- `AlgebraicGeometry.Scheme.adicFiniteResComp_existsUnique`: restriction composition
  is the identity; faithfulness gives uniqueness.
- `AlgebraicGeometry.Scheme.adicFiniteChangeComp_existsUnique`: construct the
  sheafified extension/restriction Hom equivalence, compose its adjunctions, and use
  uniqueness of left adjoints. Its unit equation gives the pure-tensor formula at
  scalar 1; linearity gives the formula at arbitrary scalars. The two Hom
  equivalences also prove uniqueness from the specified pure-tensor formula.

The added helpers are private and fully proved. No public definitions, statements,
or imports changed. The existing DAG route remains unchanged: these proofs supply
its ordinary scalar-insertion and balancing normalizations.

On resumption, the retained module compiled against the current library through
`lcompile.py` with exit code 0 in 25.9 seconds. The required delivery dry run
checks the declaration axioms and unchanged signatures independently.

## Proved and sorry left

Closed three of the eight original holes:

- `AlgebraicGeometry.Scheme.adicFiniteOrdinaryUnit_existsUnique`
- `AlgebraicGeometry.Scheme.adicFiniteResComp_existsUnique`
- `AlgebraicGeometry.Scheme.adicFiniteChangeComp_existsUnique`

No holes added and no statements split off. Five original holes remain, each tagged
with node `lem-sfb-adic-constructible-finite-reductions`:

- `AlgebraicGeometry.Scheme.adicFiniteUnit_existsUnique`
- `AlgebraicGeometry.Scheme.adicFiniteExtendComp_existsUnique`
- `AlgebraicGeometry.Scheme.adicFiniteOrdinaryComparison_existsUnique`
- `AlgebraicGeometry.Scheme.adicFiniteComparison_existsUnique`
- `AlgebraicGeometry.Scheme.adic_constructible_finite_reductions`

## No longer needed

None. The incomplete main theorem retains its existing proof-dependency imports.
No dependency node or module is pruned by these normalization proofs.

## Where the brief, the DAG or earlier work was wrong

The earlier report listed only one completed proof, although the sandbox now
contains three. Earlier split drafts were only in the scratchpad, not in the item
module, and introduced circular DAG dependencies. They remain excluded from this
delivery. The restriction normalization proof uses `Iso.ext`; `NatIso.ext` is not a
declaration in this Mathlib version.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
