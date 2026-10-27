## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.proper_open_complement_square` in
`Sheaf.AlgebraicGeometry.ProperOpenComplementSquare`, preserving its entire statement and
all public imports. No definitions or consumers changed. Scheme permanence instances prove
the geometric clauses; `Scheme.Pullback.range_fst` proves the complement equality. Exact
open extension commutes with homology, so the existing module-level disjoint vanishing
and `Functor.isZero_mapDerivedCategory_obj` prove the termwise derived restriction is zero.
`Functor.leftDerivedExactComparison`, applied to the actual pullback's universal counit,
identifies this with the specified total derived pullback on the unbounded category.
Updated the existing node's proof, proof dependencies and proof origin to this route.

The item compiled cleanly through `lcompile.py` after import cleanup. The proof uses no
extra hypotheses, reducedness assumption, bound on complexes, new intermediate statement
or arbitrary witness construction. Empty schemes and the zero coefficient ring are
covered by the same range and zero-object arguments.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.proper_open_complement_square`
(node `lem-sfb-proper-open-complement-square`).

Holes remaining in the item: zero. Holes added: zero. Split off: zero.

`#print axioms` confirms that existing transitive dependencies still contribute
`sorryAx`, alongside `propext`, `Classical.choice` and `Quot.sound`. This delivery closes
the item from the existing declared dependencies; it does not claim their closure is
axiom-free. The temporary diagnostic command was removed before delivery.

## No longer needed

Removed private proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.Restrict`
- `Mathlib.AlgebraicGeometry.ResidueField`
- `WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`

The general range-of-pullback theorem (existing Mathlib leaf
`lem-weil-pbc-base-change-image`) replaces the field-point lifting argument, so this proof
no longer needs nodes `lem-weil-pbc-open-preimage-fibre-product`,
`lem-weil-pbc-morphism-from-spec-field`, or
`lem-weil-pbc-field-point-factors-through-closed-immersion`. The separate exactness packaging
node `det-prop-sfb-module-pullback-exact-main` is also unnecessary here: the source library
already supplies the exactness instances used by the comparison. Removed its and the
field-point lemma's obsolete `tool_uses` entries, preserving the other approvals in order.
The explicit proof-dependency entries `def-pc-fibre-product` and
`sk-def-sfb-module-derived-lower-shriek` are unnecessary (the statement continues to use
them). Finite-type and separated permanence remain mathematically used;
the removed Mathlib imports are available through the preserved public imports.
No module is withdrawn, and no claim is made that these results are globally unused.

## Where the brief, the DAG or earlier work was wrong

No statement error. The planned residue-field argument and the need to import a separate
exactness packaging theorem were unnecessary. The source library already provides the
required instances. The unbounded argument can use exact-functor cohomology comparison
(existing node `lem-weil-pbc-exact-functor-bounded-below`) and detection of zero by all
homology, avoiding explicit choices of representative complexes. This preserves the
unit's closed-complement vanishing step and does not invoke proper base change itself.
No new nodes or definition changes.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
