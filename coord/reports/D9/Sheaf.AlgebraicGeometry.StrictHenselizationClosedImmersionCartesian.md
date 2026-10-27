## What changed

Proved `AlgebraicGeometry.Scheme.isIso_strictHenselizationClosedImmersionCartesian`
in its assigned module, without changing its signature, definitions, or public imports.
The proof follows the current three-step DAG plan. Four proved private helpers handle:
small filtered presentations and ind-etaleness; bijectivity of the specified quotient
factor; the quotient pushout after applying Spec; and pasting with a chosen closed chart.
The final proof chooses that chart, obtains its geometric residue embedding, and identifies
the required lift with the pullback comparison isomorphism by both projections.

Added private imports of `Sheaf.AlgebraicGeometry.StrictLocalClosedChartMap`,
`Sheaf.RingTheory.IndEtaleQuotientTwoBaseInverse`,
`WeilConjectures.RingTheory.PointedEtaleSmallFiltered`,
`WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions`, and
`Mathlib.AlgebraicGeometry.Pullbacks`. Updated only the item's DAG proof, proof dependencies,
and proof origin to describe the actual assembly, including smallness of the indexing
categories and the quotient pushout. No other existing module or node is changed.

Read the current blueprint unit and the Stacks source at Algebra Tags 05WS, 08HR, and 08HT.
The proof retains arbitrary schemes and nilpotents. The ideal is proper because the local
quotient is nontrivial; hence it lies in the local maximal ideal. Quotient representatives
prove bijectivity of the chart's specified factor from the inverse theorem's surjectivity
and kernel conclusions, so its existential quotient algebra structure is never substituted
for the chart's existing algebra structure. No arbitrary object is chosen from a holed
existence statement.

Validation: the final module compiled cleanly through `lcompile.py` in 6.3 seconds.
The exact original theorem signature and public-import list were compared unchanged,
and both new Sheaf imports passed `import_direction.py may` without a cycle.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.isIso_strictHenselizationClosedImmersionCartesian`
(node `lem-trf-closed-immersion-strict-localization-cartesian`).
The item's module has zero remaining `sorry`; this delivery adds zero holes and no nodes.
Its proof uses the existing statements `AlgebraicGeometry.Scheme.strictLocalClosedChartMap`
and `Algebra.ind_etale_quotient_two_base_inverse`; their existing holes are outside this
delivery. This is a proof from the declared dependencies, not a claim that their own proofs
or the entire target import closure are complete.

## No longer needed

Removed these old private imports from the item:

- `Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension` (duplicate private import;
  the original public import is retained)
- `Sheaf.Paper.StrictHenselizationFunctoriality`
- `WeilConjectures.RingTheory.MapIntoHenselianColimit`
- `WeilConjectures.RingTheory.PointedEtaleFiltered`
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`
- `WeilConjectures.RingTheory.StrictlyHenselianQuotient`
- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`

These inputs remain available or needed through the chart and inverse theorems and the
preserved public imports. No module is withdrawn or asserted globally unnecessary.
The direct DAG dependency `lem-sc-pointed-etale-filtered` is replaced with the already
proved combined `lem-sc-pointed-etale-small-filtered`, which also supplies the small model
needed for the ind-etale presentation. The affine spectrum, open immersion, fibre-product,
chart-map and two-base inverse dependencies are retained. The tensor-quotient Mathlib leaf
is recorded explicitly for the proved source-library quotient pushout implementation.
No mathematical branch of the unit's route is bypassed. No existing tool-use approval is
removed: those older inputs remain used transitively by the chosen dependency theorems.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The item's old imports and docstring still
named the pre-split direct algebraic inputs, while its current DAG already supplied the
compatible chart-map and two-base inverse statements. The implementation now uses those
interfaces as requested. To turn the defining pointed colimit into the small filtered
presentation required by the ind-etale predicate, the Lean proof additionally invokes the
existing combined essential-smallness/filteredness theorem. The DAG records that detail.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
