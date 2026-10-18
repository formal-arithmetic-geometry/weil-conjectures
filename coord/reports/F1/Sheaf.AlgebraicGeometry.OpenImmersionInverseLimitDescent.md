## What changed

Proved `AlgebraicGeometry.IsOpenImmersion.eventually_of_inverseLimit` in
`Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent`, without changing its signature.
The proof applies the existing etale and monomorphism descent theorems, chooses a common
upper bound, and transfers both properties to every later stage. One proved private helper
establishes persistence of any base-change-stable property; its two auxiliary pullback-square
facts are proved locally inside that helper.
Universally injective etale recognition finishes the proof.

Updated the existing node's proof, proof dependencies and proof origin to match this route.
No definitions, public signatures, or public imports changed. No other module was adapted.

Validation: the final proof compiled cleanly with `lcompile.py` in 2.9 seconds after removing
redundant proof imports. `#print axioms` reported only `propext`, `Classical.choice`, and
`Quot.sound`; the diagnostic command was removed from the delivery. The statement is unchanged,
so this also verifies that its existing descent dependencies are fully proved.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.IsOpenImmersion.eventually_of_inverseLimit`
(node `lem-weil-pbc-descend-open-immersion-qcqs`).

Proved 1 of 1 original sorries. Zero sorries remain in the item; zero holes added;
zero split-offs. The private helper is proved. This is a proof, not a decomposition.

## No longer needed

Removed redundant proof imports:
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`: retired re-export of the directly
  imported `WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: no affine cover construction is needed.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: supplied by the unchanged public
  finite-presentation import.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: supplied by the directly imported descent module.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`: supplied by the recognition module.

Removed proof dependencies:
- `lem-weil-pbc-affine-opens-basis` and
  `lem-weil-pbc-lfp-affine-opens-finite-presentation`: Mathlib already supplies the complete
  implication from local finite presentation to local finite type, so no affine-cover
  argument is required here.
- `lem-weil-pbc-open-immersion-base-change`: both etaleness and monicity are transferred
  directly to every later stage, and recognition is applied there.

All unit statements and realized unit steps are retained. The unchanged public
`LimitAffineTransition` import is part of the existing statement interface. No claim is made
that a module is globally unreachable merely because this item no longer directly imports it.

The previous returned version declared a private `over_pullback_square` theorem duplicating a
word-for-word theorem already present in `WeilConjectures.AlgebraicGeometry.EtaleAffineChartDescent`.
That duplicate declaration was removed; the same pullback facts are now local proof terms inside
`property_over_pullback_comp`, so no duplicate theorem remains.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The plan's explicit affine-basis argument was unnecessary because
Mathlib already proves finite presentation implies finite type. Its final separate
open-immersion persistence step can be combined with the transfer of etaleness and monicity.
The original source Tag 0EUU uses image and isomorphism descent; this delivery follows the
existing node's shorter alternative via monomorphism descent. Edge cases require no extra
hypotheses: empty source or target and a singleton or non-antisymmetric directed preorder
are handled by the same categorical argument.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
