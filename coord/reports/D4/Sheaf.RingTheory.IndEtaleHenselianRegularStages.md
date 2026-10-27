## What changed

Filled `RingHom.indEtale_henselian_regular_stages` without changing its statement.
Three proved private helpers transport weak etaleness across universes, prove regularity
of the residue-field fibres, and transport initial parameter sequences along a flat
local map with field closed fibre. The main proof applies regular-map ascent, obtains
domain structure from the connected regular affine scheme, identifies each local closed
fibre with a localization of the corresponding global fibre, and applies the parameter
helper. The helper uses the flat height formula and the existing theorem on regular
systems of parameters and all their initial quotients. Empty parameter lists and empty
fibres are covered by the same proof.

The fibre proof uses the already proved absolutely-flat API in
`WeilConjectures.RingTheory.ProEtale.WeakDimension`, following the first paragraph of
Stacks Tag 092Q directly. The node's proof and proof dependencies reflect this route.
All public imports and the public theorem signature are preserved.

## Proved and sorry left

Closed the single existing hole in
`RingHom.indEtale_henselian_regular_stages`
(node `lem-sfb-ind-etale-henselian-regular-stages`).
Added zero holes and zero split-off statements. The three private helpers
`weaklyEtale_of_across`, `regular_fibres`, and `parameters_over_field_fibre`
have complete proofs. No `sorry` remains in the delivered Lean module.

Validation: the complete proof compiled, and the cleaned import set compiled again
in 11.1 seconds without errors or warnings. `#print axioms` reported exactly
`[propext, Classical.choice, Quot.sound]` for the public theorem; thus this theorem
is also transitively free of `sorryAx` against the compile-server library.

## No longer needed

The proof no longer needs nodes `lem-weil-pbc-weak-etale-field` and
`lem-weil-pbc-etale-algebra-over-field-product`: absolute flatness directly supplies
reducedness and field prime localizations, so finite subalgebras and their product
classification are unnecessary. Their obsolete `tool_uses` approvals are removed
while all other approvals retain their order. The corresponding `Sheaf.RingTheory.WeaklyEtaleField`
and `Mathlib.RingTheory.Etale.Field` proof imports are removed.

Removed the direct proof import `Sheaf.RingTheory.IndEtaleStability`: its bundled
principal-Zariski and colimit stability assertions are not used. The ind-etale to
weakly-etale implication and base-change stability are used through the source and
Mathlib APIs already exposed by the retained imports, so the corresponding stability
node remains a proof dependency.

Also removed redundant direct proof imports of
`Mathlib.RingTheory.Localization.AtPrime.Basic`,
`Mathlib.RingTheory.Noetherian.Basic`,
`WeilConjectures.AlgebraicGeometry.Regular`,
`Mathlib.AlgebraicGeometry.Properties`,
`Mathlib.RingTheory.RingHom.Flat`, and
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`.
Their declarations are still used through retained imports; their mathematical nodes
remain dependencies. No module is withdrawn, and no global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The old plan's finite-etale subalgebra/product-of-fields calculation was unnecessary:
the adopted source library already proves the absolutely-flat criterion and its
field-localization consequence. The alternate route is the first paragraph of the
proof of Stacks 092Q itself. The parameter and height steps, all hypotheses, and the
unit route are retained. No statement or definition repair was needed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
