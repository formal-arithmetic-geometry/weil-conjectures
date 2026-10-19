## What changed

Proved `AlgebraicGeometry.ProEtale.condensed_point_basis` with its statement unchanged.
The finite-etale classification uses `equivPiOfIsSepClosed`. The ind-etale
classification evaluates at residue fields, proves local constancy at finite stages,
and uses reducedness and `liftPrimeSpectrum` for bijectivity. The continuous-map
bijection uses the prime-spectrum homeomorphism and clopen characteristic functions.
Locally constant algebras are already ind-Zariski.

A private categorical assembly lemma proves the equivalence onto affine ind-etale
schemes using the fully faithful relative spectrum functor and its essential image.
For the final natural comparison, private lemmas prove that LC(S, Ω) is the pushout
of LC(S, ℤ) and Ω over ℤ: localization and characteristic functions prove uniqueness,
and `liftPrimeSpectrum` supplies the map. Taking spectra gives the defining relative
test-object pullback, and its two projection equations prove naturality.

All helpers are proved in the original module. Both existing functor definitions
remain in place with identical signatures and bodies. The temporary interface and
split modules from the retained attempt are not delivered. No definition, existing
signature, public import, or consumer needs an adaptation. The node records the
actual proof route.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.condensed_point_basis`
(node `det-pe-condensed-point-basis`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the delivered module. The retained split obligations have
complete proofs incorporated as private helpers. No new nodes.

## No longer needed

Removed proof imports `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`,
`Mathlib.AlgebraicGeometry.Limits`,
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`,
`Mathlib.CategoryTheory.Limits.HasLimits`, `Mathlib.RingTheory.Etale.Pi`,
`Mathlib.Topology.Category.Profinite.CofilteredLimit`,
`Mathlib.Topology.Compactness.Compact`, `Mathlib.Topology.Homeomorph.Lemmas`,
`Mathlib.RingTheory.Etale.Field`, and
`Mathlib.Topology.Separation.Profinite`. These declarations are available through
the proof imports needed for their specialized declarations.

The proof no longer needs the planned dependency nodes
`def-weil-pbc-category-colimit`, `def-weil-size-convention`,
`lem-weil-pbc-closed-in-quasi-compact`, `lem-weil-pbc-compact-hausdorff-bijection`,
`lem-weil-pbc-etale-algebra-finite-product`,
`lem-weil-pbc-etale-algebra-over-field-product`,
`lem-weil-pbc-etale-ring-map-iff-etale-affine`,
`lem-weil-pbc-finite-separable-extension-etale`,
`lem-weil-pbc-profinite-clopen-basis`,
`lem-weil-pbc-tychonoff-product-quasi-compact`,
`lem-weil-pbc-profinite-limit-function-factorization`,
`lem-weil-pbc-finite-affine-coproduct-spectrum`, or
`lem-weil-pbc-spec-small-colimit-limit` as direct proof dependencies.
The existing finite-etale equivalence, prime-spectrum evaluation and direct ring
pushout proof replace their intermediate constructions. No blueprint unit statement
or step is bypassed: this proves the basis classification and specified test-object
identification used by `sk-prop-pe-condensed-point`.

The retained new modules `Sheaf.Paper.CondensedPointBasisDefs`,
`Sheaf.Paper.CondensedPointBasisScheme`, and
`Sheaf.Paper.CondensedPointBasisTestFunctor` are unnecessary and not delivered;
their corresponding new nodes were never landed and are not delivered either.

## Where the brief, the DAG or earlier work was wrong

The retained attempt had left the final comparison open and moved definitions to
an interface module. The direct pushout argument closes that comparison and allows
all helpers to remain private in the original module, preserving the definitions
in place. Current compiler checks do not reproduce a 60-second Lean timeout.
The retained dry run instead waited for delivery-worktree capacity and then
required a change record for a file-wide namespace opening. The opening is now
local to the four private helpers that need it; the interface check reports no
changes. No tool has been changed.
No false statement was found; empty profinite spaces, the empty finite product and
zero algebras are included. No arbitrary data is selected from an unproved theorem.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
