## What changed

Completed the Lean proof of
`AlgebraicGeometry.exists_regular_equations_of_smooth_closedImmersion` without changing its
signature. The proof chooses compatible affine charts, uses the smooth-algebra kernel result,
restricts to an affine basic open, and constructs the quotient-spectrum isomorphism. Its final
morphism equation follows from naturality and the pullback restriction isomorphism.

Added and proved `Algebra.exists_regularSequence_smooth_surjection` in
`Sheaf.RingTheory.SmoothQuotientRegularSequence`. It proves finite generation of the kernel,
identifies the fibre prime and the local quotient, proves both fibre local rings regular, and
extracts a regular prefix of a parameter system generating the fibre kernel. It then applies the
separate flat-family lifting result below. This follows the assigned fibre-regularity route;
it does not assume regularity of an arbitrary generating list.

Added and proved `Algebra.exists_regularSequence_of_flat_quotient_fiber` in
`Sheaf.RingTheory.FlatQuotientFiberRegularSequence`, the finite affine form of Stacks 063W(2).
The proof lifts fibre generators up to units, identifies the tensor of the kernel using flatness
of the quotient, and applies the existing finite-module tensor Nakayama theorem to find a single
multiplier outside Q. It then combines generation after inverting that multiplier with regularity
on a principal neighbourhood.

Added and proved `Algebra.exists_isRegular_of_fiber_local` in
`Sheaf.RingTheory.FiberRegularSequenceNeighbourhood`, the specified-list lifting argument of
Stacks 063W(1). First spread regularity on the Noetherian fibre and clear its base denominator.
Induct on the list, applying the existing scalar annihilator criterion and principal-quotient
flatness API underlying the algebraic fibre-Cartier theorem. Quotient and localization tensor
comparisons transport the tail induction; the retained prime gives properness. This works over
an arbitrary base, without imposing Noetherianity on A or R.

There are no statement changes, definition changes, forced consumer adaptations or change records.
The unit's `realized` statement and steps are empty; no unit statement or unit proof step is
bypassed. All four modules compile together with `lcompile.py --all`, with no errors or
warnings. All compilation uses the project wrapper.

## Proved and sorry left

Original holes: 1. Closed: 1, in
`AlgebraicGeometry.exists_regular_equations_of_smooth_closedImmersion`.
Original holes left: 0. New holes added: 0. No delivered Lean file contains `sorry`.

The three new public theorems are also proved completely:

- `Algebra.exists_regularSequence_smooth_surjection`
  (`lem-pur-smooth-quotient-regular-sequence`).
- `Algebra.exists_regularSequence_of_flat_quotient_fiber`
  (`lem-pur-flat-quotient-fiber-regular-sequence`).
- `Algebra.exists_isRegular_of_fiber_local`
  (`lem-pur-fiber-regular-sequence-neighbourhood`).

Every private helper is proved. No hole is split off. Existing declared dependencies are used
as the stage-3 brief permits; this packet does not claim to close their remaining holes.

## No longer needed

Removed the following direct proof imports from the item module:

- `Mathlib.RingTheory.Smooth.Basic`
- `Mathlib.RingTheory.Smooth.Flat`
- `Mathlib.RingTheory.FinitePresentation`
- `WeilConjectures.RingTheory.SmoothFibreRegularLocal`
- `WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters`
- `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Mathlib.RingTheory.Flat.Equalizer`
- `Mathlib.Algebra.Module.LocalizedModule.Exact`
- `Mathlib.RingTheory.LocalRing.Module`
- `Mathlib.RingTheory.FiniteType`
- `Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood`
- `WeilConjectures.AlgebraicGeometry.FibreCartierLocal`
- `WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness`

Some of these algebra modules remain needed through the three new modules; removing their
direct imports is import pruning only, not withdrawal of their mathematics. The complete
fibre-parameter and flat-family dependency chain is now attached to its proper algebra node.
No existing module is withdrawn.

The following old scheme-level proof dependencies are no longer needed for this route:
`lem-pc-recd-fibre-cartier-local`, `def-pc-relative-effective-cartier`,
`def-nagata-effective-cartier-ideal`, `def-weil-flat-morphism`, and
`def-sbc-locally-finite-presentation`. The flat-family theorem instead uses the existing
algebraic `lem-pc-algebra-fibre-cartier-local`, preserving the successive-Cartier route.
Removed the stale `lem-pc-recd-fibre-cartier-local` and the unused general
`lem-pc-affine-flat-module-localization-preserves-flatness` entries from the item's `tool_uses`
list; the remaining approvals retain their order.

In the new flat-quotient module, also removed unused draft imports
`Mathlib.Algebra.Module.LocalizedModule.Exact`,
`Mathlib.RingTheory.LocalRing.Module`, `Mathlib.RingTheory.Spectrum.Prime.Noetherian`,
`Mathlib.RingTheory.TensorProduct.Quotient`, and
`WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness`.
The fibre-neighbourhood module likewise does not import the last module: Mathlib's flat
localization instance and `Module.Flat.trans` give its ring special case directly. Consequently
`lem-pc-affine-flat-module-localization-preserves-flatness` is removed from the
proof dependencies and the item's top-level `tool_uses`: its general localized-module
statement is not needed. Mathlib's ring localization flatness suffices.

The other former proof dependencies remain used in the algebra results: finite presentation,
kernel finite generation, flat tensor injectivity, Nakayama, localizations, fibre Noetherianity,
fibre regularity, regular parameters, and the algebraic Cartier criterion. No claim is made
that these modules have become unreachable from all five targets.

## Where the brief, the DAG or earlier work was wrong

No error in the assigned statement was found. Smoothness over an arbitrary base does not make
the ambient ring Noetherian. Only the fibre algebra is Noetherian; applying the Noetherian
closed-fibre regular-sequence theorem directly to the ambient ring would add a hypothesis.

During this session I discarded a draft which attempted to prove regularity for an arbitrary
list generating the kernel. Such a list may be redundant and need not be regular. That draft
was never delivered; neither its module nor its proposed statement is present in this packet.
The final proof chooses a prefix of a regular parameter system on the fibre.

The shared library retired three Sheaf twins during the session. The smooth-algebra module
uses their recorded WeilConjectures declarations, matching the current node attachments.

Edge cases checked against the new theorems: for an empty fibre sequence the finite-module
Nakayama argument makes the ideal zero near the retained prime; the empty sequence is regular
there because the prime survives. For the zero ideal the same argument applies. The fibre-local
properness implies the original ideal is contained in Q, so the final quotient cannot be the
zero ring after inverting elements outside Q. A zero ambient ring cannot have the specified
prime. Flatness of A/I is essential for the tensor-kernel identification. No Noetherian base
hypothesis is inserted.

## New nodes

`lem-pur-smooth-quotient-regular-sequence`: proved smooth-algebra corollary, module
`Sheaf.RingTheory.SmoothQuotientRegularSequence`. Its proper fibre-local kernel is generated by
a regular parameter prefix; the flat-family lifting lemma supplies the neighbourhood. It is
strictly the affine algebra part, with the scheme and pullback construction proved in the item.

`lem-pur-flat-quotient-fiber-regular-sequence`: proved independent flat-family source result
063W(2), module `Sheaf.RingTheory.FlatQuotientFiberRegularSequence`. It isolates generator lifting
and finite-module Nakayama from the smooth-fibre regular-local argument.

`lem-pur-fiber-regular-sequence-neighbourhood`: proved specified-list lifting result 063W(1),
module `Sheaf.RingTheory.FiberRegularSequenceNeighbourhood`. It isolates the successive
nonzerodivisor and flat-quotient induction, with explicit comparisons for tensor products,
quotients and principal localizations. The empty list is handled directly.

The new nodes serve `lem-pur-divisor-class` through the original local-coordinate and
regular-equation nodes. `blueprint_refs.py search` found no blueprint node for the fibre-lifting
or smooth quotient algebra results. Semantic, type-pattern and Mathlib source searches are
recorded from actual `msearch.py` calls. No new node replaces a declared existing dependency.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
