## What changed

Reduced `WeilConjectures.ConstantPurityFrobenius.beta_existsUnique` to the
rational normalization of the two existing compactification-exchange
presentations. The proof cancels the explicit endpoint transports, identifies
the conjugated finite-stage components with the existing
`CommonWeilPurity.beta`, and proves uniqueness by evaluating at the literal
stage of each common-stage object. The naturality and invertibility of that
existing natural isomorphism are reused; neither is postulated again here.

Simplified `chainUnit_isIso` by unfolding only the two definitions of the same
uniquely specified unit; proof irrelevance identifies their identical choosing
propositions. Added local unfolding controls for the exchange proof
to avoid reducing large coefficient-category constructions during elaboration.
These do not export attributes or change any map.

Made the existing geometric proof arguments of `systems` explicit, retaining the
same system type by proof irrelevance. This lets its elaboration respect
transparency instead of searching through the large coefficient categories.
Removed an unused open namespace that shadowed field algebra notation. The item
then compiled in 49.1 seconds with profiling enabled; the profiling options were
removed for delivery. No current Lean module directly imports the item.

Added the proof import `Sheaf.Paper.FrobeniusCompactRationalNormalization`.
The new module imports the two constructions whose homs it compares.

Generalized the exchange helpers in the unclaimed module
`Sheaf.Paper.RationalWeilPurityNaturalityMate` by removing unused separatedness
assumptions on the arithmetic source and target in its two auxiliary namespaces.
Only separatedness of the morphism is needed for this compactification exchange.
All bodies, public imports and attributes are unchanged, and the main theorem
in section Main keeps its exact signature. No target statement changes.

Change records: `coord/changes/B3-exchange-unused-separatedness.md` and
`coord/changes/B3-constant-system-elaboration.md`.

Validation: the generalized `RationalWeilPurityNaturalityMate` and its unchanged
sole existing direct importer `WeilEquivarianceOfPurityAndTrace` both passed
`lcompile.py`. The unchanged importer copy was removed from the delivery after
that check.

## Proved and sorry left

The item started with two holes. Closed one textual hole,
`WeilConjectures.ConstantPurityFrobenius.beta_existsUnique`, and added one
strictly smaller normalization statement. This is a decomposition, not a net
hole reduction or an axiom-free proof of compact-support exchange.

The existing item hole remains:

- `WeilConjectures.ConstantPurityFrobenius.constant_purity_frobenius_square`
  (`lem-pur-constant-purity-frobenius-square`).

The one new hole is:

- `WeilConjectures.frobeniusCompactRational_normalization`
  (`lem-pur-frobenius-compact-rational-normalization`).

The adapted helper module retains its four pre-existing holes, with none added
or claimed closed:

- `WeilConjectures.RationalWeilPurity.rationalExchange_existsUnique`.
- `WeilConjectures.RationalWeilPurity.beta_naturality`.
- `WeilConjectures.CommonWeilPurity.beta_naturality`.
- `WeilConjectures.rational_weil_purity_naturality_mate`.

All four belong to `lem-pur-rational-weil-naturality-mate`. Its main theorem and
mathematical statement retain the separated scheme hypotheses; only its exchange
helper API is generalized. The new normalization concerns rational arrows before
conjugating by any exceptional coefficient system, and has no common-stage
naturality, invertibility or uniqueness conclusion. It is consequently a genuine
part of the argument, rather than beta_existsUnique under a different name.

## No longer needed

`lem-pur-rational-weil-naturality-mate` supplies an existing exchange construction
as a generic tool. Its use does not replace any step of the purity-transport
unit: the main constant/Tate/counit route is retained. The maintainer can record
the additional tool dependency during review.

No modules or nodes withdrawn. No existing imports removed. The main square's
six-step constant, Tate and counit proof route remains needed and remains recorded.
A separate existence, invertibility and uniqueness construction for common-stage
beta is unnecessary: reuse `CommonWeilPurity.beta` and the literal pair-category
object presentation after the rational normalization.

## Where the brief, the DAG or earlier work was wrong

The exchange helpers unnecessarily retained `IsSeparated X₀.hom` and
`IsSeparated Y₀.hom` as section assumptions, preventing reuse for the item's
more general auxiliary theorem. The compactification recipe requires a separated
morphism, not separated arithmetic source and target schemes. Removing the unused
section assumptions does not change the constructions. The main purity theorem
still needs and retains separated schemes.

The item and the existing purity-exchange module use two independently specified
rational presentations. Their endpoint equality alone does not establish equality
of their maps. The new normalization lemma isolates precisely this comparison;
the item proof explicitly transports the homs and then proves common-stage
uniqueness. Empty schemes, identity maps and identity coefficient stages are
included. No Frobenius-stable lattice is selected.

## New nodes

`lem-pur-frobenius-compact-rational-normalization` compares the literal localized
proper/open compactification exchange with the rational normalized exchange used
by the purity counit square. Its source is Step 2 of the current blueprint's
purity/trace equivariance proof; its docstring expands the whole-tower identity,
cancellation of realization comparisons, localization and endpoint transports.
LeanSearch, LeanFinder and repository/Mathlib grep found no existing equality of
these two maps. The existing normalization and descent constructions are reused.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
