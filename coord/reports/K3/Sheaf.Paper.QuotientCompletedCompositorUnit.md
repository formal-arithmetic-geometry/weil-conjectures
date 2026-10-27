## What changed

Filled the nine theorem proofs in `Sheaf.Paper.QuotientCompletedCompositorUnit`.
All existing declaration signatures and all non-theorem constructions are preserved.
The proof identifies the local RHom condition through the small completed site,
compares the two completion reflectors by their unit-normalized Hom bijections,
and reuses the existing strict-tower comparison. Pushforward completeness follows
from the existing direct-image/completion unit equation. The constant coefficient
comparison is natural and uniquely normalized by the actual augmentation.

The restricted adjunction is constructed from its prescribed Hom equivalence.
The compositor and identity equations follow by taking ordinary adjunction
transposes, using source naturality and Mathlib's conjugation unit equation.
Private proved helpers organize these categorical calculations. No new public
statement or definition is introduced. The existing node's proof and dependencies
are updated to describe this argument.

## Proved and sorry left

Closed nine original holes, all in namespace
`AlgebraicGeometry.Scheme.QuotientCompleted`:

- `complete_iff_local`
- `koszul_identification`
- `pull_complete`
- `push_complete`
- `reflector_identification`
- `constant_identification`
- `adjunction_existsUnique`
- `compositor_unit`
- `identity_unit`

Zero holes remain in the item. Zero holes are added; zero statements are split off.
Existing dependency theorems are used as stated, including those still containing
`sorry`; this delivery proves the item from those declarations.

## No longer needed

The separate coefficient-map computation, DVR argument, and generic ringed
pushforward-preservation argument from the original plan are unnecessary here:
`pbcActualCompletedPullback_tower`, the integral datum, and
`pbcActualDirectCompletionIso_exists` already provide the required specialized
interfaces. The proof uses the actual ordinary derived adjunction and comparison
interfaces instead of reproving their generic ringed construction.

Removed unused private imports:

- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.RingedPushforwardCompletion`

The temporary proof imports of `Mathlib.CategoryTheory.Limits.HasLimits` and
`Sheaf.CategoryTheory.NativePrincipalCompletenessSmallModel` are also unnecessary.
The exact `AsSmall.{0}` transport is proved privately from the existing native
slice-test and local-divisibility restriction interfaces.

Accordingly this node no longer directly depends on
`def-per-proetale-ring-inverse-image-comparisons`,
`lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-ringed-pushforward-completion`,
`lem-sfb-ringed-derived-monoidal-comparisons`, or
`lem-weil-pbc-adjunction-of-natural-bijection`. Mathlib supplies the last construction.
The corresponding obsolete top-level tool approvals for the DVR, generic ringed
pushforward completion, and generic ringed monoidal comparisons are removed.
These modules can remain transitively needed elsewhere; no module is withdrawn,
and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false, and no definition repair was needed. The DAG plan
repeated work already provided by the existing strict-tower and direct-completion
comparisons. It also omitted the explicit small-site transport required to align
the local RHom slice universes with the ringed Koszul reflector interface. The
updated proof records that transport and the existing normalized interfaces.
The unit's route is preserved. There are no new nodes or forced adaptations.
The first preflight requested a record for the scoped proof commands;
`coord/changes/K3-quotient-completed-proof-contexts.md` records their scope and
the zero current Lean importers. No public signature or definition body changes.

Validation: the final module compiled cleanly in 26.4 seconds after import cleanup;
all 21 existing public signatures match the source, and the item has zero `sorry`s.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
