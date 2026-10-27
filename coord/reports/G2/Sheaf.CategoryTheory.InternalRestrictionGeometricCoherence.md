## What changed

Filled eleven existing theorem holes in
`Sheaf.CategoryTheory.InternalRestrictionGeometricCoherence`, preserving every public
statement and definition. All new helpers are private and proved.

The finite-limit proof uses the existing, proved internal-module limit creation theorem
from `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`. Restriction and trivial
inflation compose with the forgetful functors to give the original forgetful functor
and the identity, respectively; reflection of limits proves preservation.

The fixed-section functor is constructed from the subfunctor testing every further
arrow. Pulling its covering sieve back and applying separatedness proves sheafhood.
The explicit inverse natural Hom bijections give the adjunction, with inclusion as
its counit. The terminal-group equivalence follows from the unit action law.

The action and presentation identities are equalities of the actual functors.
For stipulated right adjoints, literal precomposition preserves limits by comparison
with presheaves. Identity structural ring data and the proved
`SheafOfModules.ringData_inducedModules` construct the ringed realization while
retaining the supplied adjunction. Coefficient changes use identity geometric
functors and actual scalar restriction. Their square is naturality of the specified
comparison. The two mate-coherence theorems apply Mathlib's composition, identity,
whiskering, and isomorphism results.

The constructions include empty finite diagrams and the terminal group. The fixed-section
argument uses covering sieves and their pullbacks, with no subcanonical-site assumption.
The coefficient-change construction permits the zero ring and nonflat ring maps.

Added proof imports of `Mod.Limits`, `GeometricModuleConstruction`, and `Sites.Subsheaf`.
Removed the original proof import of `ModulePullbackPushforwardAdjunction`.
Removed the file's two transparency overrides. Kept existing section binders and
suppressed only the unused-section-variable linter, since deleting those binders
would change existing signatures. Updated the item's proof record to cite the
existing limit-creation and induced-module nodes.

Validation: the remote single-file compile accepted all eleven proofs in 17.9 seconds;
its suggested `letI`-to-`let` style cleanup is included in the delivery.

## Proved and sorry left

Closed 11 of the original 12 holes, all in namespace
`CategoryTheory.InternalActionSite`:

- `restrictionGroupMap_isMonHom`
- `trivialSetActions_map`
- `internalRestriction_finiteLimits`
- `internalRestriction_identities`
- `internalRestriction_fixedAdjoint`
- `internalRestriction_terminal`
- `internalRestriction_presentedIdentities`
- `internalRestriction_ringed`
- `internalRestriction_baseCoherence`
- `internalRestriction_comparisonCoherence`
- `internalRestriction_coefficients`

One existing hole remains: `CategoryTheory.InternalActionSite.internalRestriction_scalarSquares`,
attached to `lem-sfb-internal-restriction-geometric-coherence`. Its statement, source,
and complete proof sketch are unchanged. No holes were added or split off.
This is a partial proof delivery, not a claim that the aggregate node is finished.

## No longer needed

The proved finite-limit clauses need no new tuple-limit or internal-module creation
lemma: `lem-sfb-modobj-forget-creates` already supplies the exact construction.
The ringed-realization proof uses literal precomposition and the induced-module theorem,
so it does not need to transport finite-limit preservation across the action-site
equivalence.

The removed proof import is
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`; none of the completed
proofs uses its declaration. Its DAG dependency, the internal-action equivalence,
`lem-sfb-internal-restriction-module-tensor`, the sheaf tensor, and module sheafification
are retained in the aggregate argument. In particular the unproved scalar-square clause
still needs its recorded tensor and sheafification argument. No existing module or node
is withdrawn or claimed globally pruned. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The tuple-limit construction was already available as a proved source-library theorem;
reimplementing it was unnecessary. Likewise the module direct image can be obtained
from the existing induced-module construction once the literal ring data is supplied.
No mathematical statement was changed or disputed, and the unit route is preserved.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
