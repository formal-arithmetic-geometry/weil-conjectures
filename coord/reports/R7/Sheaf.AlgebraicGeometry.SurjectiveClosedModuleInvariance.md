## What changed

Completed `AlgebraicGeometry.Scheme.sfbProEtale_surjectiveClosed_module_invariance`
in `Sheaf.AlgebraicGeometry.SurjectiveClosedModuleInvariance`. The existing public
statements and both finite-local-model definitions are unchanged. The previously
proved étale theorem and its helper are retained unchanged.

The proof uses the existing constant-scalar restriction equivalence, the direct-image
comparison from the pullback-encoding module, and the published fixed-ModuleCat
pro-étale topological-invariance theorem. Equivalence of the actual intrinsic
pushforward implies equivalence of its actual left adjoint and invertibility of the
specified unit and counit. Local constant comparisons, the slice equivalence and the
existing cover-refinement theorem preserve and reflect the identical module models.
The private fixed-model argument works for any predicate on those models; its final
specialization retains both finiteness and the original finite-free splitting maps.

Added proof-only imports of `Sheaf.Paper.ProEtaleConstantModuleConstructibility`
and `Sheaf.Paper.ProEtaleConstantModulePullbackEncoding` (using `import all` to reuse
proved private comparison helpers), `Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance`.
The DAG proof, proof dependencies and origin now describe this argument. Removed
obsolete tool approvals only; no new approval was inserted. No change record is
needed: no existing public signature, definition, visibility or public import changed.

The complete proof compiled remotely without diagnostics (9.3 seconds before the final
comment/import cleanup). The delivery dry run supplies the final compile and axiom
probe. The source-level proof uses existing stated dependencies; this does not assert
that their transitive proofs are already free of sorry.

## Proved and sorry left

Closed 1 of the 1 original holes:
`AlgebraicGeometry.Scheme.sfbProEtale_surjectiveClosed_module_invariance`
(node `lem-sfb-surjective-closed-module-invariance`).

Added 0 holes, split off 0 statements, and left 0 sorry occurrences in the delivered
module. All newly introduced helpers are private and fully proved. The already proved
`AlgebraicGeometry.Scheme.sfbEtale_surjectiveClosed_module_invariance` stays proved.

## No longer needed

No original import was removed. An exploratory explicit import of
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence` was removed;
the required constant-sheaf API is already available through the retained imports.

The following old proof dependencies are unnecessary for this item's new route:

- `lem-pe-constant-left-module-inverse-image`
  (`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`).
- `lem-weil-pbc-adjunction-lifts-group-ring-objects`
  (`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`).
- `lem-weil-pbc-ringed-topoi-module-adjunction`
  (`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`).
- `lem-sfb-geometric-inverse-image-constant-module`
  (`Sheaf.SixFunctors.GeometricInverseImageConstantModule`).
- `lem-sfb-proetale-object-inverse-image-restriction`
  (`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`).
- `lem-trf-weakly-etale-between-objects` (the Mathlib cancellation leaf).

The existing concrete scalar encoding, pullback and constant-sheaf APIs replace the
abstract algebraic-structure lifting and geometric constant-module argument. Direct
slice equivalence and the published localization-restriction comparison replace the
large object-inverse-image theorem. The arbitrary-morphism fixed-module pullback
needs no additional weakly-étale hypothesis on the refinement map. The five obsolete
top-level tool approvals among these nodes were removed in their original order.
These are removals from this item's proof route, not a claim that no other target
uses those nodes or that transitive imports disappear globally. No Lean module is
withdrawn, and the unit's flat-model route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original pro-étale plan called for rebuilding a module adjunction from set-level
algebraic structures. Existing concrete scalar-encoding equivalences make that
unnecessary. The published source-library topological-invariance theorem already
accepts ModuleCat coefficients; the stipulated intrinsic adjunction can be handled
by its right-adjoint comparison. No mathematical statement was changed, no edge case
excluded and no Noetherian or nilpotence hypothesis added.

The argument includes empty covering families and empty schemes. It never uses a
nonzero scalar, positive rank, or nonzero module. Every reflected local model and
its splitting maps are reused exactly, so the Boolean projectivity clause is
preserved in both directions. No source or launcher tool failure was encountered.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
