## What changed

Proved `WeilConjectures.ProjectionReduction.exists_witnessedFlatDomains` in
`Sheaf.Paper.ProjectionReductionWitnessedFlatDomains`, with eleven proved private helpers.
All existing public declarations, signatures, definitions and public imports stay unchanged.
Updated the node proof to match the fixed-module argument. No other module is edited.

The proof unpacks the existing bounded etale origin in constructibleFiniteTor, reflects
its prescribed Tor interval, and applies the finite-value constructible flat-model theorem.
The same P,Q are used at both coefficient levels. The reduced origin is the explicit
B-linear chain comparison followed by the inverse scalar representative and reduction
of the original origin. Termwise exact pullback and the signed total-tensor theorem give
the tensor-input model and sum interval. Source quasi-compact open-extension stability
and its comparison isomorphism give the domains for every compactification.

Private proof imports added: source ComparisonMonoidal, etale Stability.OpenImmersion,
etale Finiteness.FlatConstructibleComplex and ConstructibleEtaleModuleSheafComparison.
The source-library boundary is respected: no adopted source file is changed.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.ProjectionReduction.exists_witnessedFlatDomains`
(node `lem-sf-pf-reduction-witnessed-flat-domains`). Added 0 holes; split off 0 statements.
There are zero sorry occurrences in the delivered Lean file. This is a proof from existing
declarations, including the existing bounded-flat coefficient/site-square theorem whose
own proof remains postponed; it is not a claim that the transitive axiom closure is closed.
All eleven private helpers are proved.

Validation: prescribed lcompile.py compiled the full delivered module successfully in
54.7 seconds, with no warnings or errors.

Edge cases are included uniformly: identity coefficient reduction, level one, zero objects,
empty schemes, singleton degree intervals and identity/empty-source open immersions. The
proof assumes neither a nonzero ring nor flatness of the smaller coefficient ring over the
larger one. It uses the same universal Tor predicate against arbitrary sheaves in degree zero.

## No longer needed

Removed these private proof imports from the item:

- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`: the native constructibleFiniteTor
  hypothesis already contains bounded etale origin. The corresponding node
  `lem-weil-pbc-finite-ring-constructible-derived-origin` is not needed by this proof.
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`: use its source fixed-module theorem
  torAmplitudeIn_mapDerivedCategory_iff directly, without intrinsic realization or Plus
  transport. The mathematical node `lem-exc-comparison-tor-interval` remains needed.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: use the source fixed-module
  derived comparison square directly; `lem-weil-pbc-comparison-pullback` remains needed.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`: use existing exact constant-module
  pullback and leftDerivedFunctorIsoMapDerivedCategory; its mathematical node remains used.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: source
  derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso is the needed specialization;
  the mathematical ringed-topos tensor-comparison node remains used.
- `Sheaf.Paper.OpenExtensionFiniteTor`: use the source fixed-module theorem preserving the
  exact interval and its canonical comparison square. `lem-trf-open-ctf` remains used.
- `Sheaf.Paper.IntegralFinitePullbackComposition`: the unchanged openTensorIso already uses
  the source fixed-coefficient composition isomorphism; no integral-tower wrapper is needed.
  The mathematical composition node remains used by that definition.

Additional planned nodes not needed: `lem-sp-etale-pullback-line-flat-model` (termwise exact
pullback, flat preservation and constructible pullback suffice; no line tensor or shift),
`lem-sfb-finite-type-composition-base-change` and `def-weil-proper-morphism` as proof inputs
(the open-extension result needs only quasi-compactness of the open immersion, supplied by
Noetherianity of X). Their obsolete tool-use entries were removed. The public import of
EtalePullbackLineFlatModel is preserved as part of the existing public interface; no module
is withdrawn or claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The plan used the intrinsic finite-ring origin theorem even though the actual fixed-module
constructibleFiniteTor hypothesis already contains bounded etale origin. Several recorded
wrappers have intrinsic endpoints, while the item has fixed ModuleCat endpoints; the existing
source specializations apply directly. The ambient compactification need not be shown finite
type or Noetherian to apply the source quasi-compact open-extension theorem. These are shorter
proofs below the unit level; the witnessed-domain preparation and unit route are preserved.
The existing theorem docstring is retained as requested by the Lean skill; the updated DAG
and this report record the implemented route. No statement or definition was repaired.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
