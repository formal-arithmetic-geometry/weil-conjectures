## What changed

Proved `AlgebraicGeometry.ProEtale.compactSupportSiteCoherence` with its original signature.
The refinement square uses composition of the canonical proper direct-image mates and
the defining proper/open comparison square. The composition square uses the already
proved chosen `originComposition` equation and the actual common-refinement changes.
The restriction square is the existing `compactSupport_exchange_transport` theorem.
A structural induction supplies identity, concatenation, push, pull and boundary changes;
cancellation proves equality of pro-etale routes from equality of etale routes.
All proof helpers in the item are proved. The main geometric and pasting helpers
are private; the new public implementation API exposes explicit functor and component
endpoints for the canonical maps.

Repaired the equality-transport implementation of `properTransportRefinementPlus` in
`Sheaf.Paper.RefinementComparisonIsomorphism`. The old transport of complete derived
functor structures caused the inverse calculation to exceed 60 seconds. The replacement
constructs the transport by induction on equality of scheme maps. Its proved equality
with the former `eqToIso (congrArg ... h)` certifies that the mathematical map, endpoints
and all existing signatures are unchanged. The defining module is unclaimed. The change
record, including all 122 current transitive importers and their holders, is
`coord/changes/h4-compact-support-refinement-transport.md`.


Repaired the compositor representations in the item. Named functor/component interfaces
and `CoherencePastingData` retain exactly the original four etale and six pro-etale factors;
the record contains no commutativity hypothesis. Keep compactification choices abstract
through the pasting calculation, and specialize them afterward. The ambient evaluation of
the original origin compositor is identified with `originCompositionModel` by the existing
proved `originComposition_model` equation. The change record with the old and new definitions
and all added public API is `coord/changes/h4-compact-support-compositor-interfaces.md`.
It requests an independent meaning review of these equivalent representations. The theorem
signature and all original public imports are unchanged. The latest downstream check finds
zero Lean importers of the item; the item and its DAG attachment are retained.

Updated the existing theorem and refinement-definition nodes to record the actual proof
and the equivalent equality-transport construction. No target statement or source-library
module changes. Both delivered modules compile without warnings or holes: the refinement
module in 0.9 seconds and the coherence module in 27.3 seconds. The original `ProperCompositionSiteTransport` consumer compiled against
the repaired dependency in 15.2 seconds, without edits.

## Proved and sorry left

Holes closed: 1, `AlgebraicGeometry.ProEtale.compactSupportSiteCoherence`.
Holes added: 0. Split-off statements: 0. Remaining holes in both delivered modules: 0.
The new equality-transport reflexivity and equivalence API lemmas are proved by equality
induction.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`.
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`.
- `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`.
- `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `WeilConjectures.Compactification.BaseChange`.
- `WeilConjectures.Compactification.Refinement`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` and
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` (reviewer correction,
  2026-10-21: no declaration of either is used; both remain available transitively).

Removed the following direct proof-dependency edges from the coherence node:

- `cor-cbc-derived-extension-zero-base-change`.
- `def-amb-etale-compact-support`.
- `def-cbc-compact-support-square`.
- `def-cbc-exchange-map`.
- `def-cbc-finite-constant-coefficient-transport`.
- `def-compact-support-direct-image-detailed`.
- `def-weil-finite-type-morphism`.
- `lem-cbc-compactifiable-compatible-tower`.
- `lem-cbc-extension-zero-base-change`.
- `lem-cbc-extension-zero-composition`.
- `lem-cbc-proetale-extension-zero-base-change`.
- `lem-cbc-proper-open-interchange-coherence`.
- `lem-cbc-strict-tower-proper-open-calculus`.
- `lem-sf-comparison-pullback-exact`.
- `lem-sf-proper-open-comparison-site-normalization`.
- `lem-weil-pbc-coefficient-exchange-mates`.
- `lem-weil-pbc-exchange-forget-coefficients`.
- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-mate-pasting`.
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`.

The canonical chosen-composition equation supplies the needed composition normalization;
there is no need to rebuild compatible towers or specialize the strict-tower calculus.
The existing exchange transport supplies the complete restriction square; its proper/open
and coefficient-exchange proof is not repeated. The generic proper/open definition gives
the needed site normalization directly, including the lifted coefficient ring. Mathlib
supplies the Noetherian hypotheses. Boundary naturality and induction give finite pasting.

The removed top-level `tool_uses` approvals are:
`cor-cbc-derived-extension-zero-base-change`, `lem-cbc-compactifiable-compatible-tower`, `lem-cbc-extension-zero-base-change`, `lem-cbc-extension-zero-composition`, `lem-cbc-proetale-extension-zero-base-change`, `lem-cbc-proper-open-interchange-coherence`, `lem-cbc-strict-tower-proper-open-calculus`, `lem-sf-comparison-pullback-exact`, `lem-sf-proper-open-comparison-site-normalization`, `lem-weil-pbc-coefficient-exchange-mates`, `lem-weil-pbc-exchange-forget-coefficients`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-mate-pasting`, `lem-weil-pbc-noetherian-open-subscheme-noetherian`.

These are removals of direct imports and direct proof edges. Their declarations remain
available for other consumers; no module is withdrawn by this packet.

## Where the brief, the DAG or earlier work was wrong

The DAG plan redoes normalization already present in the definitions and the proved
chosen-origin compositor. The shorter proof keeps the unit statement and uses that
existing compositor. Its common-refinement changes are the actual proper/open maps,
not newly defined conjugates. The implementation defects were equality transport through a large derived-functor
structure, and kernel conversion of concrete chosen-compositor projections. Equality
induction repairs the former. Explicit functor/component endpoints and abstract choices
through the pasting proof repair the latter. Both preserve the canonical factors. Finite-type schemes need no separated structure morphism;
the proof uses only the stated separatedness of the individual compactifiable maps.

## Reviewer corrections (2026-10-21)

The signature of `coherenceEtaleCompositor` is restored verbatim (only its body is the
componentwise `coherenceCompositorOfChanges` form of the same four factors), so the
`lean.statement` of def-pur-chosen-compactification-compositors stays exact. Two unused
plain imports are removed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
