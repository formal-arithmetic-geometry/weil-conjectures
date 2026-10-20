## What changed

Filled the two operator-naturality proofs in
`lean/Sheaf/Paper/ProjectionFormulaBaseChangeNaturality.lean`, preserving all existing
signatures, definitions and public imports.

`CategoryTheory.derivedProjectionFormulaMate_naturality` evaluates the naturality of the
existing upstream `Adjunction.rightAdjointProjectionMap`. Three proved private helpers
identify the transported forward arrow with that same mate at the specified coefficient
object, transport both inverse identities by an explicitly constructed isomorphism, and
combine forward naturality with cancellation of those identities.
`SheafOfModules.ringedProjectionFormula_operator_naturality` applies the existing
`ringedProjectionFormula_totalization` to each representative, uses those helpers, and
cancels the two inverse identities to obtain naturality of the specified inverse.
It does not replace the prescribed inverse by a separately chosen inverse. The abstract
transport and cancellation argument is proved independently of the representative data;
the ringed specialization supplies its two first-component equations and totalization
identities.

The original pro-etale base-change theorem is retained unchanged with its original hole.
No new statements with holes, data choices, definition repairs or adapted modules are added.
The completed proofs are checked through lcompile.py and the required delivery preflight.

## Proved and sorry left

Closed 2 of the original 3 holes, with 0 new holes and 0 split-off statements:

- `CategoryTheory.derivedProjectionFormulaMate_naturality`.
- `SheafOfModules.ringedProjectionFormula_operator_naturality`.

The one remaining hole is the original
`AlgebraicGeometry.Scheme.proEtaleProjectionFormula_baseChange`, under node
`lemma-weil-pbc-projection-formula-base-change-naturality`. Its statement and its complete
source/proof docstring are unchanged. This is a partial proof delivery, not a decomposition.
The operator proof uses the existing totalization theorem as a dependency, as prescribed
by DAG step 2; this delivery makes no claim to close holes in its imported dependencies.

## No longer needed

Removed these unused private imports from the item:

- `Sheaf.Paper.CondensedAmbientExchange`.
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.

The completed operator argument uses the generic recorded arrows and their totalization
identities. The remaining base-change statement uses the already publicly imported
ring-sheaf pro-etale exchange and canonical tensor comparison, so it needs neither the
condensed-module-object exchange nor the separate pro-etale strict-perfect inverse.
The explicit import of `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` is
retained for unfolding the canonical comparison behind the recorded forward arrows.
An experiment removing it timed out; the final packet retains that proof environment.

No mathematical dependency node is declared obsolete: the original base-change proof
still needs the general ringed-square coherence argument and its normalization bridge.
The general square-coherence import is unused by the completed proofs and has been
removed from this file. Its node remains part of the plan for the untouched third hole.
No declaration or module is withdrawn, and the blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing first-variable naturality is already part of the upstream bifunctor
transformation; a fresh transpose calculation is unnecessary. This is the same
naturality argument packaged by the existing library, not a new mathematical route.

DAG steps 3 and 4 do not directly typecheck as a specialization of
`SheafOfModules.ringedExchangeTensorCoherence` on the original pro-etale sites.
`RingedTensorCorner.{u,w}` requires a site in `Type u` with `Category.{u}` and ring/module
coefficients in that same universe. For `Scheme.{u}`, the original small pro-etale site
has objects in `Type (u + 1)` and morphisms in `Type u` (also explicitly documented in
`ProEtaleInverseImage.lean`). A compile experiment confirmed that
`Category.{u + 1} X.ProEt` cannot be synthesized. Attempting to build that corner directly
also forces expensive incompatible category comparisons. The independent-universe
canonical tensor interface addresses individual pullbacks, but the square-coherence
interface is still the equal-universe one. Completing this third proof needs either
transport through a small-site model with all canonical comparisons identified, or an
independent-universe square-normalization bridge; the abstract mate-coherence calculation
itself is already available upstream in
`Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`.

No theorem is marked disputed: this is an interface and normalization gap, not a
counterexample to the mathematical base-change assertion. No public interface was changed
to hide it, and no new unproved bridge was introduced.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
