## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.properOpenTowerComparison` in
`Sheaf.Paper.ProperOpenTowerComparison`. All existing public signatures, definitions,
attributes, public imports and docstrings are unchanged. The construction of lambda is
`asIso` of the specified `properOpenRestrictionMap`, so no object is chosen from a mere
existence theorem.

The proof establishes invertibility of the cartesian exchange by double mates and
conjugation of the existing `betaInv_isIso`. Explicit mate pasting factors gamma through
the cartesian beta mate and the clopen projection. The open-unit equation follows by
naturality and inverse cancellation. The open Hom-bijection identifies the adjunct with
gamma before evaluation; the cartesian normalization follows from `alpha_cartesian`.
The finite-origin and evaluation clauses then use `gamma_isIso` and `gamma_evaluation`.
Uniqueness uses the prescribed hom and `Iso.ext`.

All helper theorems are private and fully proved. The two private imports are
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` and
`WeilConjectures.CategoryTheory.Adjunction.ExchangeMate`, for the existing conjugation
and exchange/unit identities. The node's proof, proof dependencies and proof origin
record this route. Obsolete top-level tool approvals are removed in their original order.
The record `coord/changes/proper-open-tower-proof-reducibility.md` documents the
proof-local elaboration settings requested by server preflight. No other module,
statement, definition, target, unit or source-library file is changed.

Validation: the complete module compiled through lcompile.py in 21.5 seconds, with
exit code zero and no warnings. Both new proof imports pass import_direction.py.
Text comparison confirms that the six existing definition bodies and the public
theorem signature are unchanged. The module has no sorry tokens, diagnostic options
or lines exceeding 100 characters.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.StrictTower.properOpenTowerComparison`
(node `lem-sp-proper-open-tower-comparison`).
Added zero holes. Remaining holes in this module: zero. No split-off statements or modules.
Existing named dependencies, including betaInv_isIso, openToR_isIso, alpha_cartesian,
gamma_isIso and gamma_evaluation, are used as the stage-3 brief prescribes; this delivery
does not claim their proofs.

## No longer needed

Removed these private imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Paper.LocalizeRingedSiteMorphism`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`

Their categorical basics remain available through the unchanged public dependencies
and the two actual proof imports; the site and resolution modules are not needed for
an independent K-injective construction here. In particular, the following original
proof dependencies are removed:

- `lem-weil-proetale-weakly-etale-localization`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-diagram-site-realization`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`

The obsolete top-level tool approvals for eight of these nodes are removed; the
exact-functor factorization node had no such approval. Existing statement dependencies
are preserved. This is pruning of this item's proof route only: no module or declaration
is withdrawn, and no assertion is made that these nodes are unused elsewhere or absent
from transitive imports. The compact-support unit route and its realized records stay.

## Where the brief, the DAG or earlier work was wrong

The original plan rebuilds the cartesian exchange with K-injective diagram resolutions.
That work is unnecessary given the already declared cartesian betaInv isomorphism:
the four adjunctions and the iterated-mate/conjugation identity prove the required
exchange isomorphism directly. The remaining normalization uses the actual published
compositors and projection, with all associators and unitors retained. No false
statement or definition repair was required.

For compilation, the pasting and projection calculations are proved with abstract
functors before specialization. This avoids expensive unfolding of the concrete
strict-tower derived operations. The final unit-identity specialization also keeps
the scheme maps explicit: local aliases caused kernel conversion to unfold the pullback
and its derived functors. The file is still compiled as one module, at the standard
server limit; no timeout or heartbeat limit is raised.

Server preflight requested a change record for the local reducibility attribute.
`coord/changes/proper-open-tower-proof-reducibility.md` records the exact added
commands and the downstream query (zero current Lean importers). These are local
elaboration settings, so the public interface and all DAG attachments stay intact.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
