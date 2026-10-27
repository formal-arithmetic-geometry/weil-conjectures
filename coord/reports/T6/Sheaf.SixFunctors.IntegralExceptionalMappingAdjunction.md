## What changed

Replaced the proof of `WeilConjectures.IntegralExceptionalMapping.exists_unique`
with the construction from the specified total mapping-complex isomorphism.
All existing public signatures and definition bodies are unchanged. The proof
constructs domain membership, actual reconstruction isomorphisms, natural lambda
isomorphisms, total mapping isomorphisms, and the resulting Hom equivalences.
Naturality is proved using coherence of gamma and the recorded H-zero RHom
identifications. Mathlib constructs the adjunction from those natural bijections;
its Hom formula is exactly `homMap`. Values on identities prove uniqueness.
The node now records that argument instead of having an empty proof plan.

The new `IntegralExceptionalLimitConstructible` module uses the existing
coefficient-independent intrinsic exceptional bounds to prove right preservation.
The new `IntegralSupportRealizationComparison` module proves the ambient
compact-support comparison by transferring it from the existing geometric
realization. Uniqueness of adjoints compares the reductions, open extensions
and proper images as whole functors. The main proof cancels the fully faithful
constructible inclusion to obtain the comparison of restricted functors.

Validation: the current three-file packet compiles cleanly in import order
through `lcompile.py --all`, with zero errors or warnings. Existing public
definitions and the target theorem signature were checked verbatim, and both
new node signatures were checked against their Lean declarations.

## Proved and sorry left

Original module: one hole, `WeilConjectures.IntegralExceptionalMapping.exists_unique`.
Its replacement is a complete Lean proof from existing declarations and two
new proved lemmas; no sorry remains in the item module or the added modules.

New proved declarations:
`WeilConjectures.IntegralExceptionalMapping.exceptional_limit_constructible`
(node `lem-coef-integral-exceptional-limit-constructible`) and
`WeilConjectures.IntegralExceptionalMapping.support_realization_comparison`
(node `lem-coef-integral-support-realization-comparison`).

One original hole is closed and zero holes are added. The new definitions are
explicit composites of existing maps and equivalences; none chooses an arbitrary
unproved existence witness. The geometric realization is eliminated only inside
a theorem proof, and the conclusion is a proposition asserting a natural
isomorphism, without selecting new operation data.

## No longer needed

The direct proof imports `IntegralResidueTor`, `IntegralDualExceptionalSystem`,
`NormalizedDVREffectivity`, `RhomGlobalSectionsOfUniverses`,
`RingedStrictTowerHomotopyLimitIndependentCoefficients`, and `FiniteExceptional`
were removed. Residue Tor is already used by the imported, proved reduction-domain lemma; actual reconstruction and the
proved mapping-system calculus supply all reconstruction maps. The arbitrary
realization needs no auxiliary absolute dualizing operations: the existing uniform
intrinsic exceptional bounds supply preservation directly. The redundant direct `ConstructibleIntervalsUnordered` import in the new
preservation module was also removed; the bounds interface already exposes it.
The corresponding old direct dependencies are
`lem-coef-integral-residue-tor`, `lem-coef-integral-dual-exceptional-system`,
`lem-coef-normalized-dvr-effectivity`, `lem-pur-rhom-global-sections`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and `lem-coef-finite-exceptional`.
They are not direct proof dependencies of this item anymore. Some remain
transitive dependencies of the established interfaces, so this delivery claims
no global module pruning. No unit or parent statement is bypassed. No existing
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item's accepted definition node has empty `proof` and `proof_deps`; there are
no numbered steps to translate. The existing theorem docstring supplied the route.
The latest compact-support sketch omits the historical detailed paragraphs, as
already recorded in the node's source and review. The delivery records the proof
it actually implements without changing the unit, targets or theorem statement.

The docstring suggests applying `IntegralSupport` and the integral dual-exceptional
comparison, but the theorem quantifies over an arbitrary `r` and supplies neither
`IntegralSupport r` nor the absolute dualizing-operation data needed by that
comparison. The proved support comparison supplies that geometric
identification by uniqueness of adjoints; the existing uniform intrinsic bounds
avoid the extra duality data.
Finite evaluations are never used to infer equality of derived system maps.

The exceptional interval is enlarged with min/max endpoints to include the zero
object and empty schemes without assuming the uniform shift constants are ordered.
The constructions work at the first positive coefficient level and with identity
morphisms; no extra finite-Tor or common-system-bound hypothesis is introduced.

## New nodes

`lem-coef-integral-exceptional-limit-constructible` owns the proved objectwise
preservation lemma. Its proof uses the existing uniform finite exceptional bounds,
actual normalized reconstruction, actual evaluated counits, and transport of
constructibility and cohomological support. Its statement is strictly smaller
than existence of the specified integral mapping adjunction.

`lem-coef-integral-support-realization-comparison` owns the proved geometric
comparison of the literal ambient compact-support composite with the recorded
functor. It contains no adjunction or exceptional-preservation assertion. The
proof transfers the existing IntegralSupport comparison along uniqueness of
adjoints on whole systems before total limit; it does not infer maps or
equalities from finite evaluations. Mathlib semantic, type and source
searches were run and recorded, and repository searches found no arbitrary-r
comparison already stated. Both new nodes retain the item's unit and blueprint
ancestry. There is no statement/definition change record because all existing
signatures and non-proof bodies remain unchanged.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
