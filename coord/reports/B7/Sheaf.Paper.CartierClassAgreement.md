## What changed

Repaired `agreementCartierEtale` to reuse the existing canonical
`cartierRelativeCoefficientBoundary` at the actual positive coefficient level. Its
full relative Kummer normalization identifies it with the published etale Cartier
family. `agreementCartierMap`, all existing declaration signatures, and all targets
are unchanged. Added the public import of `CartierRelativeBoundaryRealization`, which
the new definition body uses. Its already proved last equality supplies the agreement
clause. The pullback clause is transported from normalized etale families by the
existing supported site-comparison pullback law.

The genuinely separate remaining result is naturality of arbitrary normalized etale
divisor families. It is stated in `Sheaf.Paper.NormalizedDivisorFamilyPullback` with
its own node and complete proof in words. It quantifies arbitrary normalized families,
requires neither separatedness nor finite type, and concerns only the etale class;
it contains neither the Cartier-map agreement nor the pro-etale comparison conclusion.
The main theorem combines that result with the existing relative-boundary agreement.

Change record: `coord/changes/B7-cartier-class-agreement-proof-context.md`.
No adopted source-library module or consumer is edited.

## Proved and sorry left

The original one hole is `WeilConjectures.PurityFiniteSetting.cartier_class_agreement`
(node `lem-pur-cartier-class-agreement`). Its proof is complete in the item module.
One hole is added in the public theorem
`WeilConjectures.PurityFiniteSetting.normalizedDivisorFamily_pullback`
(node `lem-pur-normalized-divisor-family-pullback`). The result is a decomposition:
one original hole closed, one separate hole added, one split off, zero net reduction.
The item has zero `sorry` tokens; the new module has exactly one named theorem hole.
No definition contains `sorry`. Existing imported dependency holes are not claimed
as closed. The item module compiled in 39.4 seconds (request
`ff812302588137352680cf07`); the statement module previously compiled in 33.1 seconds.
The exact packet is rechecked by delivery.

A complete proof of the new family theorem was written and compiled in the scratch
probe in 49.3 seconds (`cd082f3f290d65a7fb554044`), but its final-module rebuilds
exceeded the 60-second gate. The attempted full proof and its mathematical route were
checked during the session; its remaining implementation issue is repeated kernel
conversion between the selected supported-Hom localization and the canonical etale Ext
localization. No limit was raised. The public statement retains the entire separate
naturality conclusion and the full source argument for the next worker.

## No longer needed

Removed private proof imports:

- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `Sheaf.AlgebraicGeometry.PurityRelativeCone`
- `Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.SupportedHomPullback`
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`

The first equality reuses `lem-pur-cartier-relative-boundary-realization`; it does not
reconstruct its cone, scalar, and roots comparisons here.
`lem-pur-supported-root-scalar-site-comparison`, `lem-pur-supported-hom-pullback`,
and `lem-pur-supported-hom` are not direct proof inputs. The normalized-family lemma
retains the boundary pullback, constant-exchange normalization and supported-cup APIs.
No module is withdrawn. All original public imports remain.

Removed obsolete `tool_uses` entries: `lem-sc-line-bundle-torsor`,
`lem-amb-relative-torsor-cohomology`, `lem-amb-kummer-any-base`,
`lem-pur-divisor-relative-cone`, `lem-weil-pbc-derived-module-underlying-comparison`,
`lemma-weil-pbc-finite-direct-image-exact`, `lem-pc-bounded-above-flat-kflat-site`,
`lem-pur-supported-hom-pullback`, and `lem-pur-supported-hom`. These constructions
are encapsulated by the existing relative-boundary realization.

## Where the brief, the DAG or earlier work was wrong

The live item source is restored despite its historical quarantine row. No current
B7 return requests its withdrawal. Both definition attachments are retained.
The original proof plan repeats comparisons already established by the relative-boundary
realization; its last equality proves the agreement directly for the existing canonical
scalar adjunct. This keeps the unit route and its realized statements unchanged.

A full direct proof was written and kernel checked in diagnostic runs, but repeated
conversions between canonical etale Ext and selected supported Hom made files exceed
the 60-second gate. Local cached instances, generic derived formulas, explicit casts,
and heterogeneous transport were tried. The successful route is the distinct naturality result for arbitrary normalized
families, with its own source argument. Generalizing from concrete chosen families avoids part of the repeated conversion
through the choice predicate. The final full proof does not pass the timing gate;
the first clause is proved by an existing complete theorem and site comparison is
proved in Lean here. Etale naturality remains the named independent result.

Searches: LeanFinder for normalized Cartier pullback found only scheme-normalization
results; Loogle found generic HEq and cast lemmas; Mathlib grep found no boundary
pullback result. Project search found `supported_kummer_boundary_pullback` and the
already proved `cartier_relative_boundary_realization`.

Edge cases: the normalized-family lemma allows empty schemes and divisors; the full
relative boundary retains the complementary trivialization and sign. Both immersions
are required Cartier. No flatness, smoothness, ramification-divisibility, separatedness,
or finite-type hypothesis is added to that lemma.

## New nodes

`lem-pur-normalized-divisor-family-pullback`, module
`Sheaf.Paper.NormalizedDivisorFamilyPullback`: etale supported-Hom naturality of any
two fully normalized divisor families. Its proof in words applies the existing
normalized boundary pullback, identifies the source exchange by the constant quotient,
and transports the Ext equation via the explicit derived pullback formula. One named hole.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
