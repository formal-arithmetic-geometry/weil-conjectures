# ContinuousConstructibleIntegralGluing proof scopes

## Reason

The stage-3 static scanner conservatively flags new `open`, `variable`, and namespace
commands as a possible interface change. The finite-filtration proof needs local category
names and parameters for its proved private helpers. This record documents that flag for
independent review. No definition, existing theorem signature, or visibility changes.

## Old

The original file-level name-resolution commands were:

```lean
universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
```

Its sole theorem was `continuousConstructible_integral_gluing`, with the signature in
the existing DAG attachment and the shared repository. That signature is unchanged verbatim.

## New

The file uses `open CategoryTheory Limits` and keeps the original namespace.
A balanced `section OpenPart` contains local parameters for the proved private counit helpers.
The original ℓ/E parameters and public theorem signature remain unchanged verbatim.
All additional helper declarations are private and proved; there is no new public interface.
The only added instance is the private, proved `essentiallySmallSelfInstance`, specializing
Mathlib's `CategoryTheory.essentiallySmallSelf.{0}` to a category in `Type (u + 1)` whose
hom universe is `u`. It supplies the canonical smallness proof without searching the unrelated
Noetherian-category instances imported by `ConstructibleSheaf.Devissage`. Its conclusion is a
proposition, and it changes no data or definition used by a target. The counit proof applies
`IsIso.mono_of_iso` explicitly and the cokernel proof applies `IsIso.epi_of_iso` explicitly;
no global or local attribute changes or compiler-limit changes are needed.

The return's eight duplicate helpers have been removed. Proof-only `import all` reuses
private constructibility lemmas from
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero` and private ordinary
module support lemmas from `Sheaf.Paper.CondensedOpenClosedRecollement`. A proof-only import
of `WeilConjectures.ConstructibleSheaf.Devissage` supplies the existing finite-open-chain,
adjunction-counit and cokernel-subobject declarations. The duplicate zero-constructibility
construction is also replaced by its existing private lemma. The original public import
is unchanged. No imported module is adapted, and no declaration visibility is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed in the shared claims | Direct importer; no adaptation: the theorem signature, definitions and public imports are unchanged. |

Other transitive users, including the targets, see the same declaration and definitions.
No target statement or definition used in a target has changed, so no statement review is
reopened. No module other than the claimed item is adapted in this delivery.

## Status

landed 20261016T052145-L-3987358 2026-10-16 (merge of deliver/C1/Sheaf.Paper.ContinuousConstructibleIntegralGluing)
