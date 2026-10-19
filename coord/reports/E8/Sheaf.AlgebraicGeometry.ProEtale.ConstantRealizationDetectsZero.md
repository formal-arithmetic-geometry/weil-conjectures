## What changed

Proved `AlgebraicGeometry.ProEtale.constantRealization_detects_zero` in
`Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero`.
The canonical unit definition and the theorem signature are unchanged.
The proof identifies the underlying additive sheafification unit, obtains a covering
equalizer sieve, uses joint surjectivity at a point of the nonempty object to choose a
covering member, and uses identity constant-presheaf restrictions to conclude injectivity.
The two zero-detection implications follow from subsingleton modules and evaluation of
the restricted module sheaf at `U → U`.
Updated the existing node's proof and dependencies to describe this Lean proof.
The repaired proof compiles with zero holes; the final clean compile and delivery probe
check all declarations.
LeanFinder, Loogle and grep searches found the generic Mathlib local-injectivity unit
instance; there is no need for an additional intermediate statement.
The integral-models unit statement and proof route are preserved.

Repair of returned delivery `5e239ad9f`: removed the unnecessary file-level
`set_option warn.sorry false`. The landing source scanner matched the `sorry`
component of that option name at line 21 as an unattributed hole. Removing the
option resolves the reported attribution failure and enables ordinary warnings;
it changes no declaration, definition or mathematical statement. The retained
proof compiled before the repair, and the repaired file is compiled again below.
The change record `coord/changes/E8-constant-realization-warning-option.md`
records the option removal and the complete downstream consumer inventory.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.ProEtale.constantRealization_detects_zero`
(node `lem-sfb-constant-realization-detects-zero`).
Added zero holes; no `sorry` remains in the delivered Lean module.
No split-offs and no definition changes.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.SiteConstantModuleUnit`.
Also removed the unused retained-attempt import
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections`.
Added `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` for the existing
covering-sieve and precoverage characterizations.
The node `lem-sf-constant-module-unit-locally-bijective` is no longer a proof dependency
of this item, and its obsolete top-level `tool_uses` approval is removed.
Its equal-universe wrapper is replaced directly by Mathlib's additive sheafification
unit local-injectivity instance, whose universes fit the original statement.
The same argument is retained; no unit-level step is bypassed.
No other existing imports or nodes were removed. Existing public imports are retained.
This item no longer requires `Sheaf.CategoryTheory.SiteConstantModuleFunctor`, which
was reached through the removed proof-only import; other callers may still require it.

## Where the brief, the DAG or earlier work was wrong

The planned `siteConstantModuleUnitSections_locallyBijective` declaration assumes a
small category with equal object and morphism universes. The assigned module uses
`X.ProEt` with object universe `u + 1` and morphism universe `u`, so this specialized
wrapper does not fit. Its underlying Mathlib result does fit and is used directly.
No mathematical statement was changed. The nonempty hypothesis is essential: the
empty object admits an empty cover. The argument also handles the zero module and
zero ring, and an empty base has no nonempty site object, so causes no extra case.

The retained attempt did not compile: constant restriction maps needed an explicit
`change`, and zero detection needed to transfer subsingletonness through the proved
injective unit. Both proof gaps are repaired without changing declarations.

The returned delivery's proof did compile, but its warning-suppression option was
mistaken for an unattributed hole by the landing scanner. This repair removes that
option rather than changing or bypassing the tool.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
