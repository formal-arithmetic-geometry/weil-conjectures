## What changed

Filled the proofs of exactness and conservativity of coefficient restriction, the unique
sectionwise direct-image comparison, the ordinary inverse-image comparison and its
invertibility, and the final derived adjunction compatibility theorem. Existing public
statements and definitions are unchanged. The proof uses the canonical module unit
comparison and the proved derived-adjunction API of WeilConjectures. Private helpers
supply the termwise mate calculation and translate its homotopy-category normalization
to the specified complex-level units. The DAG records this route. Change record:
`coord/changes/A4-proetale-ring-sheaf-local-proof-control.md`. The complete module compiled cleanly through `lcompile.py`
in 47.6 seconds before this repair, and again after the repair. The duplicate helper was removed
after maintainer review identified the existing library theorem with the same statement; its
homology argument is now inlined locally in the target proof, so no duplicate declaration is
exported. The delivery dry run verifies the final cleanup.

## Proved and sorry left

Closed five of the original six holes:

- `AlgebraicGeometry.Scheme.proEtaleRingRestrictScalars_properties`.
- `AlgebraicGeometry.Scheme.proEtaleRingRestrictionDirectImage_existsUnique`.
- `AlgebraicGeometry.Scheme.proEtaleRingRestrictionPullbackApp_properties`.
- `AlgebraicGeometry.Scheme.proEtaleRingRestrictionPullbackInv_isIso`.
- `AlgebraicGeometry.Scheme.proEtaleRingSheafChangeAdjunction`.

One original hole remains, unchanged:
`AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedDirectImage_existsUnique`
(node `lem-weil-pbc-ring-sheaf-change-adjunction`). No holes or split-off modules were added.
Its remaining argument is to show that the derived mate is invertible: on an SU-K-injective
I, apply the ringed-topos composition theorem to coefficient restriction and geometric
direct image to obtain acyclicity of the RU-restriction. The private
`derived_mate_factors` already supplies the required normalization; the right-derived
universal property supplies uniqueness. The final theorem is proved from the existing
normalized-comparison existence declaration, as intended by stage 3.

## No longer needed

The fraction-formula step has been replaced by formal mate normalization. Removed the
proof dependency and maintainer tool-use approval for
`lem-pc-pre-derived-adjoint-functors-general` and its import
`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`. The dependency
`lem-weil-pbc-kinjective-hom-derived` is also unnecessary for this compatibility proof.
The general existence theorem `lem-weil-pbc-exact-functor-derived-functor` and its
import `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` are also unnecessary: the
proved `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`
API supplies the exact-functor unit and postcomposition universal property directly.
These removals are below the blueprint unit; its proper-base-change route is retained.

Removed the unused constant-coefficient import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`; this argument uses
Mathlib's restriction for an actual sheaf of rings and the generic underlying-sheaf API.
Removed redundant direct imports `Sheaf.CategoryTheory.RingedSiteModules`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`, and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`, and
`Mathlib.CategoryTheory.Localization.Predicate`; their APIs remain available through
imports that the proof uses. No new modules are introduced and no modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated the library's private `reflectsDerivedIsomorphisms`
statement word for word. Because that existing declaration is private and cannot be
referenced by its source name, this repair inlines the same homology criterion as two
local proof blocks; no public signature changes. No false statement or definition was
found. The DAG's pre-derived fraction computation was more elaborate than needed: the
canonical derived adjunction's mate normalization and the right-derived universal
property imply the compatibility directly. Restriction is never assumed to preserve
K-injectivity.

The static gate requires the change record for new local proof commands. They export no
attributes or instances; all downstream users retain the identical public interface.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
