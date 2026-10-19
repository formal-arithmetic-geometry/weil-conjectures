## What changed

Filled both original proof bodies in `Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction`.
The ordinary theorem transports a sheaf-level reverse adjunction through the canonical
constant-coefficient realizations, obtains finite-colimit preservation from the left
adjunction, and uses the existing exact-functor and right-derived adjunction APIs. The
compact-support theorem identifies extension by zero for the identity with the identity
by uniqueness of left adjoints, descends the isomorphism termwise, proves that the prime
is a unit in each stalk over the finite-field base, and transports the first adjunction.
Existing signatures, definitions, and public imports are unchanged.
All three delivered modules compile cleanly through lcompile.py (2.1--3.6 seconds
per file), and deliver3.py --no-push passed with review class CODEX. The main
module axiom probe received no server response on that dry run; the tool records
that the merge reruns the probe. No compiler timeout was raised.

Added `FiniteEtaleProEtaleReverseAdjunction`: its proof transports the actual
localization-extension/restriction adjunction along a comparison isomorphism and the
published inverse-image/restriction isomorphism.
Added `FiniteEtaleProEtaleLocalizationComparison` for the genuinely geometric part of
the source argument: the finite coproduct/product comparison, compatible on overlaps.
Updated the parent DAG route and added nodes for these two separate source results.

## Proved and sorry left

Original holes closed (2 of 2):

- `AlgebraicGeometry.Scheme.finiteEtale_proEtale_exact_derived_adjunction`.
- `AlgebraicGeometry.Scheme.finiteEtale_proEtale_identityCompactification_adjunction`.

New theorem proved:
`AlgebraicGeometry.ProEtale.finiteEtale_reverseModuleAdjunction`
(node `lem-sf-finite-etale-proetale-reverse-adjunction`).

One hole added and remaining:
`AlgebraicGeometry.ProEtale.finiteEtale_localizationExtensionIso`
(node `lem-sf-finite-etale-proetale-localization-comparison`). Its proof is exactly
`by sorry`; its docstring and node contain the source and the local splitting,
biproduct, permutation, gluing, naturality, and inverse arguments.
The item module has zero remaining holes. This is a reduction with one geometric
result outstanding, not an axiom-free proof of the full import closure.
The new comparison does not restate either original theorem: it concerns ordinary
fixed-scalar sheaves only, and asserts no exactness, intrinsic coefficient transport,
derived computation, derived adjunction, or compact-support comparison.

## No longer needed

Removed these proof-only imports from the item module:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Mathlib.Algebra.Category.ModuleCat.Ulift`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Mathlib.CategoryTheory.Sites.Over`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.DerivedPullbackTensorHom`.
- `Sheaf.Paper.SfCommonStageDirectImage`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`.

The geometric dependencies are still needed by the new localization-comparison node:
`lem-weil-proetale-weakly-etale-localization`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-pbc-finite-etale-etale-local-split`,
`lem-pur-sheaf-hom-cover-gluing`, and their definitions. They are not globally pruned.
The outer proof no longer needs the large common-stage internal-Hom and direct-image
modules `Sheaf.Paper.DerivedPullbackTensorHom` and `Sheaf.Paper.SfCommonStageDirectImage`:
it works directly with the fixed intrinsic unbounded categories already in its statement.
The generic exact-functor node remains used through its Mathlib implementation.
No module is withdrawn. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The stated dependencies supply localization, local splitting,
slice adjunction and gluing, but none directly states the required comparison between
sheafified localization extension and direct image. That comparison is isolated as a
strictly smaller source result instead of being hidden inside the derived theorem.
The library's existing finite-etale reverse adjunction is for the small etale site;
it does not apply to arbitrary sheaves on the small pro-etale site.
The sum/product argument also works for an arbitrary commutative coefficient ring;
finiteness and prime invertibility are unnecessary for this underived comparison.
Edge cases checked: empty fibres give zero sums/products; varying local sheet counts
are allowed; disconnected bases require no global rank; zero coefficient rings cause
no change to the biproduct argument. The compactification proof asserts no global
unbounded compactification-independence theorem.

## New nodes

`lem-sf-finite-etale-proetale-localization-comparison` records the natural isomorphism
between sheafified left Kan extension along finite-etale localization and direct image.
It is the finite sum/product and overlap-gluing argument in the source's first two
proof paragraphs, with the actual functors and arbitrary coefficients made explicit.
Three Mathlib search kinds and a blueprint-wide duplicate search found no such result.

`lem-sf-finite-etale-proetale-reverse-adjunction` records the underived adjunction as
its own source result, and is proved by transporting the existing localization
adjunction along the preceding comparison and the canonical restriction comparison.
It adds no hole. No definition or statement repair was made, so no change record or
forced consumer adaptation is required.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
