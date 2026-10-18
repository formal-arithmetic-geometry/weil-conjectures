## What changed

Proved every existing theorem hole in `Sheaf.CategoryTheory.ScalarLocalization`.
The pure-tensor composition formula follows from the unique extension's specification.
Tensor induction proves associativity, identities and the extended functor laws;
tensor relations prove localization linearity. Mathlib's inverse-additive and
inverse-linear equivalence instances make the strict inverse extend, and proved
private helpers transport functor composition, identities and equality.

Removed the unused public import
`Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`. No existing declaration
signature, definition or instance body changes. The change record is
`coord/changes/scalar-localization-unused-coefficient-import.md`.
Updated the definition node's previously empty proof plan to describe the Lean proof.
No new modules or nodes are introduced.

The completed module compiled cleanly through lcompile.py. Its sole direct consumer,
`Sheaf.CategoryTheory.ScalarLocalizationTriangulated`, also compiled unchanged against
the sandbox version (7.5 seconds and 3.1 seconds respectively). The consumer copy was
used only for checking and is not delivered.

## Proved and sorry left

Closed six of six holes, all attached to
`def-weil-linear-scalar-localization`:

- `CategoryTheory.ScalarLocalization.composition_tmul`
- `CategoryTheory.ScalarLocalization.composition_laws`
- `CategoryTheory.ScalarLocalization.localization_laws`
- `CategoryTheory.ScalarLocalization.localization_linear`
- `CategoryTheory.ScalarLocalization.map_laws`
- `CategoryTheory.ScalarLocalization.map_automorphism`

Zero holes remain in the delivered module; zero holes added or split off.
The existing dependency `CategoryTheory.exists_linear_scalarLocalization_category`
(`lem-weil-linear-scalar-localization-category`) is still used for its unique bilinear
extension. Its existing proof obligation is not claimed to be closed here.
The three private functor-extension helpers are fully proved.

## No longer needed

Removed import: `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`.
The general category and its functors do not use the identification of a localized
coefficient-integer ring with its coefficient field. The following library modules
leave this item's transitive import closure (this is not a claim that no other target
path reaches them):

- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrCore`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrFactorization`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian`

Their attached nodes are:

- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-l-adic-extension-integers-dvr-core`
- `lem-weil-l-adic-extension-integers-dvr-factorization`
- `lem-weil-l-adic-extension-integers-dvr-factorization-unique`
- `lem-weil-l-adic-integers-localization-uniformizer`

The p-adic specialization in the node's mathematical statement is retained; the
coefficient-field theorem is not needed to construct the general R-linear category.
No unit statement or proof step is bypassed. The unique-bilinear-extension dependency
is retained. No other imports were added or removed.

## Where the brief, the DAG or earlier work was wrong

The general tensor-Hom construction imported a coefficient-field specialization that
neither its statements nor its definitions or proofs use. The node had no proof
steps despite the six supporting theorem holes; its proof metadata now records the
implemented calculations. No mathematical statement was false or changed.

Searches run through msearch.py: LeanFinder for extension of scalars of a linear
category returned module-category scalar extension rather than this construction;
Loogle found `LinearMap.baseChange_tmul`; grep found the base-change formula and
functor-extensionality API. Local source searches found Mathlib's
`Equivalence.inverse_additive` and `Equivalence.inverseLinear`, avoiding any new
inverse-linearity obligation. The current blueprint's rationalization definition was
read at `main-20261015/blueprint/sec-proetale-coefficients/sk-def-sf-operations/`.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
