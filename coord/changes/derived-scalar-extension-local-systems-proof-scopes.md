# derivedScalarExtension_localSystems proof scopes

## Reason

The delivery adds private proof helpers under namespace and variable commands, two local elaboration/linter options, and the TwoSquare notation scope. The static interface checker records these commands as a change to what importers see. This record documents that change. All existing public declaration signatures and public imports are byte-identical; there is no definition or statement repair. Every new definition and lemma is private. The helper variable commands occur in namespaces that close before the existing theorem is declared. No existing exported instance, attribute, notation or definition changes.

## Old

The original nondeclaration command interface, verbatim from `leanindex.interface`:

```lean
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
```

## New

The delivered nondeclaration command interface, verbatim from `leanindex.interface`:

```lean
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.TwoSquare
open scoped CategoryTheory.TwoSquare
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) {B B' : Type (u + 1)} [CommRing B] [CommRing B'] (φ : B →+* B')
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) {B B' : Type (u + 1)} [CommRing B] [CommRing B'] (φ : B →+* B')
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) {B B' : Type (u + 1)} [CommRing B] [CommRing B'] (φ : B →+* B')
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D] (J : GrothendieckTopology C) (F : C ⥤ D) (K : GrothendieckTopology D) [F.IsContinuous J K] {R S : Type (u + 1)} [CommRing R] [CommRing S]
omit [EssentiallySmall.{u + 1} C] in
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
open scoped CategoryTheory.Functor
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (U : X.ProEt)
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
open scoped CategoryTheory.Functor
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (U : X.Etale)
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems --uses derivedScalarExtension_localSystems` lists the direct theorem user and the item itself. All four downstream modules are recorded below as well. Their theorem and definition signatures are unaffected, and no consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | B7 | Its original theorem now has a complete proof; public signature unchanged. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | No declaration or public import change; no adaptation. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | No declaration or public import change; no adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | No declaration or public import change; no adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | No declaration or public import change; no adaptation. |

## Status

landed 20261020T131934-L-1392123 2026-10-20 (merge of deliver/B7/Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems)
