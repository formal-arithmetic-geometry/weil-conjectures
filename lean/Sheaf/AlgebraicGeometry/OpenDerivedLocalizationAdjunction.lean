/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization

/-! # Derived localizations and the adjunction for open restriction

Source: Stacks Project, Tag 079W, Lemma cohomology-lemma-adjoint.
(blueprint: lem-pc-open-derived-localization-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transport derived localizations to an open subscheme and its opens, and derive the
right adjoint of localized open restriction. No support or detector assertion is made.
Source: Stacks Project, Tag 079W, Lemma cohomology-lemma-adjoint, used for the open
inclusion in Tag 0A9A, Lemma perfect-lemma-supported-generator.
(blueprint: lem-pc-open-derived-localization-adjunction).

Proof: Form the standard derived category on the open scheme U. The exact canonical
module equivalence `Modules.overEquiv U` induces a derived equivalence with the given
localization on the localized site over U. This transports local w-smallness to the
standard derived category on U. `hasLocalizationOfLocallySmall` shrinks its Hom types,
giving hD in universe w. Apply `nonempty_derivedOpenLocalization` to U with this hD
for the family hO on all its opens; that theorem uses exact extension by zero and
restriction to establish the necessary smallness. The localized restriction functor
has its explicit underived right adjoint. The localized module category is
Grothendieck abelian by `grothendieckAbelian_and_functorial_kInjective_resolutions`,
so it has K-injective resolutions. The upstream
`mapDerivedCategoryRightDerivedAdjunction` derives the right adjoint of exact
restriction and supplies the displayed adjunction. This right adjoint is determined
up to natural isomorphism. Empty and full opens use the same construction. -/
theorem open_derived_localizations_and_adjunction
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) :
    ∃ hD : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
    letI := hD
    ∃ hO : ∀ W : U.toScheme.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W)),
    letI := hO
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X),
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R) := by
  obtain ⟨hD⟩ := nonempty_hasDerivedCategory_openSubscheme.{u, w} X U
  let := hD
  obtain ⟨hO⟩ := nonempty_derivedOpenLocalization.{u, w} U.toScheme
  let := hO
  exact ⟨hD, hO, open_derived_localization_adjunction X U⟩

end AlgebraicGeometry
