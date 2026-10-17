/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# Extension by zero on the localizing closures of `Dctf`

For a finite coefficient ring `Λ` and a quasi-compact open immersion `j : U ⟶ X`, the extension
by zero `j_! : D(U_proét, Λ) ⥤ D(X_proét, Λ)` (applied levelwise, `j_!` being exact)

* maps `Dctf(U, Λ)` into `Dctf(X, Λ)`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek`):
  an object of `Dctf(U, Λ)` is `ν_U^* K'` for an étale `K' ∈ Dctf(U, Λ)`, and
  `j_! ν_U^* K' ≅ ν_X^* j_! K'` with `j_! K' ∈ Dctf(X, Λ)` (`lem-trf-open-ctf`);
* preserves coproducts, being a left adjoint;
* hence maps the localizing closure `Loc(Dctf(U, Λ))` into `Loc(Dctf(X, Λ))`
  (`AlgebraicGeometry.ProEtale.localizingClosure_constructibleFiniteTor_openImmersionLowerShriek`,
  blueprint `det-proper-image-localizing-open`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j] [QuasiCompact j]

/-- For a finite ring `Λ` and a quasi-compact open immersion `j : U ⟶ X`, the extension by zero
`j_!` maps `Dctf(U_proét, Λ)` into `Dctf(X_proét, Λ)`: an object of `Dctf(U, Λ)` is `ν_U^* K'`
for an étale `K' ∈ Dctf(U, Λ)` (`ν^*` detects Tor amplitude), and
`j_! ν_U^* K' ≅ ν_X^* j_! K'` with `j_! K' ∈ Dctf(X, Λ)` on the étale site
(`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`,
`lem-trf-open-ctf`). -/
theorem DerivedCategory.constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)).obj K) := by
  obtain ⟨⟨K', hK', ⟨e⟩⟩, a, b, hKt⟩ := hK
  have hK't : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b K' :=
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b).prop_of_iso e.symm hKt)
  obtain ⟨a', b', h⟩ :=
    (Etale.DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K').2
      ⟨hK', a, b, hK't⟩
  obtain ⟨⟨hbc, -⟩, ht⟩ :=
    Etale.constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ j a' b' h
  let E := (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} Λ) j).app K' ≪≫
      (D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)).mapIso e
  exact ⟨⟨_, hbc, ⟨E⟩⟩, a', b',
    (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a' b').prop_of_iso E
      ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a' b' _).2 ht)⟩

/-- The extension by zero `j_! : D(U_proét, Λ) ⥤ D(X_proét, Λ)` along an open immersion
preserves coproducts, being left adjoint to `j^*`. -/
lemma preservesColimitsOfShape_mapDerivedCategory_openImmersionLowerShriek (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      (D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)) :=
  (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
    j).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- Blueprint `det-proper-image-localizing-open`: Extension by zero on the localizing
categories.

For a finite coefficient ring `Λ` and a quasi-compact open immersion `j : U ⟶ X`, the extension
by zero `j_! : D(U_proét, Λ) ⥤ D(X_proét, Λ)` maps `Dctf(U, Λ)` into `Dctf(X, Λ)`, preserves
coproducts, and maps the localizing closure `Loc(Dctf(U, Λ))` into `Loc(Dctf(X, Λ))` (so that it
restricts to a triangulated, coproduct-preserving functor between them, the triangulated
structures and coproducts of the localizing closures being the ambient ones). The last part is
the principle `det-proper-image-localizing-principle`
(`CategoryTheory.ObjectProperty.localizingClosure_obj`), applied to the triangulated functor
`j_!`. This is the finite-coefficient case of the blueprint statement, for which `Dctf` is
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`. -/
theorem localizingClosure_constructibleFiniteTor_openImmersionLowerShriek :
    (∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)).obj K)) ∧
    (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      (D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j))) ∧
    (∀ K, (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U).localizingClosure.{u + 1}
        K →
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure.{u + 1}
        ((D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)).obj K)) := by
  have h₁ := fun K (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U K) ↦
    DerivedCategory.constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek Λ j hK
  have h₂ := preservesColimitsOfShape_mapDerivedCategory_openImmersionLowerShriek Λ j
  refine ⟨h₁, h₂, fun K hK ↦ ?_⟩
  exact ObjectProperty.localizingClosure_obj _ _
    (fun K hK ↦ ObjectProperty.le_localizingClosure _ _ (h₁ K hK)) hK

end AlgebraicGeometry.ProEtale
