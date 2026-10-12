/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

/-!
# Sections of the sheaf of differentials over affine opens

Let `g : X ⟶ Spec R` be a morphism of schemes and `U` an affine open of `X`. Then the sections
`Γ(Ω¹_{X/R}, U)` of the sheaf of relative differentials are the Kähler differentials
`Ω[Γ(X, U)⁄R]`, compatibly with `d` and `D`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Hom.specStructureMap`: the structure map `R ⟶ Γ(X, U)`.
- `AlgebraicGeometry.Scheme.Hom.exists_linearEquiv_kaehlerDifferential`: for `U` affine,
  `Ω[Γ(X, U)⁄R] ≃ Γ(Ω¹_{X/R}, U)`, sending `D b` to `d b`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R)

/-- The structure map `R ⟶ Γ(X, U)` of a scheme `X` over `Spec R`. -/
noncomputable def specStructureMap (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ U le_top

lemma specStructureMap_map {U V : X.Opens} (h : V ≤ U) :
    g.specStructureMap U ≫ X.presheaf.map (homOfLE h).op = g.specStructureMap V := by
  simp [specStructureMap]

/-- The universal derivation `d : 𝒪_X → Ω¹_{X/R}` on sections over `U`. -/
noncomputable def sectionsD (U : X.Opens) : Γ(X, U) →+ Γ(g.relativeDifferentials, U) :=
  g.relativeDifferentialsDerivation.d (X := op U)

lemma sectionsD_mul (U : X.Opens) (a b : Γ(X, U)) :
    g.sectionsD U (a * b) = a • g.sectionsD U b + b • g.sectionsD U a :=
  g.relativeDifferentialsDerivation.d_mul a b

lemma sectionsD_map {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    g.sectionsD V (X.presheaf.map (homOfLE h).op a) =
      g.relativeDifferentials.presheaf.map (homOfLE h).op (g.sectionsD U a) :=
  g.relativeDifferentialsDerivation.d_map _ a

lemma sectionsD_specStructureMap (U : X.Opens) (r : R) :
    g.sectionsD U (g.specStructureMap U r) = 0 := by
  have h := PresheafOfModules.Derivation'.d_app_app g.relativeDifferentialsDerivation ⊤
    ((Scheme.ΓSpecIso R).inv r)
  have h' := g.sectionsD_map (le_top : U ≤ g ⁻¹ᵁ ⊤) (g.app ⊤ ((Scheme.ΓSpecIso R).inv r))
  have e : g.specStructureMap U r =
      X.presheaf.map (homOfLE (le_top : U ≤ g ⁻¹ᵁ ⊤)).op (g.app ⊤ ((Scheme.ΓSpecIso R).inv r)) := by
    simp [specStructureMap, Scheme.Hom.appLE]
  rw [e, h']
  exact (congrArg (g.relativeDifferentials.presheaf.map _) h).trans (map_zero _)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R) {U : X.Opens}
  (hU : IsAffineOpen U)

include hU in
lemma _root_.AlgebraicGeometry.IsAffineOpen.image_fromSpec_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [image_top_eq_opensRange, hU.opensRange_fromSpec]

lemma fromSpec_comp_eq_specMap : hU.fromSpec ≫ g = Spec.map (g.specStructureMap U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top (Spec R)) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, specStructureMap, Spec.map_comp]

/-- The map `Γ(Ω¹_{X/R}, U) → Ω[Γ(X, U)⁄R]` for an affine open `U`, through the sections of
`Ω¹_{Spec Γ(X, U) / Spec R}`. -/
noncomputable def sectionsToKaehler (m : Γ(g.relativeDifferentials, U)) :
    CommRingCat.KaehlerDifferential (g.specStructureMap U) :=
  (relativeDifferentialsSpecΓIso (g.specStructureMap U)).hom.hom
    (((g.relativeDifferentialsRestrictIso hU.fromSpec).hom ≫
      (relativeDifferentialsCongr _ (g.fromSpec_comp_eq_specMap hU)).hom).app ⊤
      (g.relativeDifferentials.presheaf.map (homOfLE hU.image_fromSpec_top.le).op m))

end AlgebraicGeometry.Scheme.Hom
