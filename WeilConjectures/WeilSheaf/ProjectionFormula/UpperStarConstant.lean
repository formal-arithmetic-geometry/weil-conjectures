/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarTensorWeil
public import WeilConjectures.WeilSheaf.StalkConstantSheaf

/-!
# The pullback of the constant sheaf, compatibly with the exchange isomorphisms

For a morphism `j : T₁ ⟶ T₂` intertwining automorphisms `a` and `b`, the canonical morphism
`j^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is compatible with the structure morphisms `(a⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` and
`(b⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` transported along the exchange isomorphism
(`AlgebraicGeometry.ProEtale.upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom`): both
sides are the canonical morphism along `a ≫ j = j ≫ b`, by the cocycle condition for the
canonical morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T₁ T₂ : Scheme.{u}}

/-- The canonical morphism `j^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is compatible with the structure isomorphisms
`(a⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` and `(b⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` transported along the exchange isomorphism. -/
lemma upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom (j : T₁ ⟶ T₂)
    (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom) :
    (a.inv)_*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l j) ≫
        (adicConstantSheafLowerStarIso l a.symm).hom =
      (upperStarExchange l j a b c).hom.app (adicConstantSheaf l T₂) ≫
        (j)^*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l b.symm).hom ≫
        upperStarAdicConstantSheafHom l j := by
  have ha : (adicConstantSheafLowerStarIso l a.symm).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app (adicConstantSheaf l T₁) ≫
        upperStarAdicConstantSheafHom l a.hom := by
    rw [← upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom l a,
      Iso.inv_hom_id_app_assoc]
  have hb := upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom l b
  have n := (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.naturality
    (upperStarAdicConstantSheafHom l j)
  have hc₁ : (a.hom)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l j) ≫
      upperStarAdicConstantSheafHom l a.hom =
        (upperStarComp _ a.hom j).inv.app (adicConstantSheaf l T₂) ≫
          upperStarAdicConstantSheafHom l (a.hom ≫ j) := by
    rw [← upperStarAdicConstantSheafHom_comp l a.hom j, Iso.inv_hom_id_app_assoc]
  have hc₂ := upperStarAdicConstantSheafHom_comp l j b.hom
  have hcg := upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom (l := l) c
  rw [ha, reassoc_of% n, hc₁, upperStarExchange_hom_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hb, hc₂, hcg]

/-- `AlgebraicGeometry.ProEtale.upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom` for
an isomorphism `e` equal to the exchange isomorphism, kept abstract to avoid unfolding it. -/
lemma upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom_of_eq (j : T₁ ⟶ T₂)
    (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (e : (j)^*[WeilCoefficients.{u} l] ⋙ (a.inv)_*[WeilCoefficients.{u} l] ≅
      (b.inv)_*[WeilCoefficients.{u} l] ⋙ (j)^*[WeilCoefficients.{u} l])
    (he : e = upperStarExchange l j a b c) :
    (a.inv)_*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l j) ≫
        (adicConstantSheafLowerStarIso l a.symm).hom =
      e.hom.app (adicConstantSheaf l T₂) ≫
        (j)^*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l b.symm).hom ≫
        upperStarAdicConstantSheafHom l j := by
  subst he
  exact upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom j a b c

/-- The isomorphism `g^* ℚ̄_ℓ ≅ ℚ̄_ℓ` of modules is the canonical morphism on underlying sheaves. -/
lemma adicUpperStarUnitIso_hom_hom {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (adicUpperStarUnitIso l g).hom.hom = upperStarAdicConstantSheafHom l g :=
  rfl

variable (l) in
/-- The constant sheaf `ℚ̄_ℓ` with the structure isomorphism `(a⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ`. For `a` the
geometric Frobenius, this is the constant pro-étale Weil sheaf
`AlgebraicGeometry.ProEtaleWeilSheaf.adicConstant`. -/
noncomputable def isoAlgebraUnit {T : Scheme.{u}} (a : T ≅ T) : IsoAlgebra (a.inv)_*ᵃ[l] :=
  IsoAlgebra.mk (AdicSheaf.unit l T) (adicLowerStarUnitIso l a.symm)

/-- The canonical isomorphism `j^* ℚ̄_ℓ ≅ ℚ̄_ℓ` is compatible with the structure isomorphisms
of the constant sheaves transported along an isomorphism `e` equal to the exchange
isomorphism. -/
lemma adicUpperStarUnitIso_isoAlgebraUnit_comm (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) :
    (a.inv)_*ᵃ[l].map (adicUpperStarUnitIso l j).hom ≫ (isoAlgebraUnit l a).obj.str =
      ((IsoAlgebra.mapOfNatIso e).obj (isoAlgebraUnit l b)).obj.str ≫
        (adicUpperStarUnitIso l j).hom := by
  obtain ⟨e', he', h₁⟩ : ∃ e' : (j)^*[WeilCoefficients.{u} l] ⋙ (a.inv)_*[WeilCoefficients.{u} l] ≅
      (b.inv)_*[WeilCoefficients.{u} l] ⋙ (j)^*[WeilCoefficients.{u} l],
      e' = upperStarExchange l j a b c ∧ ∀ M, (e.hom.app M).hom = e'.hom.app M.X :=
    ⟨_, rfl, fun M ↦ by
      subst he
      exact adicUpperStarExchange_hom_app_hom j a b c M⟩
  rw [mapOfNatIso_obj_obj_str]
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicUpperStar_map_hom, Category.assoc]
  rw [h₁, adicUpperStarUnitIso_hom_hom]
  exact upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom_of_eq j a b c e' he'

variable (l) in
/-- The pullback of the constant sheaf with structure isomorphism is the constant sheaf with
structure isomorphism. -/
noncomputable def mapOfNatIsoIsoAlgebraUnitIso (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) :
    (IsoAlgebra.mapOfNatIso e).obj (isoAlgebraUnit l b) ≅ isoAlgebraUnit l a :=
  IsoAlgebra.isoMk (adicUpperStarUnitIso l j)
    (adicUpperStarUnitIso_isoAlgebraUnit_comm j a b c e he)

/-- `AlgebraicGeometry.ProEtale.mapOfNatIsoIsoAlgebraUnitIso` for objects equal to the constant
sheaves with structure isomorphisms. -/
theorem nonempty_mapOfNatIso_obj_iso_of_eq (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (K : IsoAlgebra (b.inv)_*ᵃ[l])
    (hK : K = isoAlgebraUnit l b) (K' : IsoAlgebra (a.inv)_*ᵃ[l]) (hK' : K' = isoAlgebraUnit l a) :
    Nonempty ((IsoAlgebra.mapOfNatIso e).obj K ≅ K') := by
  subst hK hK'
  exact ⟨mapOfNatIsoIsoAlgebraUnitIso l j a b c e he⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "𝐒" => Spec (CommRingCat.of k₀)

set_option hygiene false in
local notation "Fr[" T "]" => Scheme.Hom.geometricGaloisFrobenius (T ↘ Spec (CommRingCat.of k₀))

set_option hygiene false in
local notation "bc[" f "]" =>
  Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "EX[" φ "]" => adicUpperStarExchange l (bc[φ]) (Fr[X]) (Fr[Y])
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ 𝐒)).symm

/-- The constant pro-étale Weil sheaf is the constant sheaf with structure isomorphism along
the geometric Frobenius. -/
lemma adicConstant_eq_isoAlgebraUnit (T : Scheme.{u}) [T.Over 𝐒] :
    adicConstant k₀ l T = isoAlgebraUnit l (Fr[T]) :=
  rfl

/-- **The pullback of the constant pro-étale Weil sheaf is the constant pro-étale Weil sheaf**:
`φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ`, through the canonical isomorphism of the underlying sheaves. -/
theorem nonempty_upperStar_obj_adicConstant_iso (φ : X ⟶ Y) [φ.IsOver 𝐒] :
    Nonempty ((upperStar k₀ l φ).obj (adicConstant k₀ l Y) ≅ adicConstant k₀ l X) := by
  rw [upperStar_eq_mapOfNatIso]
  exact nonempty_mapOfNatIso_obj_iso_of_eq (l := l) (bc[φ]) (Fr[X]) (Fr[Y])
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ 𝐒)).symm
    (EX[φ]) rfl _ (adicConstant_eq_isoAlgebraUnit Y) _ (adicConstant_eq_isoAlgebraUnit X)

end AlgebraicGeometry.ProEtaleWeilSheaf
