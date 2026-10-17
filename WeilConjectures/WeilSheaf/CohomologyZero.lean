/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.Finiteness

/-!
# Cohomology in degree zero of a Weil sheaf

For a morphism `φ : X ⟶ Y` of `k₀`-schemes and a Weil sheaf `F` on `X`, the invariance
`Γ(Ȳ, φ̄_* F) ≅ Γ(X̄, F)` of global sections under pushforward
(`AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso`) commutes with the Frobenius of the
global sections, the Weil structure of `φ_* F` being transported along `φ̄ ≫ Fr_Y⁻¹ = Fr_X⁻¹ ≫ φ̄`.
Applied to the structure morphism `a : X ⟶ Spec k₀`, together with `𝓗⁰(Ra_* F) ≅ a_* F`, this
identifies `H⁰(X ⊗ k̄, F)` with the global sections `Γ(X̄, F)`, Frobenius-equivariantly.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.globalSectionsLowerStarEquiv`: `Γ(Ȳ, φ_* F) ≅ Γ(X̄, F)` as
  Frobenius modules.
- `AlgebraicGeometry.WeilSheaf.cohomologyZeroEquiv`: `H⁰(X ⊗ k̄, F) ≅ Γ(X̄, F)` as Frobenius
  modules.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section LowerStar

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

/-- The underlying morphism of the Weil structure of `φ_* F`: the transport along
`φ̄ ≫ Fr_Y⁻¹ = Fr_X⁻¹ ≫ φ̄`, followed by the pushforward of the Weil structure of `F`. -/
lemma forget_map_lowerStar_obj_obj_str_hom (F : WeilSheaf k₀ l X) :
    (AdicSheaf.forget _).map ((lowerStar φ).obj F).obj.str.hom =
      (lowerStarComp _ (φ̄) (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).hom.app
          F.obj.carrier.X ≫
        (lowerStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ
          (comp_over φ (Spec (CommRingCat.of k₀))))).hom.app F.obj.carrier.X ≫
        (lowerStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
          (φ̄)).inv.app F.obj.carrier.X ≫
        (φ̄)_*[WeilCoefficients.{u} l].map ((AdicSheaf.forget _).map F.obj.str.hom) := by
  rw [lowerStar_obj_obj_str, Iso.trans_hom, Functor.mapIso_hom]
  unfold adicLowerStarGeometricFiberMapCompFrobeniusIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.forget_map, Mod.comp_hom',
    Iso.app_hom, adicLowerStarComp_hom_app_hom, adicLowerStarCongr_hom_app_hom,
    adicLowerStarComp_inv_app_hom, adicLowerStar_map_hom, Category.assoc]

/-- Let `g : Z ⟶ W` intertwine `F_Z : Z ⟶ Z` and `F_W : W ⟶ W`. For a morphism
`ψ : (F_Z)_* G ⟶ G`, the invariance `Γ(W, g_* G) ≅ Γ(Z, G)` of global sections under pushforward
intertwines `Γ(ψ)` with `Γ` of its transport `(F_W)_* g_* G ≅ g_* (F_Z)_* G ⟶ g_* G`. -/
lemma _root_.AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso_hom_comp_transport
    {Z W : Scheme.{u}} (g : Z ⟶ W) {FZ : Z ⟶ Z} {FW : W ⟶ W} (hc : g ≫ FW = FZ ≫ g)
    (G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (ψ : (FZ)_*[WeilCoefficients.{u} l].obj G ⟶ G) :
    (globalSectionsLowerStarIso _ FW).inv.app ((g)_*[WeilCoefficients.{u} l].obj G) ≫
      (Sheaf.Γ _ _).map ((lowerStarComp _ g FW).hom.app G ≫ (lowerStarCongr _ hc).hom.app G ≫
        (lowerStarComp _ FZ g).inv.app G ≫ (g)_*[WeilCoefficients.{u} l].map ψ) ≫
      (globalSectionsLowerStarIso _ g).hom.app G =
    (globalSectionsLowerStarIso _ g).hom.app G ≫ (globalSectionsLowerStarIso _ FZ).inv.app G ≫
      (Sheaf.Γ _ _).map ψ := by
  have c₁ := globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) g FW G
  have c₂ := globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) FZ g G
  have c₃ := globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) hc G
  have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).hom.naturality ψ
  simp only [Functor.comp_map] at n
  -- the prefix, before `ψ`
  have key : (globalSectionsLowerStarIso _ FW).inv.app ((g)_*[WeilCoefficients.{u} l].obj G) ≫
      (Sheaf.Γ _ _).map ((lowerStarComp (WeilCoefficients.{u} l) g FW).hom.app G) ≫
      (Sheaf.Γ _ _).map ((lowerStarCongr (WeilCoefficients.{u} l) hc).hom.app G) ≫
      (Sheaf.Γ _ _).map ((lowerStarComp (WeilCoefficients.{u} l) FZ g).inv.app G) ≫
      (globalSectionsLowerStarIso _ g).hom.app ((FZ)_*[WeilCoefficients.{u} l].obj G) =
      (globalSectionsLowerStarIso _ g).hom.app G ≫ (globalSectionsLowerStarIso _ FZ).inv.app G := by
    rw [← cancel_mono ((globalSectionsLowerStarIso _ FZ).hom.app G)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← c₂]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [Functor.map_comp_assoc, c₃, c₁, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [n, reassoc_of% key]

/-- The invariance `Γ(Ȳ, φ̄_* F) ≅ Γ(X̄, F)` of global sections under pushforward commutes with
the Frobenius of the global sections of the Weil sheaves `φ_* F` and `F`. -/
lemma globalSectionsLowerStarIso_hom_comp_frobenius (F : WeilSheaf k₀ l X) :
    (globalSectionsLowerStarIso _
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app
        ((lowerStar φ).obj F).obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map ((lowerStar φ).obj F).obj.str.hom) ≫
      (globalSectionsLowerStarIso _ (φ̄)).hom.app F.obj.carrier.X =
    (globalSectionsLowerStarIso _ (φ̄)).hom.app F.obj.carrier.X ≫
      (globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app F.obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map F.obj.str.hom) := by
  rw [forget_map_lowerStar_obj_obj_str_hom]
  exact globalSectionsLowerStarIso_hom_comp_transport (φ̄) _ F.obj.carrier.X
    ((AdicSheaf.forget _).map F.obj.str.hom)

/-- The invariance `Γ(Ȳ, φ̄_* F) ≅ Γ(X̄, F)` of global sections under the pushforward along the
base change `φ̄` of `φ`, as an isomorphism of Frobenius modules
(`AlgebraicGeometry.WeilSheaf.globalSectionsLowerStarIso_hom_comp_frobenius`). -/
noncomputable def globalSectionsLowerStarEquiv [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).globalSections.Equiv F.globalSections where
  toLinearEquiv := WeilCoefficients.linearEquivOfIso
    ((globalSectionsLowerStarIso _ (φ̄)).app F.obj.carrier.X)
  map_frobenius x := by
    have h := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom x)
      (globalSectionsLowerStarIso_hom_comp_frobenius φ F)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

end LowerStar

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology `H⁰(Y ⊗ k̄, G)` of a Weil sheaf is its space of global sections `Γ(Ȳ, G)`,
Frobenius-equivariantly: `H⁰ = Γ(Spec k̄, 𝓗⁰(Ra_* G)) ≅ Γ(Spec k̄, a_* G) ≅ Γ(Ȳ, G)`, by the left
exactness of `a_*` (`AlgebraicGeometry.WeilSheaf.homologySheafZeroDerivedLowerStarIso`) and the
invariance of global sections under pushforward
(`AlgebraicGeometry.WeilSheaf.globalSectionsLowerStarEquiv`).

Used for blueprint `p-real-sections` and `lem-a1-affine-hc2` (step 3: `H⁰(U, -) = Γ(Ū, -)`). -/
noncomputable def cohomologyZeroEquiv (G : WeilSheaf k₀ l Y) :
    (G.cohomology 0).Equiv G.globalSections :=
  (globalSectionsEquivOfIso
    (homologySheafZeroDerivedLowerStarIso (Y ↘ Spec (CommRingCat.of k₀)) G)).trans
    (globalSectionsLowerStarEquiv (Y ↘ Spec (CommRingCat.of k₀)) G)

end AlgebraicGeometry.WeilSheaf
