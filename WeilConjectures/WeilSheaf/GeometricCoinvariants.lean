/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkPairing
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Purity of the geometric coinvariants

Let `F` be a lisse Weil sheaf on a `k₀`-scheme `X` locally of finite type, punctually `ι`-pure of
weight `w`. Its geometric coinvariants `Γ(X̄, F^∨)^∨`
(`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) are `ι`-pure of weight `w`
(`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`).

Let `β` be an eigenvalue of the Frobenius on the global sections `Γ(X̄, G)` of a Weil sheaf `G`,
with eigenvector `a`. The morphism of sheaves `ℚ̄_ℓ ⟶ G` sending `1` to `a`
(`AlgebraicGeometry.ProEtale.bijective_globalSectionOfModHom`) is a morphism of Weil sheaves
`u : ℚ̄_ℓ(β) ⟶ G` out of the constant Weil twist of `ℚ̄_ℓ` by `β`
(`AlgebraicGeometry.WeilSheaf.homOfGlobalSection`). Its image is nonzero, so it has a nonzero
stalk at some closed point `x`, a quotient of the stalk of `ℚ̄_ℓ(β)`, on which the local
Frobenius acts by `β^{deg x}`. Hence `β^{deg x}` is an eigenvalue of the local Frobenius of `G`
at `x` (`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections`).

For `G = F^∨`, whose stalks are the duals of those of `F`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_dual`), this shows that every eigenvalue of
the Frobenius on `Γ(X̄, F^∨)` has weight `-w`, so that its dual has weight `w`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section GlobalSections

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The Frobenius of the global sections of a Weil sheaf: the inverse of
`Γ(X̄, Fr^* G) ≅ Γ(X̄, G)` followed by the global sections of the Weil structure. -/
lemma globalSections_frobenius_apply (G : WeilSheaf k₀ l X) (a : G.globalSections.carrier) :
    G.globalSections.frobenius a = ((Sheaf.Γ _ _).map G.obj.str.hom.hom).hom
      (((globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app
          G.obj.carrier.X).hom a) :=
  rfl

end GlobalSections

/-- The Weil structure of the constant Weil sheaf `ℚ̄_ℓ` fixes the global section `1`. -/
lemma adicConstant_globalSections_str_one :
    ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.hom.hom).hom
      (((globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app
          (adicConstant k₀ l X).obj.carrier.X).hom
        (oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) =
      oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber := by
  have hε := NatTrans.IsMonoidal.unit (τ := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).hom)
  have key : ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫
      (Sheaf.Γ _ _).map (MonObj.one (X := adicConstantSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ≫
      (globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app _ ≫
      (Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.hom.hom =
      ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫
        (Sheaf.Γ _ _).map (MonObj.one (X := adicConstantSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) := by
    have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.naturality
        (MonObj.one (X := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    have hε' : ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app (𝟙_ _) =
        ε (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_] ⋙
          Sheaf.Γ _ (WeilCoefficients.{u} l)) := by
      rw [← hε, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    erw [reassoc_of% n, reassoc_of% hε']
    rw [Functor.LaxMonoidal.comp_ε, Category.assoc]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp]
    have hu := adicConstant_unit_str (k₀ := k₀) (l := l) (X := X)
    rw [Category.assoc] at *
    exact congrArg (fun m ↦ ε (Sheaf.Γ _ (WeilCoefficients.{u} l)) ≫ (Sheaf.Γ _ _).map m) hu
  exact congrArg (fun m ↦ m.hom (1 : ULift.{u + 1} (PadicAlgCl l))) key

section Hom

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The morphism of sheaves of modules `ℚ̄_ℓ ⟶ G` sending `1` to a global section `a` of a Weil
sheaf `G`. -/
noncomputable def modHomOfGlobalSection (G : WeilSheaf k₀ l X) (a : G.globalSections.carrier) :
    AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶ G.obj.carrier :=
  Function.surjInv (bijective_globalSectionOfModHom G.obj.carrier).2 a

lemma globalSectionOfModHom_modHomOfGlobalSection (G : WeilSheaf k₀ l X)
    (a : G.globalSections.carrier) :
    globalSectionOfModHom (modHomOfGlobalSection G a) = a :=
  Function.surjInv_eq _ a

/-- The morphism `ℚ̄_ℓ ⟶ G` of a Frobenius eigenvector `a` with eigenvalue `β` intertwines the
Weil structure of `G` with the Weil structure of `ℚ̄_ℓ` twisted by `β`. -/
theorem modHomOfGlobalSection_comm (G : WeilSheaf k₀ l X) (β : (PadicAlgCl l)ˣ)
    (a : G.globalSections.carrier) (ha : G.globalSections.frobenius a = (β : PadicAlgCl l) • a) :
    (frobeniusPullback k₀ l X).map (modHomOfGlobalSection G a) ≫ G.obj.str.hom =
      ((adicConstant k₀ l X).constantTwist β).obj.str.hom ≫ modHomOfGlobalSection G a := by
  set v := modHomOfGlobalSection G a with hv_def
  have hv : ((Sheaf.Γ _ _).map v.hom).hom
      (oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) = a := by
    rw [← globalSectionOfModHom_eq]
    exact globalSectionOfModHom_modHomOfGlobalSection G a
  let gs := globalSectionsLowerStarIso (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
  let one := oneGlobalSection (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have e₁ : ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.inv.hom).hom one =
      (gs.inv.app _).hom one := by
    have h := congrArg ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.inv.hom).hom
      (adicConstant_globalSections_str_one (k₀ := k₀) (l := l) (X := X))
    rw [← h, ← ModuleCat.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', Iso.hom_inv_id,
      Mod.id_hom', CategoryTheory.Functor.map_id]
    rfl
  have e₂ : G.globalSections.frobenius a = ((Sheaf.Γ _ _).map G.obj.str.hom.hom).hom
      (((Sheaf.Γ _ _).map ((frobeniusPullback k₀ l X).map v).hom).hom
        (gs.inv.app _ |>.hom one)) := by
    rw [globalSections_frobenius_apply, ← hv,
      ← ModuleCat.comp_apply (f := (Sheaf.Γ _ _).map v.hom)]
    erw [gs.inv.naturality v.hom]
    rfl
  rw [← cancel_epi (adicConstant k₀ l X).obj.str.inv]
  refine (bijective_globalSectionOfModHom G.obj.carrier).1 ?_
  rw [globalSectionOfModHom_eq, globalSectionOfModHom_eq]
  have e₃ (y) : ((Sheaf.Γ _ _).map
      ((adicConstant k₀ l X).constantTwist β).obj.str.hom.hom).hom y =
      (ULift.up (β : PadicAlgCl l) : ULift.{u + 1} (PadicAlgCl l)) •
        ((Sheaf.Γ _ _).map (adicConstant k₀ l X).obj.str.hom.hom).hom y := by
    have hs : ((adicConstant k₀ l X).constantTwist β).obj.str.hom.hom =
        (adicConstant k₀ l X).obj.str.hom.hom ≫
          ((ULift.up (β : PadicAlgCl l) : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _) := by
      simp only [constantTwist, Endofunctor.IsoAlgebra.mk_str, Iso.trans_hom, Mod.comp_hom',
        WeilCoefficients.smulIso, AdicSheaf.smul_hom]
    rw [hs, Functor.map_comp, Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  simp only [Mod.comp_hom', Functor.map_comp, ModuleCat.comp_apply]
  erw [e₁, ← e₂, e₃]
  erw [adicConstant_globalSections_str_one (k₀ := k₀) (l := l) (X := X)]
  rw [map_smul]
  erw [hv, ha]
  rfl

end Hom

end AlgebraicGeometry.WeilSheaf
