/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison

/-!
# Base change of the Kummer coefficients

For a finite coefficient ring `Λ` of characteristic `n` which is free as a `ℤ/n`-module, the
natural map `Λ ⊗ Hᵠ(X, μₙ) ⟶ Hᵠ(X, μₙ ⊗ Λ)` is an isomorphism, compatibly with the Kummer
boundary maps (blueprint `lem-pur-kummer-coefficient-base-change`).

Over an algebraically closed field `μₙ ≅ ℤ/n`, and the comparison reduces to the additivity of
cohomology: `μₙ ⊗ Λ` is the constant sheaf on `Λ ⊗ ℤ/n ≅ (ℤ/n)ʳ`, through the unit
`ℤ/n ⟶ Λ ⊗ ℤ/n` (`AlgebraicGeometry.Etale.unit_comp_constantSheafCompExtendScalarsIso`).
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite TensorProduct




namespace CategoryTheory.Functor

variable (F : AddCommGrpCat.{v} ⥤ AddCommGrpCat.{w}) [F.Additive] {L : Type*} [AddCommGroup L]
  {Z V : AddCommGrpCat.{v}} (ψ : L →+ (Z ⟶ V))

/-- The map `L ⊗ F(Z) ⟶ F(V)`, `c ⊗ z ↦ F(ψ c) z`. -/
noncomputable def tensorMapOf : L ⊗[ℤ] F.obj Z →+ F.obj V :=
  TensorProduct.liftAddHom
    { toFun c := (F.map (ψ c)).hom
      map_zero' := by simp
      map_add' c c' := by simp }
    (fun m c z ↦ by
      change (F.map (ψ (m • c))).hom z = (F.map (ψ c)).hom (m • z)
      rw [_root_.map_zsmul, F.map_zsmul, _root_.map_zsmul]
      rfl)

@[simp]
lemma tensorMapOf_tmul (c : L) (z : F.obj Z) : F.tensorMapOf ψ (c ⊗ₜ z) = F.map (ψ c) z :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- If `ψ : L ≅ Hom(Z, V)` and `V` is a finite direct sum of copies of `Z`, whose endomorphisms
are integers, then `L ⊗ F(Z) ≅ F(V)` for every additive functor `F`. -/
theorem bijective_tensorMapOf (hψ : Function.Bijective ψ) {r : ℕ}
    (κ : V ≅ ⨁ fun _ : Fin r ↦ Z) (hZ : ∀ g : Z ⟶ Z, ∃ m : ℤ, g = m • 𝟙 Z) :
    Function.Bijective (F.tensorMapOf ψ) := by
  let π (i : Fin r) : V ⟶ Z := κ.hom ≫ biproduct.π (fun _ : Fin r ↦ Z) i
  let ι (i : Fin r) : Z ⟶ V := biproduct.ι (fun _ : Fin r ↦ Z) i ≫ κ.inv
  have hsum : ∑ i, π i ≫ ι i = 𝟙 V := by
    calc ∑ i, π i ≫ ι i = κ.hom ≫ (∑ i, biproduct.π (fun _ : Fin r ↦ Z) i ≫
          biproduct.ι (fun _ : Fin r ↦ Z) i) ≫ κ.inv := by
          rw [Preadditive.sum_comp, Preadditive.comp_sum]
          simp only [π, ι, Category.assoc]
      _ = 𝟙 V := by rw [biproduct.total, Category.id_comp, κ.hom_inv_id]
  obtain ⟨β, hβ⟩ : ∃ β : Fin r → L, ∀ i, ψ (β i) = ι i := ⟨fun i ↦ (hψ.2 (ι i)).choose,
    fun i ↦ (hψ.2 (ι i)).choose_spec⟩
  let G : F.obj V →+ L ⊗[ℤ] F.obj Z :=
    { toFun y := ∑ i, β i ⊗ₜ (F.map (π i) y)
      map_zero' := by simp
      map_add' a b := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib] }
  have hGΞ : ∀ x, G (F.tensorMapOf ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]
    | tmul c z =>
      rw [tensorMapOf_tmul]
      have hm (i : Fin r) : ∃ m : ℤ, ψ c ≫ π i = m • 𝟙 Z := hZ _
      choose m hm using hm
      have hc : c = ∑ i, m i • β i := by
        apply hψ.1
        rw [_root_.map_sum]
        simp only [_root_.map_zsmul, hβ]
        calc ψ c = ψ c ≫ ∑ i, π i ≫ ι i := by rw [hsum, Category.comp_id]
          _ = ∑ i, (ψ c ≫ π i) ≫ ι i := by
            rw [Preadditive.comp_sum]
            simp only [Category.assoc]
          _ = ∑ i, m i • ι i := by
            simp only [hm, Preadditive.zsmul_comp, Category.id_comp]
      change ∑ i, β i ⊗ₜ (F.map (π i) (F.map (ψ c) z)) = _
      conv_rhs => rw [hc, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hm, F.map_zsmul, F.map_id,
        TensorProduct.smul_tmul]
      rfl
  have hsumF : ∀ y : F.obj V, ∑ i, F.map (ι i) (F.map (π i) y) = y := by
    intro y
    have h := congrArg (fun φ : F.obj V ⟶ F.obj V ↦ φ y) (congrArg F.map hsum)
    simp only [F.map_sum, F.map_id] at h
    refine Eq.trans ?_ h
    classical
    simp only [← ConcreteCategory.comp_apply, ← F.map_comp]
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
        AddCommGrpCat.hom_add_apply]
  refine ⟨Function.LeftInverse.injective hGΞ, fun y ↦ ⟨G y, ?_⟩⟩
  change F.tensorMapOf ψ (∑ i, β i ⊗ₜ (F.map (π i) y)) = y
  rw [_root_.map_sum]
  simp only [tensorMapOf_tmul, hβ]
  exact hsumF y

end CategoryTheory.Functor



namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

set_option linter.flexible false in
/-- The unit of `constantSheaf ⊣ Γ(⊤, -)` on modules, made abelian, is the unit on abelian
groups, under `forget₂ ∘ constantSheaf ≅ constantSheaf ∘ forget₂`. -/
lemma forget₂_map_constantSheafAdj_unit_app (N : ModuleCat.{u + 1} Λ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal).unit.app
          N) ≫
      ((constantSheafSheafComposeForget₂Iso Λ).hom.app N).hom.app (op (⊤_ X.Etale)) =
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj N) := by
  simp [constantSheafAdj, constantPresheafAdj, constantSheafSheafComposeForget₂Iso]
  have : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂CoinduceAdj Λ)
  have h : Functor.whiskerRight (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N))
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
        (sheafifyComposeIso X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
          ((Functor.const X.Etaleᵒᵖ).obj N)).inv =
      toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    rw [← sheafComposeIso_hom_fac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 := congrArg (fun φ ↦ φ.app (op (⊤_ X.Etale))) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h2
  erw [Category.id_comp]
  exact h2

/-- **The unit of extension of scalars on constant sheaves.** Under
`Λ ⊗ M_X ≅ (Λ ⊗ M)_X` and `forget₂ ∘ constantSheaf ≅ constantSheaf ∘ forget₂`, the unit
`M_X ⟶ Λ ⊗ M_X` is the constant sheaf on the unit `M ⟶ Λ ⊗ M`. -/
lemma unit_comp_constantSheafCompExtendScalarsIso (M : AddCommGrpCat.{u + 1}) :
    (extendScalarsAdjunction Λ X).unit.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ≫
      (forget₂Sheaf Λ X).map ((constantSheafCompExtendScalarsIso Λ X).hom.app M) ≫
        (constantSheafSheafComposeForget₂Iso Λ).hom.app
          ((ModuleCat.extendScalarsAddCommGrp Λ).obj M) =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app M) := by
  let adjA := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  apply (adjA.homEquiv _ _).injective
  have hR : adjA.homEquiv M ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((ModuleCat.extendScalarsAddCommGrp Λ).obj M)))
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app M)) =
        (ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app M ≫ adjA.unit.app _ := by
    rw [Adjunction.homEquiv_unit]
    exact (adjA.unit.naturality _).symm
  have hU := Adjunction.unit_leftAdjointUniq_hom_app
    (adjA.comp (extendScalarsAdjunction Λ X))
    (((ModuleCat.extendScalarsAddCommGrpAdj Λ).comp (constantSheafAdj X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))) M
  erw [hR]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← Category.assoc]
  erw [hU]
  simp only [Adjunction.ofNatIsoRight, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.assoc]
  congr 1
  exact forget₂_map_constantSheafAdj_unit_app Λ X _

end AlgebraicGeometry.Etale
