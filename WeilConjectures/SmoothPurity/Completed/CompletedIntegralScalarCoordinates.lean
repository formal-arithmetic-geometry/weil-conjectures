/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFrobeniusTrace
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree

/-! # Coordinates for the completed coefficient extension

Let `𝒪_E^∧ ⟶ 𝒪_L^∧` be the completed coefficient map, `Ord = 𝒪_L^∧ ⊗_{𝒪_E^∧} -` and `Res`
restriction of scalars, with the extension ⊣ restriction adjunction `Ord ⊣ Res`. For an
`𝒪_E`-basis `(bᵢ)` of `𝒪_L`, the maps `ιᵢ : M ⟶ Res (Ord M)`, `m ↦ bᵢ ⊗ m`, and coordinate maps
`πⱼ : Res (Ord M) ⟶ M` satisfy `πⱼ ∘ ιᵢ = δᵢⱼ` and `∑ⱼ ιⱼ ∘ πⱼ = 1`, i.e. they exhibit
`Res (Ord M)` as the direct sum of copies of `M`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The constant sections of `𝒪_L^∧` are compatible with restrictions. -/
theorem integralScalarConstant_map {V W : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ} (g : V ⟶ W)
    (x : Padic.coefficientExtensionIntegers l L) :
    (completedIntegralCommRingSheafUnrestricted l L Y).obj.map g
      (integralScalarConstant l L Y V x) = integralScalarConstant l L Y W x := by
  obtain ⟨-, -, κ, hκ, hκc, -⟩ := integralCompletedScalarMap_frobeniusSystem_trace l L L
    (AlgHom.id ℚ_[l] L) Y
  rw [← hκc, ← hκc]
  exact hκ g x

/-- Multiplication by the constant section of `x ∈ 𝒪_L` on `𝒪_L^∧`-module sheaves. -/
noncomputable def integralScalarSMul (x : Padic.coefficientExtensionIntegers l L) :
    𝟭 (integralTowerModules l L Y) ⟶ 𝟭 (integralTowerModules l L Y) :=
  SheafOfModules.smulSections (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (R := completedIntegralCommRingSheafUnrestricted l L Y)
    (fun V ↦ integralScalarConstant l L Y V x) (fun g ↦ integralScalarConstant_map l L Y g x)

set_option maxHeartbeats 1000000 in
set_option trace.profiler true in
-- The `erw` transport across `integralOrdinaryScalar = changeOfRingsFunctor` is slow.
/-- Coordinates for the completed coefficient extension: the extension ⊣ restriction
adjunction `Ord ⊣ Res`, an `𝒪_E`-basis `b` of `𝒪_L`, and coordinate maps `π j` with
`π j ∘ ι i = δ i j` and `∑ j, ι j ∘ π j = 1`, where `ι i = Res (b i •) ∘ unit`.
Source: Bhatt--Scholze, Lemma 6.8.2(1) (finite freeness of the completed coefficient
extension). -/
theorem integralOrdinaryScalar_coordinates :
    ∃ (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L)
      (a : integralOrdinaryScalar l E L ι Y ⊣ SheafOfModules.restrictScalars
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralCompletedScalarMap l E L ι Y)))
      (π : Fin d → (integralOrdinaryScalar l E L ι Y ⋙ SheafOfModules.restrictScalars
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralCompletedScalarMap l E L ι Y)) ⟶ 𝟭 (integralTowerModules l E Y))),
      (letI := (integralScalarIntegerInclusion l E L ι).toAlgebra
        ∃ b' : Module.Basis (Fin d) (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l L), ⇑b' = b) ∧
      (∀ i j (M : integralTowerModules l E Y),
        a.unit.app M ≫ (SheafOfModules.restrictScalars _).map
          ((integralScalarSMul l L Y (b i)).app _) ≫ (π j).app M =
            if i = j then 𝟙 M else 0) ∧
      ∀ M : integralTowerModules l E Y,
        ∑ j, (π j).app M ≫ a.unit.app M ≫ (SheafOfModules.restrictScalars _).map
          ((integralScalarSMul l L Y (b j)).app _) = 𝟙 _ := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  let := ι.toAlgebra
  let φ := integralCompletedScalarMap l E L ι Y
  obtain ⟨hobj, hmap, -⟩ := (integralOrdinaryScalarWitness l E L ι Y).choose_spec
  have hOC : integralOrdinaryScalar l E L ι Y = SheafOfModules.changeOfRingsFunctor φ :=
    CategoryTheory.Functor.ext hobj fun _ _ f ↦ hmap f
  obtain ⟨-, -, hO⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, ha⟩ := hO (integralOrdinaryScalar l E L ι Y) hobj hmap
  obtain ⟨d, Φ, κ, hκ, hκc, -, b, hb, hbasis, htrace, -⟩ :=
    integralCompletedScalarMap_frobeniusSystem_trace l E L ι Y
  obtain ⟨e⟩ := completedIntegralFiniteFree.{u, u} l E Y L ι φ
    (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec
  let εF := (Φ.adjunction e.symm).counit
  let σ (j : Fin d) := SheafOfModules.smulSections (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (R := completedIntegralCommRingSheafUnrestricted l L Y) (fun V ↦ (Φ.data V).dual j)
    (fun g ↦ Φ.dual_naturality j g)
  have hu (M : integralTowerModules l E Y) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (m : M.val.obj U) : (a.unit.app M).val.app U m = (eqToHom (hobj M).symm).val.app U
        ((SheafOfModules.toChangeOfRings (φ := φ) M).app U
          (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) 1 m)) := by
    have h := ha M _ (eqToHom (hobj M).symm) U m
    rw [eqToHom_trans, eqToHom_refl] at h
    erw [Adjunction.homEquiv_id] at h
    exact h
  have hcancel (M : integralTowerModules l E Y) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (y : (SheafOfModules.changeOfRings φ M).val.obj U) :
      (eqToHom (hobj M)).val.app U ((eqToHom (hobj M).symm).val.app U y) = y := by
    have h := eqToHom_trans (hobj M).symm (hobj M)
    rw [eqToHom_refl] at h
    exact congrArg (fun g ↦ g.val.app U y) h
  let R₀ := SheafOfModules.restrictScalars ((sheafCompose
    (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
  have hswap (τ : 𝟭 (integralTowerModules l L Y) ⟶ 𝟭 (integralTowerModules l L Y))
      {X X' : integralTowerModules l L Y} (h : X = X') :
      τ.app X ≫ eqToHom h = eqToHom h ≫ τ.app X' :=
    (τ.naturality (eqToHom h)).symm
  have hg (M : integralTowerModules l E Y) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (m : M.val.obj U) : (a.unit.app M ≫ R₀.map (eqToHom (hobj M))).val.app U m =
        (SheafOfModules.toChangeOfRings (φ := φ) M).app U
          (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) 1 m) :=
    (congrArg ((eqToHom (hobj M)).val.app U) (hu M U m)).trans (hcancel M U _)
  have hconj (τ : 𝟭 (integralTowerModules l L Y) ⟶ 𝟭 (integralTowerModules l L Y))
      {X X' : integralTowerModules l L Y} (h : X = X') :
      τ.app X = (eqToHom h ≫ τ.app X') ≫ eqToHom h.symm := by
    subst h
    simp
  refine ⟨d, b, a, fun j ↦ Functor.whiskerRight (Functor.whiskerLeft
    (integralOrdinaryScalar l E L ι Y) (σ j)) _ ≫ Functor.whiskerRight (eqToHom hOC) _ ≫ εF,
    hb, ?_, ?_⟩
  · intro i j M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_app]
    have key : R₀.map ((integralScalarSMul l L Y (b i)).app
          ((integralOrdinaryScalar l E L ι Y).obj M)) ≫
        R₀.map ((σ j).app ((integralOrdinaryScalar l E L ι Y).obj M)) ≫
          R₀.map (eqToHom (hobj M)) =
        R₀.map (eqToHom (hobj M)) ≫ R₀.map ((integralScalarSMul l L Y (b i)).app _) ≫
          R₀.map ((σ j).app _) := by
      simp only [← Functor.map_comp]
      rw [hswap, ← Category.assoc, hswap, Category.assoc]
      rfl
    rw [reassoc_of% key, ← Category.assoc]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    refine (Φ.unit_smul_smul_counitHom_val_app e.symm M _ (hg M)
      (fun V ↦ integralScalarConstant l L Y V (b i)) (fun g ↦ integralScalarConstant_map l L Y g _)
      (fun V ↦ (Φ.data V).dual j) (fun g ↦ Φ.dual_naturality j g) U m).trans ?_
    have htr : (Φ.data U).trace ((Φ.data U).dual j * (Φ.data U).basis i) =
        if i = j then 1 else 0 := by
      rw [mul_comm]
      exact htrace U i j
    rw [← hκc, ← hbasis]
    erw [htr]
    split_ifs
    · exact one_smul _ m
    · exact zero_smul _ m
  · intro M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_app,
      Category.assoc]
    have hsmb (j : Fin d) : integralScalarSMul l L Y (b j) = SheafOfModules.smulSections
        (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
        (R := completedIntegralCommRingSheafUnrestricted l L Y) (fun V ↦ (Φ.data V).basis j)
        (fun g ↦ Φ.basis_naturality j g) := by
      have hfam : (fun V ↦ integralScalarConstant l L Y V (b j)) =
          fun V ↦ (Φ.data V).basis j := by
        funext V
        rw [← hκc, ← hbasis]
      unfold integralScalarSMul
      congr 1
    have hterm (j : Fin d) : R₀.map ((σ j).app ((integralOrdinaryScalar l E L ι Y).obj M)) ≫
        R₀.map (eqToHom (hobj M)) ≫ εF.app M ≫ a.unit.app M ≫
          R₀.map ((integralScalarSMul l L Y (b j)).app ((integralOrdinaryScalar l E L ι Y).obj M)) =
        R₀.map (eqToHom (hobj M)) ≫ (R₀.map ((σ j).app _) ≫ Φ.counitHom e.symm M ≫
          (a.unit.app M ≫ R₀.map (eqToHom (hobj M))) ≫
            R₀.map ((integralScalarSMul l L Y (b j)).app _)) ≫
          R₀.map (eqToHom (hobj M).symm) := by
      have h2 := hconj (integralScalarSMul l L Y (b j)) (hobj M)
      have h1 : R₀.map ((σ j).app ((integralOrdinaryScalar l E L ι Y).obj M)) ≫
          R₀.map (eqToHom (hobj M)) = R₀.map (eqToHom (hobj M)) ≫
            R₀.map ((σ j).app _) := by
        rw [← R₀.map_comp, ← R₀.map_comp, hswap]
        rfl
      erw [reassoc_of% h1, h2]
      rw [R₀.map_comp, R₀.map_comp]
      simp only [Category.assoc]
      rfl
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Preadditive.comp_sum, ← Preadditive.sum_comp]
    simp only [hsmb]
    rw [Φ.sum_smul_counitHom_unit_smul e.symm M _ (hg M)]
    erw [Category.id_comp]
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
    rfl

end WeilConjectures
