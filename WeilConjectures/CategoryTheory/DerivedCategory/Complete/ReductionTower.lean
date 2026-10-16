/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.NormalizedTower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.AdicTower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.NormalizedTower
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ConstructibleReduction

/-!
# Reduction towers and normalized towers

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`, and put `P_n = R ⧸ Iⁿ`. This file compares the tower of reductions
`n ↦ K ⊗ᴸ R/Iⁿ` of an object `K ∈ D(J, R)` (`DerivedCategory.derivedCompletionDiagram`) with the
normalized towers `M_n ∈ D(J, P_n)` of `CategoryTheory.Sheaf.NormalizedTower` (the adic towers
of blueprint `def-weil-pbc-adic-coefficient-datum`):

* `CategoryTheory.Sheaf.NormalizedTower.ofIsDerivedBaseChange`: derived base changes
  `K ⟶ Res M_n` of a fixed object form a normalized tower;
* `DerivedCategory.exists_normalizedTower_restrict_iso`: the reductions of every `K` are the
  restrictions of scalars `Res M_n` of the levels of a normalized tower (the derived base
  changes `K ⊗ᴸ_R P_n`, computed by a K-flat model of `K`);
* `CategoryTheory.Sheaf.NormalizedTower.exists_derivedComplete_iso`: conversely every normalized
  tower is the reduction tower of a derived complete object, its derived limit (effectivity);
* `DerivedCategory.derivedComplete_and_iso_of_isHomotopyLimit`: the derived limit of the
  reductions of `K` (its derived completion) is derived complete and has the same reductions as
  `K`.

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace CategoryTheory.Sheaf.NormalizedTower

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R] {I : Ideal R}

/-- The transition map `K_{n+1} ⟶ Res K_n` between two derived base changes `K ⟶ Res K_n` of
the same object: the map adjoint to `K ⟶ Res K_n`. -/
lemma exists_transition_of_isDerivedBaseChange
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (Kn : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R ⧸ I ^ n))))
    (η : ∀ n : ℕ, K ⟶ (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).obj (Kn n))
    (hη : ∀ n : ℕ, IsDerivedBaseChange (η n)) (n : ℕ) :
    ∃ t : Kn (n + 1) ⟶
        (derivedRestrictScalars J (Ideal.Quotient.factorPowSucc I n)).obj (Kn n),
      η (n + 1) ≫ (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ (n + 1)))).map t =
        η n ≫ (derivedRestrictScalarsCompIso J (Ideal.Quotient.factor_comp_mk
          (Ideal.pow_le_pow_right n.le_succ)).symm).inv.app (Kn n) :=
  (hη (n + 1) _).2 _

/-- Derived base changes `η_n : K ⟶ Res K_n` of a fixed object `K` along `R ⟶ R ⧸ Iⁿ` form a
normalized tower: the transition maps `K_{n+1} ⟶ Res K_n` are the maps adjoint to the `η_n`,
and they exhibit `K_n` as the derived base change `K_{n+1} ⊗ᴸ R ⧸ Iⁿ`. -/
noncomputable def ofIsDerivedBaseChange {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (Kn : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R ⧸ I ^ n))))
    (η : ∀ n : ℕ, K ⟶ (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).obj (Kn n))
    (hη : ∀ n : ℕ, IsDerivedBaseChange (η n)) : NormalizedTower J I where
  obj := Kn
  map n := (exists_transition_of_isDerivedBaseChange Kn η hη n).choose
  isDerivedBaseChange n N := by
    have hspec := (exists_transition_of_isDerivedBaseChange Kn η hη n).choose_spec
    set t := (exists_transition_of_isDerivedBaseChange Kn η hη n).choose
    let e := (derivedRestrictScalarsCompIso J (Ideal.Quotient.factor_comp_mk
      (Ideal.pow_le_pow_right (I := I) n.le_succ)).symm).app N
    rw [← Function.Bijective.of_comp_iff' (hη (n + 1)
      ((derivedRestrictScalars J (Ideal.Quotient.factorPowSucc I n)).obj N))]
    have h : ((fun g' ↦ η (n + 1) ≫
          (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ (n + 1)))).map g') ∘
        fun g ↦ t ≫ (derivedRestrictScalars J (Ideal.Quotient.factorPowSucc I n)).map g) =
        (fun h ↦ h ≫ e.inv) ∘
          fun g ↦ η n ≫ (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).map g := by
      funext g
      have hnat := (derivedRestrictScalarsCompIso J (Ideal.Quotient.factor_comp_mk
        (Ideal.pow_le_pow_right (I := I) n.le_succ)).symm).inv.naturality g
      simp only [Functor.comp_obj, Functor.comp_map] at hnat
      simp only [Function.comp_apply, Functor.map_comp, ← Category.assoc, hspec]
      simp only [Category.assoc, e, Iso.app_inv, hnat]
    rw [h]
    refine Function.Bijective.comp ?_ (hη n N)
    exact Function.bijective_iff_has_inverse.2 ⟨fun h ↦ h ≫ e.hom, fun h ↦ by simp,
      fun h ↦ by simp⟩

@[simp]
lemma ofIsDerivedBaseChange_obj {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (Kn : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R ⧸ I ^ n))))
    (η : ∀ n : ℕ, K ⟶ (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).obj (Kn n))
    (hη : ∀ n : ℕ, IsDerivedBaseChange (η n)) :
    (ofIsDerivedBaseChange Kn η hη).obj = Kn :=
  rfl

end CategoryTheory.Sheaf.NormalizedTower

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) (J : GrothendieckTopology C) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) (J : GrothendieckTopology C) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) (J : GrothendieckTopology C) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) (J : GrothendieckTopology C) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high) (J : GrothendieckTopology C)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high) (J : GrothendieckTopology C)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

local instance (J : GrothendieckTopology C) : IsIso (sheafTensorStructure J R).ε :=
  (sheafTensorStructure J R).isIso_ε

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hI in
lemma ker_mk_pow_eq_span (n : ℕ) :
    RingHom.ker (Ideal.Quotient.mk (I ^ n)) = Ideal.span {ϖ ^ n} := by
  rw [Ideal.mk_ker, hI, Ideal.span_singleton_pow]

section Reduction

variable (J) in
/-- The reduction `F ↦ F / ϖⁿ F` of sheaves of `R`-modules to sheaves of `R ⧸ Iⁿ`-modules, as a
reduction datum for the restriction of scalars along `R ⟶ R ⧸ Iⁿ`. -/
noncomputable abbrev quotPowReductionDatum (n : ℕ) :
    Functor.ReductionDatum (Sheaf.restrictScalars J (Ideal.Quotient.mk (I ^ n)))
      (Sheaf.smulNatTrans J (ϖ ^ n)) :=
  Sheaf.reductionDatum J (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective (ϖ ^ n)
    (ker_mk_pow_eq_span hI n)

/-- The reduction map `Q P ⟶ Res Q(P / ϖⁿ P)` of a complex `P`. -/
noncomputable abbrev quotPowReductionMap (n : ℕ)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) :
    Q.obj P ⟶ (Sheaf.derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).obj
      (Q.obj (((quotPowReductionDatum J hI n).Φ.mapHomologicalComplex (.up ℤ)).obj P)) :=
  Q.map ((quotPowReductionDatum J hI n).complexMap P) ≫
    (Sheaf.restrictScalars J (Ideal.Quotient.mk (I ^ n))).mapDerivedCategoryFactors.inv.app _

/-- The reduction of a K-flat complex is its derived base change along `R ⟶ R ⧸ Iⁿ`. -/
lemma isDerivedBaseChange_quotPowReductionMap (n : ℕ)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) (hP : P.IsKFlat) :
    Sheaf.IsDerivedBaseChange (quotPowReductionMap hI n P) := by
  have := Sheaf.restrictScalars_full J (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective
  exact fun N ↦ (quotPowReductionDatum J hI n).bijective_comp_map P hP N

include hϖ in
/-- Multiplication by `ϖⁿ` on a flat sheaf is a monomorphism. -/
lemma mono_smul_of_flat {F : Sheaf J (ModuleCat.{u + 1} R)} (hF : ObjectProperty.flat F)
    (n : ℕ) : Mono (ϖ ^ n • 𝟙 F) := by
  have h := Sheaf.exact_smul_of_flat J hF 0 (ϖ ^ n) (zero_mul _) (fun b ↦ by
    simp only [zero_mul, Set.mem_range, exists_const]
    constructor
    · intro hb
      exact ((mul_cancel_left_mem_nonZeroDivisors (pow_mem hϖ n)).1
        (hb.trans (mul_zero _).symm)).symm
    · rintro rfl
      exact mul_zero _)
  exact h.mono_g (by simp)

include hϖ in
/-- For a complex `P` of flat sheaves, `0 ⟶ P --ϖⁿ--> P ⟶ P / ϖⁿ P ⟶ 0` is short exact. -/
lemma shortExact_quotPowReduction (n : ℕ)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ)
    (hP : ∀ i, ObjectProperty.flat (P.X i)) :
    (ShortComplex.mk (ϖ ^ n • 𝟙 P) ((quotPowReductionDatum J hI n).complexMap P) (by
      ext i : 1
      exact (quotPowReductionDatum J hI n).σ_comp_r (P.X i))).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  have := mono_smul_of_flat hϖ (hP i) n
  have := (quotPowReductionDatum J hI n).epi_r (P.X i)
  exact { exact := (quotPowReductionDatum J hI n).exact (P.X i)
          mono_f := by dsimp; infer_instance
          epi_g := by dsimp; infer_instance }

include hϖ in
/-- For a complex `P` of flat sheaves, the restriction of scalars of `P / ϖⁿ P` is the reduction
`Q P ⊗ᴸ R/Iⁿ`: both are cones of the multiplication by `ϖⁿ` on `Q P`. -/
lemma nonempty_iso_restrict_quotPowReduction (n : ℕ)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ)
    (hP : ∀ i, ObjectProperty.flat (P.X i)) :
    Nonempty ((Sheaf.derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).obj
        (Q.obj (((quotPowReductionDatum J hI n).Φ.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (derivedCompletionDiagram J I (Q.obj P)).obj (op n)) := by
  have hS := shortExact_quotPowReduction hϖ hI n P hP
  let T₁ := triangleOfSES hS
  let T₂ := tensorQuotPowTriangle hϖ hI (Q.obj P) n
  have hT₁ : T₁.mor₁ = ϖ ^ n • 𝟙 T₁.obj₁ := by
    change Q.map (ϖ ^ n • 𝟙 P) = _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  let v : T₁.obj₁ ≅ T₂.obj₁ := unitIso (Q.obj P)
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
    (triangleOfSES_distinguished hS) (tensorQuotPowTriangle_distinguished hϖ hI _ n)
    (Arrow.isoMk v v (by
      change v.hom ≫ T₂.mor₁ = T₁.mor₁ ≫ v.hom
      rw [hT₁, tensorQuotPowTriangle_mor₁, Linear.comp_smul, Linear.smul_comp, comp_id,
        id_comp]))
  exact ⟨(Sheaf.restrictScalars J (Ideal.Quotient.mk (I ^ n))).mapDerivedCategoryFactors.app _ ≪≫
    Triangle.π₃.mapIso e⟩

end Reduction

include hϖ in
/-- **The reduction tower of an object is the restriction of a normalized tower.** For every
`K ∈ D(J, R)` there is a normalized tower `M` (the derived base changes `K ⊗ᴸ_R R ⧸ Iⁿ`) whose
levels `Res M_n` are the reductions `K ⊗ᴸ R/Iⁿ`. -/
theorem exists_normalizedTower_restrict_iso (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ∃ M : Sheaf.NormalizedTower J I, ∀ n : ℕ,
      Nonempty (M.restrict.obj (op n) ≅ (derivedCompletionDiagram J I K).obj (op n)) := by
  obtain ⟨M⟩ := KFlatModel.nonempty K
  refine ⟨Sheaf.NormalizedTower.ofIsDerivedBaseChange
    (fun n ↦ Q.obj (((quotPowReductionDatum J hI n).Φ.mapHomologicalComplex (.up ℤ)).obj M.P))
    (fun n ↦ M.iso.inv ≫ quotPowReductionMap hI n M.P)
    (fun n ↦ (isDerivedBaseChange_quotPowReductionMap hI n M.P M.isKFlat).of_iso M.iso.symm),
    fun n ↦ ?_⟩
  obtain ⟨e⟩ := nonempty_iso_restrict_quotPowReduction hϖ hI n M.P M.flat
  exact ⟨e ≪≫ whiskerRightIso M.iso ((quotPowFunctor J I).obj (op n))⟩


section Completion

include hϖ hI in
/-- For a homotopy limit `c` of the reductions `L ⊗ᴸ R/Iⁿ` of `L`, there is a map `φ : L ⟶ c.pt`
which becomes an isomorphism after `- ⊗ᴸ R/I`: the tower `L ⊗ᴸ R/Iⁿ ⊗ᴸ R/I` is pro-isomorphic
to the constant tower `L ⊗ᴸ R/I`
(`DerivedCategory.exists_lift_whiskerRight_derivedCompletionCone`), and `- ⊗ᴸ R/I` commutes with
countable products. This is the argument of `DerivedCategory.derivedComplete_of_rightOrthogonal`.
-/
lemma exists_isIso_whiskerRight_quot_of_isHomotopyLimit
    (L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    {c : Cone (derivedCompletionDiagram J I L)} (hc : IsHomotopyLimit c) :
    ∃ φ : L ⟶ c.pt, IsIso (φ ▷ (quotPowFunctor J I).obj (op 1)) := by
  let G := derivedCompletionDiagram J I L
  let c' := derivedCompletionCone J I L
  obtain ⟨P, hP, ε, hT⟩ := hc
  -- the Milnor triangle of the constant tower `L`
  let c₀ : Cone ((Functor.const ℕᵒᵖ).obj L) := { pt := L, π := 𝟙 _ }
  have : ∀ n, IsIso (c₀.π.app n) := fun n ↦ by dsimp [c₀]; infer_instance
  obtain ⟨PK, hPK, δK, hTK⟩ := IsHomotopyLimit.of_isIso_π c₀
  let m := productTowerMap (PF := PK) hP c'.π
  obtain ⟨φ, hφ₁, hφ₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hTK hT m m
    (productTowerMap_comp_sub_towerShift hPK hP c'.π).symm
  replace hφ₁ : Fan.IsLimit.lift hPK (fun n ↦ c₀.π.app (op n)) ≫ m =
      φ ≫ Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) := hφ₁
  replace hφ₃ : δK ≫ φ⟦(1 : ℤ)⟧' = m ≫ ε := hφ₃
  let M := (quotPowFunctor J I).obj (op 1)
  let TM := (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj M
  let F' : ℕᵒᵖ ⥤ _ := (Functor.const ℕᵒᵖ).obj L ⋙ TM
  let G' : ℕᵒᵖ ⥤ _ := G ⋙ TM
  let PM : Fan fun n : ℕ ↦ G'.obj (op n) := Fan.mk (P.pt ⊗ M) fun j ↦ P.proj j ▷ M
  have hPM : IsLimit PM := isLimit_fan_whiskerRight_quot hϖ hI hP
  let PKM : Fan fun n : ℕ ↦ F'.obj (op n) := Fan.mk (PK.pt ⊗ M) fun j ↦ PK.proj j ▷ M
  have hPKM : IsLimit PKM := isLimit_fan_whiskerRight_quot hϖ hI hPK
  have htK : TM.map (towerShift hPK) = towerShift hPKM :=
    Fan.IsLimit.hom_ext hPKM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have ht : TM.map (towerShift hP) = towerShift hPM :=
    Fan.IsLimit.hom_ext hPM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have hTKM : Triangle.mk (TM.map (Fan.IsLimit.lift hPK fun n ↦ c₀.π.app (op n)))
      (𝟙 _ - towerShift hPKM) (TM.map δK ≫ (TM.commShiftIso (1 : ℤ)).hom.app L) ∈
        distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hTK) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, comp_id, id_comp]
          change _ = TM.map (𝟙 PK.pt - towerShift hPK)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, htK]
          rfl)
        (by simp; rfl))
  have hTFM : Triangle.mk (TM.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)))
      (𝟙 _ - towerShift hPM) (TM.map ε ≫ (TM.commShiftIso (1 : ℤ)).hom.app c.pt) ∈
        distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, comp_id, id_comp]
          change _ = TM.map (𝟙 P.pt - towerShift hP)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, ht]
          rfl)
        (by simp; rfl))
  let a : F' ⟶ G' := Functor.whiskerRight c'.π TM
  have hb := exists_lift_whiskerRight_derivedCompletionCone hϖ hI L
  choose b hb₁ hb₂ using hb
  have hm : productTowerMap (PF := PKM) hPM a = TM.map m :=
    Fan.IsLimit.hom_ext hPM _ _ fun n ↦ by
      rw [productTowerMap_proj]
      change _ = TM.map _ ≫ TM.map _
      rw [← TM.map_comp, productTowerMap_proj, TM.map_comp]
      rfl
  exact ⟨φ, isIso_of_proIso hPKM hPM hTKM hTFM a b hb₁ hb₂ (TM.map φ)
    (by rw [hm]; dsimp; rw [← TM.map_comp, ← TM.map_comp, hφ₁])
    (by
      rw [hm, assoc, ← TM.commShiftIso_hom_naturality, ← TM.map_comp_assoc, hφ₃,
        TM.map_comp_assoc])⟩

include hϖ hI in
/-- `ϖ` acts invertibly on an object `X` with `X ⊗ᴸ R/I = 0`. -/
lemma smulInvertible_of_isZero_tensor_quot {X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hX : IsZero (X ⊗ (quotPowFunctor J I).obj (op 1))) : smulInvertible J ϖ X := by
  have h₁ := (Triangle.isZero₃_iff_isIso₁ _ (tensorQuotPowTriangle_distinguished hϖ hI X 1)).1 hX
  change IsIso (X ◁ (quotPowTriangle J hϖ hI 1).mor₁) at h₁
  rw [quotPowTriangle_mor₁, pow_one, MonoidalLinear.whiskerLeft_smul,
    MonoidalCategory.whiskerLeft_id] at h₁
  change IsIso (ϖ • 𝟙 X)
  have : ϖ • 𝟙 X = (unitIso X).hom ≫ (ϖ • 𝟙 _) ≫ (unitIso X).inv := by
    rw [Linear.smul_comp, id_comp, Linear.comp_smul, Iso.hom_inv_id]
  have h₂ : IsIso (ϖ • 𝟙 (X ⊗ (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
      (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))))) := h₁
  rw [this]
  infer_instance

include hϖ hI in
/-- `X ⊗ᴸ R/Iⁿ = 0` when `ϖ` acts invertibly on `X`. -/
lemma isZero_tensor_quotPow_of_smulInvertible
    {X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (hX : smulInvertible J ϖ X) (n : ℕ) :
    IsZero (X ⊗ (quotPowFunctor J I).obj (op n)) := by
  refine (Triangle.isZero₃_iff_isIso₁ _ (tensorQuotPowTriangle_distinguished hϖ hI X n)).2 ?_
  have := hX.pow n
  change IsIso (X ◁ (quotPowTriangle J hϖ hI n).mor₁)
  rw [quotPowTriangle_mor₁, MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id]
  have h : ϖ ^ n • 𝟙 (X ⊗ (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
      (𝟙_ (Sheaf J (ModuleCat.{u + 1} R)))) =
      (unitIso X).inv ≫ (ϖ ^ n • 𝟙 X) ≫ (unitIso X).hom := by
    rw [Linear.smul_comp, id_comp, Linear.comp_smul, Iso.inv_hom_id]
  erw [h]
  infer_instance

include hϖ hI in
/-- A map which becomes an isomorphism after `- ⊗ᴸ R/I` becomes an isomorphism after every
`- ⊗ᴸ R/Iⁿ`: its cone `X` has `X ⊗ᴸ R/I = 0`, so `ϖ` acts invertibly on `X` and
`X ⊗ᴸ R/Iⁿ = 0`. -/
lemma isIso_whiskerRight_quotPow_of_isIso
    {L L' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (φ : L ⟶ L')
    (hφ : IsIso (φ ▷ (quotPowFunctor J I).obj (op 1))) (n : ℕ) :
    IsIso (φ ▷ (quotPowFunctor J I).obj (op n)) := by
  obtain ⟨X, g, h, hX⟩ := distinguished_cocone_triangle φ
  have hX₁ : IsZero (X ⊗ (quotPowFunctor J I).obj (op 1)) :=
    (Triangle.isZero₃_iff_isIso₁ _ (((curriedTensor _).flip.obj
      ((quotPowFunctor J I).obj (op 1))).map_distinguished _ hX)).2 hφ
  exact (Triangle.isZero₃_iff_isIso₁ _ (((curriedTensor _).flip.obj
    ((quotPowFunctor J I).obj (op n))).map_distinguished _ hX)).1
    (isZero_tensor_quotPow_of_smulInvertible hϖ hI
      (smulInvertible_of_isZero_tensor_quot hϖ hI hX₁) n)

include hϖ hI in
/-- **The derived completion has the same reductions.** For a homotopy limit `c` of the
reductions `L ⊗ᴸ R/Iⁿ` of `L` (the derived completion of `L`), the object `c.pt` is derived
complete and `c.pt ⊗ᴸ R/Iⁿ ≅ L ⊗ᴸ R/Iⁿ` for every `n`. -/
theorem derivedComplete_and_iso_of_isHomotopyLimit
    (L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    {c : Cone (derivedCompletionDiagram J I L)} (hc : IsHomotopyLimit c) :
    derivedComplete J I c.pt ∧ ∀ n : ℕ,
      Nonempty ((derivedCompletionDiagram J I c.pt).obj (op n) ≅
        (derivedCompletionDiagram J I L).obj (op n)) := by
  have hϖI := mem_of_eq_span hI
  refine ⟨(derivedComplete_iff_rightOrthogonal hϖ hI _).2 fun X f hX ↦ hc.hom_ext_zero
    (fun n g ↦ hX.hom_eq_zero (smul_id_derivedCompletionDiagram_obj J hϖI L n) g)
    (fun n g ↦ (ObjectProperty.le_shift _ 1 X hX).hom_eq_zero
      (smul_id_derivedCompletionDiagram_obj J hϖI L n) g) f, fun n ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := exists_isIso_whiskerRight_quot_of_isHomotopyLimit hϖ hI L hc
  have := isIso_whiskerRight_quotPow_of_isIso hϖ hI φ hφ n
  exact ⟨(asIso (φ ▷ (quotPowFunctor J I).obj (op n))).symm⟩

end Completion

end DerivedCategory

namespace CategoryTheory.Sheaf.NormalizedTower

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R] {I : Ideal R} {ϖ : R}

/-- **Effectivity of normalized towers.** Every normalized tower `M` is the tower of reductions
of a derived complete object `K` (its derived limit `R lim_n Res M_n`):
`K ⊗ᴸ R/Iⁿ ≅ Res M_n` for every `n`. The tower is represented by a strict normalized adic tower
of complexes (`DerivedCategory.exists_isNormalizedAdicTower`), whose derived limit has the
levels of the tower as reductions
(`DerivedCategory.exists_derivedCompletionDiagram_iso_of_isNormalizedAdicTower`). -/
theorem exists_derivedComplete_iso (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
    (M : NormalizedTower J I) :
    ∃ K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)),
      DerivedCategory.derivedComplete J I K ∧ ∀ n : ℕ,
        Nonempty ((DerivedCategory.derivedCompletionDiagram J I K).obj (op n) ≅
          M.restrict.obj (op n)) := by
  obtain ⟨T, e, hT, -⟩ := DerivedCategory.exists_isNormalizedAdicTower
    (fun {_ _} h ↦ Ideal.Quotient.factorPow I h) (fun n ↦ Ideal.Quotient.mk (I ^ n))
    (fun _ ↦ Ideal.Quotient.factor_comp_mk _)
    (fun _ _ ↦ RingHom.ext fun x ↦ by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
    (Ideal.Quotient.mk_pow_eq_zero_of_eq_span hI) (Ideal.Quotient.exact_mul_mk_pow hϖ hI)
    (fun _ ↦ Ideal.Quotient.factor_surjective _)
    (fun h ↦ Ideal.Quotient.ker_factor_pow_eq_span hI h) M.obj M.map M.isDerivedBaseChange
  obtain ⟨c, hc⟩ := IsHomotopyLimit.exists_cone (T ⋙ DerivedCategory.Q)
  obtain ⟨E, hE⟩ :=
    DerivedCategory.exists_derivedCompletionDiagram_iso_of_isNormalizedAdicTower hϖ hI hT hc
  refine ⟨c.pt, hc.of_iso E.symm _ (Iso.refl _) fun n ↦ ?_, fun n ↦ ⟨E.app (op n) ≪≫ e n⟩⟩
  rw [hE n]
  simp

end CategoryTheory.Sheaf.NormalizedTower
