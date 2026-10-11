/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ReductionCone
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Reductions of the derived limit of a strict normalized adic tower

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. For a normalized `ϖ`-adic tower `T` of complexes of sheaves of
`R`-modules (`CochainComplex.IsNormalizedAdicTower`) and a homotopy limit
`K = R lim_n T_n` of its image in `D(J, R)`, the reductions `K ⊗ᴸ R/Iⁿ` are the `T_n`,
compatibly with the reduction maps and with the transitions
(work in progress).

The proof follows blueprint `sk-prop-trace-adic` (i): `- ⊗ᴸ R/Iⁿ` is triangulated and commutes
with countable products, hence with `R lim`; on complexes it is the mapping cone of `ϖⁿ`
(`DerivedCategory.reductionIso`), and the tower of cones `cone(ϖⁿ on T_{m+n})` has derived limit
`T_n` (`CochainComplex.IsNormalizedAdicTower.isIso_π_comp`).

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

local instance : IsIso (sheafTensorStructure J R).ε := (sheafTensorStructure J R).isIso_ε

variable {J}

section Products

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

/-- Tensoring with `R/Iⁿ` commutes with countable products. -/
noncomputable def isLimit_fan_whiskerRight_quotPow (n : ℕ)
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (quotPowFunctor J I).obj (op n)) fun j ↦ P.proj j ▷ _) := by
  let T := fun j ↦ tensorQuotPowTriangle hϖ hI (Y j) n
  let ψ : tensorQuotPowTriangle hϖ hI P.pt n ⟶ productTriangle T :=
    productTriangle.lift T fun j ↦ tensorQuotPowTriangleMap hϖ hI (P.proj j) n
  have hU := isLimit_fan_whiskerRight_unit (J := J) hP
  have h₁ : IsIso ψ.hom₁ := by
    have : ψ.hom₁ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₂ : IsIso ψ.hom₂ := by
    have : ψ.hom₂ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₃ : IsIso ψ.hom₃ := isIso₃_of_isIso₁₂ ψ (tensorQuotPowTriangle_distinguished hϖ hI _ n)
    (productTriangle_distinguished T fun j ↦ tensorQuotPowTriangle_distinguished hϖ hI _ n) h₁ h₂
  refine IsLimit.ofIsoLimit (productIsProduct _) (Fan.ext (asIso ψ.hom₃).symm fun j ↦ ?_)
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
  simp only [ψ, productTriangle.lift_hom₃, tensorQuotPowTriangleMap, Fan.mk_pt]
  exact Pi.lift_π _ _

variable (J I) in
/-- The reduction functor `- ⊗ᴸ R/Iⁿ` on `D(J, R)`. -/
noncomputable abbrev reductionFunctor (n : ℕ) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj
    ((quotPowFunctor J I).obj (op n))

include hϖ hI in
/-- The reduction functor `- ⊗ᴸ R/Iⁿ` preserves homotopy limits of towers. -/
lemma IsHomotopyLimit.map_reductionFunctor (n : ℕ)
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {c : Cone F}
    (hc : IsHomotopyLimit c) : IsHomotopyLimit ((reductionFunctor J I n).mapCone c) := by
  have : PreservesLimit (Discrete.functor fun j : ℕ ↦ F.obj (op j)) (reductionFunctor J I n) :=
    preservesLimit_of_preserves_limit_cone (productIsProduct _)
      ((isLimitMapConeFanMkEquiv _ _ _).symm
        (isLimit_fan_whiskerRight_quotPow hϖ hI n (productIsProduct _)))
  exact hc.map (reductionFunctor J I n)

end Products

section Reduction

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

lemma constantSheaf_map_smul_id (r : R) :
    (constantSheaf J (ModuleCat.{u + 1} R)).map (r • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) =
      r • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))) := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

include hI in
lemma smul_comp_sheafQuotPowCone_π (n : ℕ) :
    (ϖ ^ n • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{u + 1} R)))) ≫ (Sheaf.quotPowCone J I).π.app (op n) =
      0 := by
  erw [← constantSheaf_map_smul_id]
  change (constantSheaf J (ModuleCat.{u + 1} R)).map _ ≫
    (constantSheaf J (ModuleCat.{u + 1} R)).map _ = 0
  rw [← Functor.map_comp]
  exact (congrArg _ (quotPowShortComplex I ϖ (mem_of_eq_span hI) n).zero).trans
    (Functor.map_zero _ _ _)

include hϖ in
/-- The short exact sequence `0 ⟶ R ⟶ R ⟶ R/Iⁿ ⟶ 0` of constant sheaves, the first map being
the multiplication by `ϖⁿ` on the monoidal unit. -/
lemma sheafQuotPowShortComplex_shortExact' (n : ℕ) :
    (ShortComplex.mk _ _ (smul_comp_sheafQuotPowCone_π (J := J) (R := R) hI n)).ShortExact := by
  have h := sheafQuotPowShortComplex_shortExact J hϖ hI n
  refine ShortComplex.shortExact_of_iso ?_ h
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, id_comp, comp_id, ShortComplex.map_f]
    exact (constantSheaf_map_smul_id (J := J) (ϖ ^ n)).symm
  · simp only [Iso.refl_hom, id_comp, comp_id, ShortComplex.map_g]
    rfl

/-- The reduction `Q X ⊗ᴸ R/Iⁿ` of a complex `X` of sheaves is the mapping cone of `ϖⁿ` on
`X`. -/
noncomputable def reductionConeIso (n : ℕ)
    (X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) :
    Q.obj X ⊗ (quotPowFunctor J I).obj (op n) ≅
      Q.obj (CochainComplex.mappingCone (ϖ ^ n • 𝟙 X)) :=
  TensorStructure.reductionIso (sheafTensorStructure J R) rfl
    (smul_comp_sheafQuotPowCone_π hI n)
    (sheafQuotPowShortComplex_shortExact' hϖ hI n) X

end Reduction

section Reduction'

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

lemma reductionConeIso_hom_naturality (n : ℕ)
    {X Y : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ} (f : X ⟶ Y) :
    (Q.map f ▷ (quotPowFunctor J I).obj (op n)) ≫ (reductionConeIso hϖ hI n Y).hom =
      (reductionConeIso hϖ hI n X).hom ≫
        Q.map (CochainComplex.mappingCone.map (ϖ ^ n • 𝟙 X) (ϖ ^ n • 𝟙 Y) f f (by simp)) :=
  TensorStructure.reductionIso_hom_naturality (sheafTensorStructure J R) rfl _ _ f

/-- Under `reductionConeIso`, the reduction map `Q X ⟶ Q X ⊗ᴸ R/Iⁿ` is the inclusion of `X` into
the mapping cone. -/
lemma derivedCompletionCone_π_app_reductionConeIso_hom (n : ℕ)
    (X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) :
    (derivedCompletionCone J I (Q.obj X)).π.app (op n) ≫ (reductionConeIso hϖ hI n X).hom =
      Q.map (CochainComplex.mappingCone.inr (ϖ ^ n • 𝟙 X)) :=
  by
  rw [show (derivedCompletionCone J I (Q.obj X)).π.app (op n) = (ρ_ (Q.obj X)).inv ≫
    Q.obj X ◁ ((sheafTensorStructure J R).ε ≫ (singleFunctor _ 0).map
      ((Sheaf.quotPowCone J I).π.app (op n))) from rfl, assoc]
  exact TensorStructure.reduction_reductionIso_hom (sheafTensorStructure J R) rfl
    (smul_comp_sheafQuotPowCone_π hI n) (sheafQuotPowShortComplex_shortExact' hϖ hI n) X

/-- `reductionConeIso` is compatible with the transition `R/Iⁿ ⟶ R/Iᵏ` for `k ≤ n`. -/
lemma derivedCompletionDiagram_map_reductionConeIso_hom {k n : ℕ} (h : k ≤ n)
    (X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) :
    (derivedCompletionDiagram J I (Q.obj X)).map (homOfLE h).op ≫
        (reductionConeIso hϖ hI k X).hom =
      (reductionConeIso hϖ hI n X).hom ≫ Q.map (CochainComplex.mappingCone.map
        (ϖ ^ n • 𝟙 X) (ϖ ^ k • 𝟙 X) (ϖ ^ (n - k) • 𝟙 X) (𝟙 X)
        (smul_comp_smul_eq (by rw [← pow_add, Nat.add_sub_cancel' h]) X).symm) :=
  TensorStructure.whiskerLeft_reductionIso_hom (sheafTensorStructure J R) rfl
    (by rw [← pow_add, Nat.add_sub_cancel' h]) _ _ _ _ _ ((Sheaf.quotPowCone J I).w _) X

/-- The reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ` are natural in `K`. -/
@[reassoc]
lemma derivedCompletionCone_π_app_naturality
    {K K' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (f : K ⟶ K') (n : ℕ) :
    (derivedCompletionCone J I K).π.app (op n) ≫ f ▷ (quotPowFunctor J I).obj (op n) =
      f ≫ (derivedCompletionCone J I K').π.app (op n) := by
  change ((ρ_ K).inv ≫ K ◁ _) ≫ _ = f ≫ (ρ_ K').inv ≫ K' ◁ _
  rw [assoc, whisker_exchange, ← assoc, ← rightUnitor_inv_naturality, assoc]

end Reduction'

end DerivedCategory
