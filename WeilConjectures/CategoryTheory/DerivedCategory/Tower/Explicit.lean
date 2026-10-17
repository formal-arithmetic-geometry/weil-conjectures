/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.ConeTower
public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Model

/-!
# The explicit product-cone model of the derived inverse limit

Let `A` be a Grothendieck abelian category. For a complex of towers `M` in `A`, let `I` be its
functorial K-injective resolution and `s : ∏ₙ Iₙ ⟶ ∏ₙ Iₙ` the transition endomorphism
`(xₙ)ₙ ↦ (t_{n+1,n}(x_{n+1}))ₙ` of the termwise product of its levels. This file defines the
explicit model

`R lim M := Cone(1 - s : ∏ₙ Iₙ ⟶ ∏ₙ Iₙ)[-1]`

(`DerivedCategory.rlimExplicit`), as a functor of `M` (maps of towers act componentwise on the
two products, hence on the mapping cone), together with its functorial distinguished triangle
`R lim M ⟶ ∏ₙ Mₙ ──1 - s──▶ ∏ₙ Mₙ ⟶ (R lim M)[1]` (`DerivedCategory.rlimExplicitTriangle`).
The product `Q (∏ₙ Iₙ)` is the derived product of the evaluations of `M`
(`DerivedCategory.isLimitFanTowerDiagram`), and the explicit model is isomorphic to the derived
limit `R lim (Q M)` (`DerivedCategory.nonempty_rlimExplicit_iso`), both being cocones of the
Roos triangle on the same morphism `1 - s`.

For an adic coefficient tower `P` (`DerivedCategory.reductionTower`), the explicit adic derived
inverse limit of `K = Q X`, `X` K-flat, is the explicit model of the complex of towers
`(X ⊗ Pₙ)ₙ` (`DerivedCategory.adicRlimExplicit`, Blueprint
`def-weil-pbc-adic-derived-inverse-limit`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace DerivedCategory

section Explicit

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- The termwise product `∏ₙ Mₙ` of the levels of a complex of towers `M`, as a functor. -/
@[simps]
noncomputable def towerProduct : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj M := ∏ᶜ fun n : ℕ ↦ M.asFunctor.obj (op n)
  map f := Pi.map fun n ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)
  map_id M := Pi.hom_ext _ _ fun n ↦ by simp
  map_comp f g := Pi.hom_ext _ _ fun n ↦ by simp

/-- The transition endomorphism `s : (xₙ)ₙ ↦ (t_{n+1,n}(x_{n+1}))ₙ` of the termwise product of
the levels of a complex of towers. -/
noncomputable def towerProductShift : towerProduct A ⟶ towerProduct A where
  app M := towerShift (productIsProduct fun n : ℕ ↦ M.asFunctor.obj (op n))
  naturality M M' f := Pi.hom_ext _ _ fun n ↦ by
    have h₁ := towerShift_proj (productIsProduct fun n : ℕ ↦ M.asFunctor.obj (op n)) n
    have h₂ := towerShift_proj (productIsProduct fun n : ℕ ↦ M'.asFunctor.obj (op n)) n
    simp only [Fan.mk_pt, fan_mk_proj] at h₁ h₂
    simp only [towerProduct_obj, towerProduct_map, Category.assoc, h₂, Pi.map_π_assoc,
      Pi.map_π, ← Category.assoc, h₁]
    simp only [Category.assoc]
    congr 1
    exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality _).symm

@[reassoc (attr := simp)]
lemma towerProductShift_app_π (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (towerProductShift A).app M ≫ Pi.π _ n =
      Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) (n + 1) ≫
        M.asFunctor.map (homOfLE n.le_succ).op :=
  towerShift_proj (productIsProduct fun n : ℕ ↦ M.asFunctor.obj (op n)) n

/-- **Blueprint `def-weil-pbc-adic-derived-inverse-limit`** (the general product-cone model).
The explicit derived inverse limit of a complex of towers `M`:
`R lim M := Cone(1 - s : ∏ₙ Iₙ ⟶ ∏ₙ Iₙ)[-1]`, where `I` is the functorial K-injective
resolution of `M` and `s` is the transition endomorphism of the termwise product of its levels.
It is a functor of `M`: maps of towers act componentwise on the two products and hence on the
mapping cone. -/
noncomputable def rlimExplicit : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ DerivedCategory A :=
  CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A) ⋙
    CochainComplex.mappingConeFunctor (𝟙 (towerProduct A) - towerProductShift A) ⋙ Q ⋙
      shiftFunctor (DerivedCategory A) (-1 : ℤ)

/-- The distinguished triangle `R lim M ⟶ ∏ₙ Iₙ ──1 - s──▶ ∏ₙ Iₙ ⟶ (R lim M)[1]` of the
explicit model `DerivedCategory.rlimExplicit`, the inverse rotation of the mapping cone
triangle of `1 - s`. -/
noncomputable def rlimExplicitTriangle (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Triangle (DerivedCategory A) :=
  (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
    ((𝟙 (towerProduct A) - towerProductShift A).app
      ((CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)).obj M)))).invRotate

lemma rlimExplicitTriangle_obj₁ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (rlimExplicitTriangle A M).obj₁ = (rlimExplicit A).obj M := rfl

lemma rlimExplicitTriangle_mor₂ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (rlimExplicitTriangle A M).mor₂ =
      Q.map ((𝟙 (towerProduct A) - towerProductShift A).app
        ((CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)).obj M)) := rfl

lemma rlimExplicitTriangle_distinguished (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    rlimExplicitTriangle A M ∈ distTriang _ :=
  inv_rot_of_distTriang _ (mappingCone_triangle_distinguished _)

variable {A}

/-- For a K-injective complex of towers `I`, the image of the termwise product `∏ₙ Iₙ`, with the
image of the transition endomorphism, is a product of the evaluations whose `towerShift` is
`Q s`. -/
lemma towerShift_isLimitFanMkQ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    towerShift (F := I.asFunctor ⋙ Q)
        (isLimitFanMkQObjOfIsKInjective (productIsProduct fun n : ℕ ↦ I.asFunctor.obj (op n))) =
      Q.map ((towerProductShift A).app I) :=
  Fan.IsLimit.hom_ext (isLimitFanMkQObjOfIsKInjective (productIsProduct _)) _ _ fun n ↦ by
    rw [towerShift_proj]
    simp only [fan_mk_proj, Functor.comp_map, ← Functor.map_comp]
    congr 1
    exact (towerProductShift_app_π A I n).symm

/-- **Blueprint `def-weil-pbc-adic-derived-inverse-limit`** (comparison with `R lim`). The
explicit model `Cone(1 - s)[-1]` of a complex of towers `M` is isomorphic to the derived limit
`R lim (Q M)`: both complete the morphism `1 - s` of the derived product to a distinguished
triangle (the Roos triangle `DerivedCategory.isHomotopyLimit_rlimCone`). -/
theorem nonempty_rlimExplicit_iso (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Nonempty ((rlimExplicit A).obj M ≅ (rlim A).obj (Q.obj M)) := by
  let I := (CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)).obj M
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{v} (ℕᵒᵖ ⥤ A)).app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{v} _ M).2
  let eM : (rlim A).obj (Q.obj I) ≅ (rlim A).obj (Q.obj M) :=
    (rlim A).mapIso (asIso (Q.map ((CochainComplex.toKInjectiveResolution.{v} _).app M))).symm
  obtain ⟨P, hP, δ, hT⟩ := isHomotopyLimit_mapCone_limConeAsFunctor I
  let hPD := isLimitFanMkQObjOfIsKInjective (productIsProduct fun n : ℕ ↦ I.asFunctor.obj (op n))
  let eP : P.pt ≅ Q.obj ((towerProduct A).obj I) := hP.conePointUniqueUpToIso hPD
  have heP (n : ℕ) : eP.hom ≫ Q.map (Pi.π _ n) = P.proj n :=
    hP.conePointUniqueUpToIso_hom_comp hPD ⟨n⟩
  have ht : towerShift hP ≫ eP.hom = eP.hom ≫ Q.map ((towerProductShift A).app I) := by
    rw [← towerShift_isLimitFanMkQ]
    refine Fan.IsLimit.hom_ext hPD _ _ fun n ↦ ?_
    simp only [Category.assoc]
    erw [heP, towerShift_proj, towerShift_proj]
    rw [← Category.assoc]
    erw [heP]
  let T₁ := (Triangle.mk (Fan.IsLimit.lift hP fun n ↦ (Q.mapCone (limConeAsFunctor I)).π.app
    (op n)) (𝟙 P.pt - towerShift hP) δ).rotate
  let T₂ := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
    ((𝟙 (towerProduct A) - towerProductShift A).app I))
  have e : Arrow.mk T₁.mor₁ ≅ Arrow.mk T₂.mor₁ := Arrow.isoMk eP eP (by
    dsimp [T₁, T₂]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, ht, Category.id_comp, Category.comp_id,
      Functor.map_sub, Functor.map_id, Preadditive.comp_sub, Category.comp_id])
  obtain ⟨e', -⟩ := exists_iso_of_arrow_iso T₁ T₂ (rot_of_distTriang _ hT)
    (mappingCone_triangle_distinguished _) e
  let e₃ : (Q.obj (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex _).obj I))⟦(1 : ℤ)⟧ ≅
      Q.obj (CochainComplex.mappingCone ((𝟙 (towerProduct A) - towerProductShift A).app I)) :=
    Triangle.π₃.mapIso e'
  exact ⟨(shiftFunctor _ (-1 : ℤ)).mapIso e₃.symm ≪≫
    (shiftFunctorCompIsoId (DerivedCategory A) (1 : ℤ) (-1) (by lia)).app _ ≪≫
    (rlimObjQIso I).symm ≪≫ eM⟩

end Explicit

section Adic

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

/-- **Blueprint `def-weil-pbc-adic-derived-inverse-limit`.** The explicit adic derived inverse
limit of the reduction tower `Kₙ = K ⊗ᴸ Pₙ` attached to a coefficient tower `P`, for
`K = Q X` represented by a K-flat complex `X`: the product-cone model
`R lim_n Kₙ := Cone(1 - s : ∏ₙ Kₙ ⟶ ∏ₙ Kₙ)[-1]` (`DerivedCategory.rlimExplicit`) of the complex
of towers `(X ⊗ Pₙ)ₙ`. It is functorial in `X`, comes with the functorial distinguished triangle
`R lim_n Kₙ ⟶ ∏ₙ Kₙ ──1 - s──▶ ∏ₙ Kₙ ⟶` (`DerivedCategory.rlimExplicitTriangle_distinguished`),
and is isomorphic to `R lim` of the reduction tower
(`DerivedCategory.nonempty_adicRlimExplicit_iso`). -/
noncomputable def adicRlimExplicit (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    CochainComplex.KFlat A ⥤ DerivedCategory A :=
  CochainComplex.ιKFlat A ⋙ tensorTowerFunctor P ⋙ rlimExplicit A

/-- The explicit adic derived inverse limit of `K = Q X` is isomorphic to the derived limit
`R lim` of the reduction tower `K_• = DerivedCategory.reductionTower P K`. -/
theorem nonempty_adicRlimExplicit_iso (P : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (X : CochainComplex.KFlat A) :
    Nonempty ((adicRlimExplicit P).obj X ≅
      (rlim A).obj ((reductionTower P).obj ((TensorCommShift₂.LKFlat A).obj X))) := by
  obtain ⟨e⟩ := nonempty_rlimExplicit_iso ((tensorTowerFunctor P).obj X.1)
  exact ⟨e ≪≫ (rlim A).mapIso ((Localization.Lifting.iso (TensorCommShift₂.LKFlat A)
    (kFlatQuasiIso A) (tensorTowerFunctorKFlat P) (reductionTower P)).app X).symm⟩

end Adic

end DerivedCategory
