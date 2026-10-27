/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.KFlatRoosDerivedComparison
import Sheaf.CategoryTheory.KFlatRoosSignedMap
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Product preservation and the tensor comparison on resolved limits -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] SheafOfModules.TotalTensorSigns.total
  SheafOfModules.TotalTensorSigns.tensor CategoryTheory.Functor.map₂HomologicalComplex

universe u v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex
namespace CategoryTheory.KFlatAugmentedRoos
open SheafOfModules.TotalTensorSigns
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {𝒥 : GrothendieckTopology C} (R : Sheaf 𝒥 CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)]

/-- Invertibility of the canonical derived product comparison makes the ordinary-limit
comparison between injective resolutions invertible after localization.
Source: Stacks sites-cohomology.tex Tags 0941 and 06YM; derived.tex Tag 014A;
steps 5, 8 and 9 of lem-sfb-kflat-augmented-roos-comparison.
(blueprint: lem-sfb-kflat-roos-product-criterion).
Proof: the injective-tower theorem identifies the products of I and J with their
derived products, and their limit inclusions into the shifted cones are
quasi-isomorphisms. The signed tensor/cone comparison gives a morphism of their
normalized distinguished fibre triangles. Both product components are Qb. Projection
onto n identifies Qb, transported through the localization comparison e, with the
canonical derived product comparison. The quasi-isomorphisms s and q identify the
families with the given family QX_n, so the assumed product comparison makes both
components invertible. The triangle two-out-of-three theorem makes the fibre map
invertible. The strict limit-inclusion square and the two invertible inclusions
then make Qθ invertible. No product of unresolved complexes is assumed exact. -/
theorem limitComparisonMap_isIso
    [HasCountableProducts (DerivedCategory.{w} (Modules R))]
    (A : CochainComplex (Modules R) ℤ) (hA : IsKFlatIndependentCoefficients A)
    (T : DerivedCategory.{w} (Modules R) ⥤ DerivedCategory.{w} (Modules R))
    (e : DerivedCategory.Q.{w} ⋙ T ≅ (total R).obj A ⋙ DerivedCategory.Q.{w})
    (X I J : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ)
    (s : X ⟶ I) (q : (tower ((total R).obj A)).obj I ⟶ J)
    [QuasiIso s] [I.IsKInjective] (hI : ∀ k : ℤ, Injective (I.X k))
    [QuasiIso q] [J.IsKInjective] (hJ : ∀ k : ℤ, Injective (J.X k))
    (hprod : IsIso (piComparison T
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (.op n))))) :
    IsIso (DerivedCategory.Q.{w}.map (limitComparisonMap ((total R).obj A) I J q)) := by
  classical
  let := hprod
  let : PreservesLimit (Discrete.functor
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (.op n)))) T :=
    PreservesProduct.of_iso_comparison T _
  have hlevels := (HomologicalComplex.quasiIso_iff_evaluation s).1
    (inferInstance : QuasiIso s)
  have heXI (n : ℕ) : IsIso (DerivedCategory.Q.{w}.map
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map s).app (.op n))) := by
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules R) _).2 (hlevels (.op n))
  let (n : ℕ) := heXI n
  let eXI (n : ℕ) := asIso (DerivedCategory.Q.{w}.map
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map s).app (.op n)))
  let : PreservesLimit (Discrete.functor
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (I.asFunctor.obj (.op n)))) T :=
    preservesLimit_of_iso_diagram T
      (Discrete.natIso (fun n ↦ eXI n.as) :
        Discrete.functor (fun n : ℕ ↦ DerivedCategory.Q.obj (X.asFunctor.obj (.op n))) ≅
          Discrete.functor (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (.op n))))
  have facts (N : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ)
      [N.IsKInjective] (hi : ∀ k : ℤ, Injective (N.X k)) :
      Nonempty (IsLimit (DerivedCategory.Q.{w}.mapCone
        (limit.cone (Discrete.functor (fun n : ℕ ↦ N.asFunctor.obj (.op n)))))) ∧
        QuasiIso (roosι N) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hroos, _, _⟩ := injectiveTowerRoosShifts
      𝒥 ((sheafCompose 𝒥 (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
      (fun U a b ↦ @mul_comm (R.obj.obj U) inferInstance a b)
    exact ⟨(hroos N hi).2.2.2.1, (hroos N hi).2.2.2.2.1⟩
  obtain ⟨⟨hpI⟩, hιI⟩ := facts I hI
  obtain ⟨⟨hpJ⟩, hιJ⟩ := facts J hJ
  let fI := fun n : ℕ ↦ I.asFunctor.obj (.op n)
  let fJ := fun n : ℕ ↦ J.asFunctor.obj (.op n)
  let hpI' := (isLimitMapConeFanMkEquiv DerivedCategory.Q fI
    (fun n ↦ Pi.π fI n)).1 hpI
  let hpJ' := (isLimitMapConeFanMkEquiv DerivedCategory.Q fJ
    (fun n ↦ Pi.π fJ n)).1 hpJ
  let htpI := isLimitFanMkObjOfIsLimit T _ _ hpI'
  let b := productComparisonMap ((total R).obj A) I J q
  have hqlevels := (HomologicalComplex.quasiIso_iff_evaluation q).1
    (inferInstance : QuasiIso q)
  have hbn (n : ℕ) : IsIso (DerivedCategory.Q.map
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (.op n))) := by
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules R) _).2 (hqlevels (.op n))
  let (n : ℕ) := hbn n
  let eb (n : ℕ) := e.app (fI n) ≪≫ asIso (DerivedCategory.Q.map
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (.op n)))
  have hbiso : IsIso (e.hom.app (roosP I) ≫ DerivedCategory.Q.map b) := by
    apply Fan.IsLimit.isIso_of_isos htpI hpJ' eb
    intro n
    dsimp only [eb, Iso.trans_hom, asIso_hom]
    change (e.hom.app (roosP I) ≫ DerivedCategory.Q.map b) ≫
      DerivedCategory.Q.map (Pi.π fJ n) =
        T.map (DerivedCategory.Q.map (Pi.π fI n)) ≫
          (e.app (fI n)).hom ≫ _
    erw [Category.assoc, ← DerivedCategory.Q.map_comp, productComparisonMap_π]
    erw [DerivedCategory.Q.map_comp, ← Category.assoc]
    erw [← e.hom.naturality]
    simp only [Functor.comp_map, Category.assoc]
    rfl
  have hbiso' : IsIso (DerivedCategory.Q.map b) :=
    (isIso_comp_left_iff (e.hom.app (roosP I)) _).1 hbiso
  let := hbiso'
  have hb := productComparisonMap_comm ((total R).obj A) I J q
  let m := DerivedCategory.Q.mapTriangle.map
    (mappingCone.triangleMap (((total R).obj A).map (roosU I)) (roosU J) b b hb)
  have hm : IsIso m.hom₃ := Pretriangulated.isIso₃_of_isIso₁₂ m
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _) hbiso' hbiso'
  have hc : IsIso (DerivedCategory.Q.map (mappingCone.map _ _ b b hb)) := hm
  have hshift : IsIso (DerivedCategory.Q.map ((mappingCone.map _ _ b b hb)⟦(-1 : ℤ)⟧')) := by
    have := (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules R) _).1 hc
    infer_instance
  let : IsIso (DerivedCategory.Q.map ((mappingCone.map
      (((MonoidalCategory.curriedTensor (Modules R)).map₂CochainComplex.obj A).map (roosU I))
      (roosU J) b b hb)⟦(-1 : ℤ)⟧')) := hshift
  have hψ : IsIso (DerivedCategory.Q.map (signedFiberMap R A I J b hb)) := by
    dsimp only [signedFiberMap]
    rw [DerivedCategory.Q.map_comp]
    infer_instance
  have hθ : ((total R).obj A).map (InjectiveTowerRoos.inclusion I) ≫ b =
      limitComparisonMap ((total R).obj A) I J q ≫ InjectiveTowerRoos.inclusion J := by
    apply Pi.hom_ext
    intro n
    dsimp only [InjectiveTowerRoos.inclusion]
    simp only [Category.assoc, Pi.lift_π]
    rw [productComparisonMap_π, ← Functor.map_comp_assoc, Pi.lift_π,
      limitComparisonMap_π]
  have hsquare := (signedFiberMap_spec R A I J b _ hb hθ).2
  let := hιI
  let := hιJ
  have hAι := (SheafOfModules.TotalTensorSigns.totalTensorHomotopyConeSigns R).2.2.2.2.2.2.1
    A hA
  have : QuasiIso (((total R).obj A).map (roosι I)) :=
    (hAι.1 _ _ (roosι I) hιI).1
  have hi : IsIso (DerivedCategory.Q.map
      (limitComparisonMap ((total R).obj A) I J q) ≫ DerivedCategory.Q.map (roosι J)) := by
    rw [← DerivedCategory.Q.map_comp, ← hsquare, DerivedCategory.Q.map_comp]
    infer_instance
  exact (isIso_comp_right_iff _ (DerivedCategory.Q.map (roosι J))).1 hi

end CategoryTheory.KFlatAugmentedRoos
