/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerRoosTriangle

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The localized evaluation tower of a K-injective complex has a Roos triangle.
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M. -/
theorem derivedCategory_towerLimit_triangle
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
      (c : Cone I.asFunctor), IsLimit c →
      let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (Opposite.op n))
      let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map
        (I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
      let p := Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (Opposite.op n)))
      ∃ δ : (∏ᶜ K₀) ⟶ (DerivedCategory.Q.obj c.pt)⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f₀ (DerivedCategory.Q.obj c.pt) p δ := by
  intro hI I _ c hc
  let K := fun n : ℕ ↦ I.asFunctor.obj (Opposite.op n)
  have (n : ℕ) : CochainComplex.IsKInjective (K n) :=
    tower_evaluation_isKInjective A I (Opposite.op n)
  let P : Fan K := HomologicalComplex.coneOfHasLimitEval (Discrete.functor K)
  let hP := HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor K)
  let qP := HomotopyCategory.quotient (A) (.up ℤ)
  let hqFan := HomotopyCategory.isLimitFanQuotient (A) (.up ℤ)
    (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor K))
  have hPI : CochainComplex.IsKInjective P.pt := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact (HomotopyCategory.subcategoryAcyclic (A)).rightOrthogonal.prop_of_isLimit
      hqFan (fun j ↦ CochainComplex.IsKInjective.rightOrthogonal (K j.as))
  have : CochainComplex.IsKInjective P.pt := hPI
  let hqP := (Fan.isLimitMapConeEquiv qP K P).symm hqFan
  let L := DerivedCategory.Qh (C := A)
  let pre (s : Cone ((Discrete.functor K ⋙ qP) ⋙ L)) :
      Cone (Discrete.functor K ⋙ qP) :=
    { pt := L.objPreimage s.pt
      π := Discrete.natTrans fun j ↦
        (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
          (L.objPreimage s.pt) (K j.as))).symm
            ((L.objObjPreimageIso s.pt).hom ≫ s.π.app j) }
  have key (s : Cone ((Discrete.functor K ⋙ qP) ⋙ L)) (j : Discrete ℕ) :
      L.map ((pre s).π.app j) = (L.objObjPreimageIso s.pt).hom ≫ s.π.app j :=
    (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
      (L.objPreimage s.pt) (K j.as))).apply_symm_apply _
  have hd : IsLimit (L.mapCone (qP.mapCone P)) := by
    refine
      { lift := fun s ↦ (L.objObjPreimageIso s.pt).inv ≫ L.map (hqP.lift (pre s))
        fac := ?_
        uniq := ?_ }
    · intro s j
      dsimp only [Functor.mapCone_π_app]
      have fac := hqP.fac (pre s) j
      dsimp only [Functor.mapCone_π_app] at fac
      rw [Category.assoc, ← L.map_comp, fac, key]
      simp
    · intro s m hm
      dsimp only [Functor.mapCone_π_app] at hm
      obtain ⟨m', hm'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
        (L.objPreimage s.pt) P.pt).surjective ((L.objObjPreimageIso s.pt).hom ≫ m)
      have eq : m' = hqP.lift (pre s) := by
        apply hqP.uniq (pre s) m'
        intro j
        apply (CochainComplex.IsKInjective.Qh_map_bijective
          (L.objPreimage s.pt) (K j.as)).injective
        simp only [Functor.mapCone_π_app]
        rw [L.map_comp, hm', Category.assoc, hm j, key]
      rw [← eq, hm']
      simp
  have hQP : IsLimit (DerivedCategory.Q.mapCone P) :=
    IsLimit.mapConeEquiv (DerivedCategory.quotientCompQhIso (A)) hd
  let iota : c.pt ⟶ P.pt := hP.lift
    (Fan.mk c.pt (fun n : ℕ ↦ c.π.app (Opposite.op n)))
  let s : P.pt ⟶ P.pt := hP.lift
    (Fan.mk P.pt (fun n : ℕ ↦ P.proj (n + 1) ≫
      I.asFunctor.map (homOfLE (Nat.le_succ n)).op))
  let t : P.pt ⟶ P.pt := 𝟙 _ - s
  have hiota (n : ℕ) : iota ≫ P.proj n = c.π.app (Opposite.op n) :=
    hP.fac _ ⟨n⟩
  have ht (n : ℕ) : t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫
      I.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
    dsimp [t]
    rw [Preadditive.sub_comp, Category.id_comp]
    exact congrArg (fun x ↦ P.proj n - x) (hP.fac _ ⟨n⟩)
  obtain ⟨δ, hδ⟩ := derivedCategory_tower_roos_triangle A I c hc P hP iota t hiota ht
  let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (K n)
  let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map
    (I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  let p := Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (Opposite.op n)))
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K P) hQP
  let E : DerivedCategory.Q.obj P.pt ≅ ∏ᶜ K₀ :=
    hQFan.conePointUniqueUpToIso (productIsProduct K₀)
  have hE (n : ℕ) : E.hom ≫ Pi.π K₀ n = DerivedCategory.Q.map (P.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct K₀) ⟨n⟩
  have hπ (n : ℕ) : p ≫ Pi.π K₀ n = DerivedCategory.Q.map (c.π.app (Opposite.op n)) :=
    Pi.lift_comp_π _ _
  have hi : DerivedCategory.Q.map iota ≫ E.hom = p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hiota, hπ]
  have hT : DerivedCategory.Q.map t ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism f₀ := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, ht, Functor.map_sub]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_comp_π, hE, f₀]
    rw [Functor.map_comp, ← Category.assoc, hE]
  refine ⟨E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (DerivedCategory.Q.map iota) (DerivedCategory.Q.map t) δ)
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f₀) (E.inv ≫ δ))
      (Iso.refl _) E E (by simpa using hi) hT (by simp))).mp hδ

end CategoryTheory
