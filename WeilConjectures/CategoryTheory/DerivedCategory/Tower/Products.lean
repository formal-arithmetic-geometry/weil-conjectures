/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Products of K-injective complexes in the derived category

Let `A` be an abelian category with K-injective resolutions. A product `∏ⱼ Iⱼ` of K-injective
cochain complexes is again K-injective (`CochainComplex.isKInjective_of_isLimit_fan`), and its
image in the derived category, with the images of the projections, is a product of the images
`Q Iⱼ` (`DerivedCategory.isLimitFanQOfIsKInjective`). In other words, products in `D(A)`
(`DerivedCategory.hasLimitsOfShape_discrete`) are computed by termwise products of
K-injective representatives.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable {A : Type*} [Category A] [Abelian A] {J : Type*} [HasLimitsOfShape (Discrete J) A]

/-- A product of K-injective complexes is K-injective: null-homotopies of the components of a
map from an acyclic complex are assembled degreewise (`HomotopyCategory.homotopyOfFan`). -/
lemma isKInjective_of_isLimit_fan {K : J → CochainComplex A ℤ} [∀ j, (K j).IsKInjective]
    {P : Fan K} (hP : IsLimit P) : P.pt.IsKInjective where
  nonempty_homotopy_zero f hX := ⟨HomotopyCategory.homotopyOfFan hP fun j ↦
    (IsKInjective.homotopyZero (f ≫ P.proj j) hX).trans (Homotopy.ofEq (by simp))⟩

end CochainComplex

namespace DerivedCategory

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Abelian.HasKInjectiveResolutions A] {J : Type*} [HasLimitsOfShape (Discrete J) A]

/-- The image in the derived category of a product fan of K-injective complexes is a product
fan: since `Qh` restricts to an equivalence between the homotopy category of K-injective
complexes and the derived category, and the K-injective complexes are closed under products
in the homotopy category, products of K-injective complexes compute products in `D(A)`. -/
noncomputable def isLimitFanQOfIsKInjective {K : J → CochainComplex A ℤ}
    [∀ j, (K j).IsKInjective] {P : Fan K} (hP : IsLimit P) :
    IsLimit (Fan.mk (Q.obj P.pt) fun j ↦ Q.map (P.proj j)) := by
  have := CochainComplex.isKInjective_of_isLimit_fan hP
  let F : Fan fun j ↦ HomotopyCategory.KInjectives.mk (K j) :=
    Fan.mk (HomotopyCategory.KInjectives.mk P.pt) fun j ↦
      ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (P.proj j))
  have hF : IsLimit F := isLimitOfReflects (ObjectProperty.ι _)
    ((isLimitMapConeFanMkEquiv _ _ _).symm (HomotopyCategory.isLimitFanQuotient _ _ hP))
  have hF' := (isLimitMapConeFanMkEquiv HomotopyCategory.KInjectives.Qh _ _)
    (isLimitOfPreserves HomotopyCategory.KInjectives.Qh hF)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv
    (Discrete.natIso fun j ↦ (quotientCompQhIso A).app (K j.as)) _).symm hF')
    (Fan.ext ((quotientCompQhIso A).app P.pt) fun j ↦ ?_)
  exact (quotientCompQhIso A).hom.naturality (P.proj j)

end DerivedCategory
