/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-!
# Naturality of normalized scalar reduction boundaries

The quotient and Kummer identifications are characterized by adjunction units.
Their naturality, and the naturality of the resulting degree-two boundary, are formal
consequences of the exact right-adjoint square and its shift-compatible derived mate.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]

end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [R'.CommShift ℤ]
  (ρ : R ⋙ F ≅ G ⋙ R') [NatTrans.CommShift ρ.hom ℤ]
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')

end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')

end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  (a : L ⊣ R) (a' : L' ⊣ R') (F : A ⥤ A') (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R') (θ : L ⋙ G ≅ F ⋙ L')
  (hθ : ∀ X, a'.unit.app (F.obj X) ≫ R'.map (θ.inv.app X) =
    F.map (a.unit.app X) ≫ ρ.hom.app (L.obj X))
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  (L : A ⥤ B) (L' : A' ⥤ B') (F : A ⥤ A') (G : B ⥤ B')
  [L.CommShift ℤ] [L'.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  (θ : L ⋙ G ≅ F ⋙ L') [NatTrans.CommShift θ.hom ℤ]
  {X₁ X₃ : A} {X₁' X₃' : A'} {H Q : B} {H' Q' : B'}
  (t₁ : F.obj X₁ ⟶ X₁') (t₃ : F.obj X₃ ⟶ X₃')
  (sH : G.obj H ⟶ H') (sQ : G.obj Q ⟶ Q')
  (δ : ShiftedHom X₃ X₁ (1 : ℤ)) (δ' : ShiftedHom X₃' X₁' (1 : ℤ))
  (aF : L.obj X₃ ≅ Q) (aF' : L'.obj X₃' ≅ Q')
  (aB : ShiftedHom (L.obj X₁) H (1 : ℤ))
  (aB' : ShiftedHom (L'.obj X₁') H' (1 : ℤ))
  (hF : G.map aF.hom ≫ sQ = θ.hom.app X₃ ≫ L'.map t₃ ≫ aF'.hom)
  (hB : aB.map G ≫ sH⟦(1 : ℤ)⟧' = θ.hom.app X₁ ≫ L'.map t₁ ≫ aB')
  (hδ : δ.map F ≫ t₁⟦(1 : ℤ)⟧' = t₃ ≫ δ')
end

section NormalizedBoundaries
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B') [L.CommShift ℤ] [L'.CommShift ℤ]
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  (θ : L ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ L')
  [NatTrans.CommShift θ.hom ℤ]
  (hθ : ∀ X, ad'.unit.app (F.mapDerivedCategory.obj X) ≫
    R'.mapDerivedCategory.map (θ.inv.app X) =
    F.mapDerivedCategory.map (ad.unit.app X) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X))
  (n : ℕ) (S : ShortComplex A) (S' : ShortComplex A')
  (hS : S.ShortExact) (hS' : S'.ShortExact)
  (H Q : B) (H' Q' : B') (i : R.obj H ⟶ S.X₁) (i' : R'.obj H' ⟶ S'.X₁)
  (wi : i ≫ (n • 𝟙 S.X₁) = 0) (wi' : i' ≫ (n • 𝟙 S'.X₁) = 0)
  (hK : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact)
  (hK' : (ShortComplex.mk i' (n • 𝟙 S'.X₁) wi').ShortExact)
  (p : S.X₃ ⟶ R.obj Q) (p' : S'.X₃ ⟶ R'.obj Q')
  (aF : L.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≅
    (DerivedCategory.singleFunctor B 0).obj Q)
  (aF' : L'.obj ((DerivedCategory.singleFunctor A' 0).obj S'.X₃) ≅
    (DerivedCategory.singleFunctor B' 0).obj Q')
  (aB : L.obj ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≅
    ((DerivedCategory.singleFunctor B 0).obj H)⟦(1 : ℤ)⟧)
  (aB' : L'.obj ((DerivedCategory.singleFunctor A' 0).obj S'.X₁) ≅
    ((DerivedCategory.singleFunctor B' 0).obj H')⟦(1 : ℤ)⟧)
  (huF : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≫
    R.mapDerivedCategory.map aF.hom ≫ (R.mapDerivedCategorySingleFunctor 0).hom.app Q =
    (DerivedCategory.singleFunctor A 0).map p)
  (huF' : ad'.unit.app ((DerivedCategory.singleFunctor A' 0).obj S'.X₃) ≫
    R'.mapDerivedCategory.map aF'.hom ≫ (R'.mapDerivedCategorySingleFunctor 0).hom.app Q' =
    (DerivedCategory.singleFunctor A' 0).map p')
  (huB : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≫
    R.mapDerivedCategory.map aB.hom =
      hK.singleδ ≫ ((R.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(1 : ℤ)⟧' ≫
      (R.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor B 0).obj H))
  (huB' : ad'.unit.app ((DerivedCategory.singleFunctor A' 0).obj S'.X₁) ≫
    R'.mapDerivedCategory.map aB'.hom =
      hK'.singleδ ≫ ((R'.mapDerivedCategorySingleFunctor 0).inv.app H')⟦(1 : ℤ)⟧' ≫
      (R'.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor B' 0).obj H'))
  (f : S' ≅ F.mapShortComplex.obj S) (h : H' ≅ G.obj H) (q : Q' ≅ G.obj Q)
  (hi : i' ≫ f.hom.τ₁ = R'.map h.hom ≫ ρ.inv.app H ≫ F.map i)
  (hp : f.hom.τ₃ ≫ F.map p = p' ≫ R'.map q.hom ≫ ρ.inv.app Q)

end NormalizedBoundaries
