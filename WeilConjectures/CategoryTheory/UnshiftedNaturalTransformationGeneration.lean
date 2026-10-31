/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift

/-! # Detecting an arbitrary natural transformation on shifted generators

Source: the scalar-generator argument for the proper projection formula.
(blueprint: lem-coef-unshifted-natural-transformation-generation).
-/

@[expose] public section
set_option autoImplicit false
universe u v w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

private theorem abelian_five (A : Type*) [Category* A] [Abelian A]
    (H I : C ⥤ A) [H.IsHomological] [I.IsHomological] (τ : H ⟶ I)
    (T : Triangle C) (hT : T ∈ distTriang C)
    [IsIso (τ.app T.obj₁)] [IsIso (τ.app T.obj₂)]
    [IsIso (τ.app (T.obj₁⟦(1 : ℤ)⟧))] [IsIso (τ.app (T.obj₂⟦(1 : ℤ)⟧))] :
    IsIso (τ.app T.obj₃) := by
  let R (J : C ⥤ A) : ComposableArrows A 4 :=
    ComposableArrows.mk₄ (J.map T.mor₁) (J.map T.mor₂) (J.map T.mor₃)
      (J.map T.rotate.rotate.mor₂)
  have hR (J : C ⥤ A) [J.IsHomological] : (R J).Exact := by
    exact ComposableArrows.exact_of_δ₀
      (J.map_distinguished_exact T hT).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (J.map_distinguished_exact T.rotate (rot_of_distTriang _ hT)).exact_toComposableArrows
        (J.map_distinguished_exact T.rotate.rotate
          (rot_of_distTriang _ (rot_of_distTriang _ hT))).exact_toComposableArrows)
  let φ : R H ⟶ R I := ComposableArrows.homMk₄
    (τ.app _) (τ.app _) (τ.app _) (τ.app _) (τ.app _)
    (τ.naturality _) (τ.naturality _) (τ.naturality _) (τ.naturality _)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (hR H) (hR I) φ
    (by dsimp [φ, R]; infer_instance) (by dsimp [φ, R]; infer_instance)
    (by dsimp [φ, R]; infer_instance)
    (by change Mono (τ.app (T.obj₂⟦(1 : ℤ)⟧)); infer_instance)

/-- The four surrounding components of the five-term exact sequence suffice, without
shift compatibility of the natural transformation.
Source: the five lemma and the proper projection scalar-generator argument.
(blueprint: lem-coef-unshifted-natural-transformation-generation).
Proof: apply every additive covariant representable. Exactness on a triangle and its
first two rotations gives an exact five-term sequence. Naturality gives all four
commuting squares, including the connecting morphism itself. The abelian five lemma
makes its middle component invertible. Covariant representables detect isomorphisms. -/
private theorem isIso_app_obj₃_without_commShift (α : F ⟶ G)
    (T : Triangle C) (hT : T ∈ distTriang C)
    [IsIso (α.app T.obj₁)] [IsIso (α.app T.obj₂)]
    [IsIso (α.app (T.obj₁⟦(1 : ℤ)⟧))] [IsIso (α.app (T.obj₂⟦(1 : ℤ)⟧))] :
    IsIso (α.app T.obj₃) := by
  apply isIso_of_yoneda_map_bijective
  intro U
  let τ := Functor.whiskerRight α (preadditiveCoyoneda.obj (Opposite.op U))
  have : IsIso (τ.app T.obj₁) := by dsimp [τ]; infer_instance
  have : IsIso (τ.app T.obj₂) := by dsimp [τ]; infer_instance
  have : IsIso (τ.app (T.obj₁⟦(1 : ℤ)⟧)) := by dsimp [τ]; infer_instance
  have : IsIso (τ.app (T.obj₂⟦(1 : ℤ)⟧)) := by dsimp [τ]; infer_instance
  have hi := abelian_five AddCommGrpCat
    (F ⋙ preadditiveCoyoneda.obj (Opposite.op U))
    (G ⋙ preadditiveCoyoneda.obj (Opposite.op U))
    τ T hT
  have : IsIso ((preadditiveCoyoneda.obj (Opposite.op U)).map (α.app T.obj₃)) := hi
  exact (ConcreteCategory.bijective_of_isIso
    ((preadditiveCoyoneda.obj (Opposite.op U)).map (α.app T.obj₃)))

end CategoryTheory.NatTrans

namespace CategoryTheory

/-- An ordinary natural transformation between exact coproduct-preserving functors
from a module derived category is invertible if it is invertible on every shift of R.
Source: Stacks Tag 09PB, the scalar-generator proof of proper projection.
(blueprint: lem-coef-unshifted-natural-transformation-generation).
Proof: use generation by shifts of the regular module with the strengthened property
that all shifted components are invertible. Shifts preserve coproducts, so naturality
and their universal property give coproduct closure. The preceding five-lemma argument
gives triangle closure, using the hypotheses for the first two vertices and their
shifts. Naturality preserves retracts. Finally use the zero-shift isomorphism. -/
theorem derivedModule_isIso_of_shifted_regular
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {D : Type v} [Category.{w'} D]
    [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : DerivedCategory (ModuleCat.{u} R) ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) F]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) G]
    (α : F ⟶ G)
    (h : ∀ n : ℤ, IsIso (α.app
      (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{0} R)))⟦n⟧)))
    (M : DerivedCategory (ModuleCat.{u} R)) : IsIso (α.app M) := by
  have hM : ∀ n : ℤ, IsIso (α.app (M⟦n⟧)) := by
    apply derivedModuleFreeGeneration.{u, 0} R M
      (fun N ↦ ∀ n : ℤ, IsIso (α.app (N⟦n⟧)))
    · intro n k
      exact (NatTrans.isIso_app_iff_of_iso α
        ((shiftFunctorAdd' _ n k (n + k) rfl).app _)).mp (h (n + k))
    · intro I N S ι hc hN n
      let β := Functor.whiskerLeft (shiftFunctor _ n) α
      have : IsIso (Functor.whiskerLeft (Discrete.functor N) β) := by
        rw [NatTrans.isIso_iff_isIso_app]
        intro i
        exact hN i.as n
      exact isIso_app_coconePt_of_preservesColimit (Discrete.functor N) β
        (Cofan.mk S ι) hc
    · intro T ht h₁ h₂ n
      let β := Functor.whiskerLeft (shiftFunctor _ n) α
      have : IsIso (β.app T.obj₁) := h₁ n
      have : IsIso (β.app T.obj₂) := h₂ n
      have : IsIso (β.app (T.obj₁⟦(1 : ℤ)⟧)) :=
        (NatTrans.isIso_app_iff_of_iso α
          ((shiftFunctorAdd' _ 1 n (1 + n) rfl).app _)).mp (h₁ (1 + n))
      have : IsIso (β.app (T.obj₂⟦(1 : ℤ)⟧)) :=
        (NatTrans.isIso_app_iff_of_iso α
          ((shiftFunctorAdd' _ 1 n (1 + n) rfl).app _)).mp (h₂ (1 + n))
      exact NatTrans.isIso_app_obj₃_without_commShift β T ht
    · intro N P r hP n
      have : IsIso ((Functor.whiskerLeft (shiftFunctor _ n) α).app P) := hP n
      exact NatTrans.isIso_app_of_retract
        (Functor.whiskerLeft (shiftFunctor _ n) α) r
  exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorZero _ ℤ).app M)).mp (hM 0)

end CategoryTheory
