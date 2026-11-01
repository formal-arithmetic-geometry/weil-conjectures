/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNativeClosed
import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomBraidedEvaluation

/-! # Derived braided evaluation for an arbitrary compatible functor
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-etale-braided-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d w z
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

-- Retain named tensor fields instead of expanding the derived bifunctor.
set_option allowUnsafeReducibility true in
attribute [local irreducible] DerivedMonoidal.tensorObjAux
  DerivedMonoidal.whiskerLeftAux DerivedMonoidal.whiskerRightAux

-- Use the coefficient and sheaf braidings fixed in the ordinary derived tensor.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000]
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  ModuleCat.MonoidalCategory.instBraidedCategory

attribute [local implicit_reducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local implicit_reducible]
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

attribute [local irreducible] DerivedCategory.monoidalClosed

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1600000 in
-- Instance conversion compares the fixed native derived tensor and closed data.
set_option maxHeartbeats 1600000 in
-- Instance conversion compares the fixed native derived tensor and closed data.
end WeilConjectures

namespace WeilConjectures

private theorem inverseSquare_iso_congr {C : Type a} [Category.{b} C]
    {D : Type c} [Category.{d} D] (F : C ⥤ D) {P Q : C} {U V : D}
    (e e₁ : P ≅ Q) (e' e'₁ : U ≅ V) (t : U ⟶ F.obj P) (s : V ⟶ F.obj Q)
    (h₁ : e = e₁) (h₂ : e' = e'₁)
    (h : e'₁.inv ≫ t = s ≫ F.map e₁.inv) :
    e'.inv ≫ t = s ≫ F.map e.inv := by
  cases h₁
  cases h₂
  exact h

-- Inline the selected braiding while matching the abstract derived adjunction.

private theorem baseDerivedEvaluation
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type c) [Category.{d} D] [Abelian D] [IsGrothendieckAbelian.{z} D]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} D] [HasDerivedCategory.{z} D]
    [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : DerivedCategory C ⥤ DerivedCategory D) (K M : DerivedCategory C)
    (t : ∀ P Q, F.obj P ⊗ F.obj Q ⟶ F.obj (P ⊗ Q))
    (v : F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (ht : (finiteHomKoszulIso D (F.obj K) (F.obj ((ihom K).obj M))).inv ≫
        t K ((ihom K).obj M) = t ((ihom K).obj M) K ≫
          F.map (finiteHomKoszulIso C K ((ihom K).obj M)).inv)
    (hv : v = (((MonoidalClosed.internalHomAdjunction₂
      (C := DerivedCategory D)).adj (F.obj K)).homEquiv _ _)
      (t K ((ihom K).obj M) ≫ F.map
        (((MonoidalClosed.internalHomAdjunction₂ (C := DerivedCategory C)).adj K).counit.app M))) :
    (finiteHomNativeDerivedClosed D).tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
      (finiteHomNativeDerivedClosed D).evaluation (F.obj K) (F.obj M) =
      t ((ihom K).obj M) K ≫
        F.map ((finiteHomNativeDerivedClosed C).evaluation K M) := by
  letI := finiteHomDerivedBraiding C
  letI := finiteHomDerivedBraiding D
  have hC (P Q : DerivedCategory C) :
      (finiteHomDerivedBraiding C).braiding P Q = finiteHomKoszulIso C P Q :=
    eq_of_heq ((finiteHomDerivedBraiding_existsUnique C).choose_spec.1 P Q)
  have hD (P Q : DerivedCategory D) :
      (finiteHomDerivedBraiding D).braiding P Q = finiteHomKoszulIso D P Q :=
    eq_of_heq ((finiteHomDerivedBraiding_existsUnique D).choose_spec.1 P Q)
  rw [MonoidalClosed.internalHomAdjunction₂_adj,
    MonoidalClosed.internalHomAdjunction₂_adj] at hv
  rw [hv]
  exact finiteHom_braided_evaluation F K M t (by
    exact inverseSquare_iso_congr F _ _ _ _ _ _
      (hC K ((ihom K).obj M)) (hD (F.obj K) (F.obj ((ihom K).obj M))) ht)

/-- An ordinary left-tensor adjunct satisfies native right-tensor evaluation.
Source: blueprint thm-coef-finite-hom, opening evaluation paragraph.
(blueprint: lem-coef-finite-hom-etale-braided-evaluation).

Proof: work first over abstract base categories with their native derived closed
structures. The specified Koszul braid equals the chosen derived braiding by
uniqueness. Rewrite the parameter adjunction to its unary shadow and apply the
generic braided evaluation identity. Specializing the base categories to sheaves
identifies the parameter adjunction with the ordinary etale adjunction by its
definition. Only the displayed braid square and adjunct formula are used. -/
theorem finiteHom_etale_braided_evaluation
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (B : Type b) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u})
    (F : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : ∀ P Q, ((Etale.derivedTensor B X).obj (F.obj P)).obj (F.obj Q) ⟶
      F.obj (((Etale.derivedTensor A X).obj P).obj Q))
    (v : F.obj (((Etale.derivedHom A X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom B X).obj (op (F.obj K))).obj (F.obj M))
    (ht : (finiteHomKoszulIso (Sheaf X.smallEtaleTopology B) (F.obj K)
        (F.obj (((Etale.derivedHom A X).obj (op K)).obj M))).inv ≫
        t K (((Etale.derivedHom A X).obj (op K)).obj M) =
      t (((Etale.derivedHom A X).obj (op K)).obj M) K ≫ F.map
        (finiteHomKoszulIso (Sheaf X.smallEtaleTopology A) K
          (((Etale.derivedHom A X).obj (op K)).obj M)).inv)
    (hv : v = ((Etale.derivedTensorHomAdjunction B (F.obj K)).homEquiv _ _)
      (t K (((Etale.derivedHom A X).obj (op K)).obj M) ≫
        F.map ((Etale.derivedTensorHomAdjunction A K).counit.app M))) :
    (finiteHomNativeDerivedClosed (Sheaf X.smallEtaleTopology B)).tensor.map
        (Prod.mkHom v (𝟙 (F.obj K))) ≫
      (finiteHomNativeDerivedClosed (Sheaf X.smallEtaleTopology B)).evaluation
        (F.obj K) (F.obj M) =
      t (((Etale.derivedHom A X).obj (op K)).obj M) K ≫
        F.map ((finiteHomNativeDerivedClosed (Sheaf X.smallEtaleTopology A)).evaluation K M) := by
  exact baseDerivedEvaluation (Sheaf X.smallEtaleTopology A)
    (Sheaf X.smallEtaleTopology B) F K M t v ht hv

end WeilConjectures
