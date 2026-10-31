/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedExactComparison
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorStalk
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatDerivability

/-!
# Exact-derived identification and normalized tensor comparisons

Source: blueprint `sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md`,
second sentence, and the exact-functor convention `def-sfb-left-derived-exact`
(blueprint: lem-sf-exact-derived-tensor-comparison-normalization).

The representative equations use the lax tensorators of `Qh`. On K-flat pairs these
are the inverses of the tensor-model maps in the source. Thus the normalization is
written after postcomposition with the target lax tensorator. The quotient from
complexes to the homotopy category identifies this with the cochain normalization.
-/

@[expose] public section

set_option autoImplicit false

universe uC uD vC vD wC wD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor

/-- The canonical identification of any specified total left derived functor of an exact
strong monoidal functor with its termwise derived functor respects the specified natural
tensor comparisons, provided they have their derived-counit normalizations.

Source: blueprint `def-wf-tensor-product.md`, second sentence, with the convention
`def-sfb-left-derived-exact`
(blueprint: lem-sf-exact-derived-tensor-comparison-normalization).

Proof plan:
1. The exact-flat tensor comparison theorem gives the normalization of `δH`; its lax
   localization tensorators are the inverses of the K-flat tensor-model maps, by
   `lem-sfb-derived-monoidal`. Preservation of K-flat complexes allows the same
   identification on the target side.
2. On K-flat representatives, substitute the counit factorization defining
   `leftDerivedExactComparison` in the normalization of `δL`. Naturality of that
   comparison identifies the right side with the normalization of `δH`. Cancel the
   invertible localization factors and the invertible target tensor-model map.
3. By `lem-sfb-kflat-derivability` every unbounded derived object has a K-flat
   representative. Naturality of `δL`, `δH` and the exact comparison transports the
   equality along the representative isomorphisms to every pair of derived objects.
-/
theorem exactDerived_tensorComparison_normalization
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [HasColimitsOfSize.{0, 0} C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [HasColimitsOfSize.{0, 0} D] [Abelian.HasFunctorialFlatResolution D]
    [HasDerivedCategory.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal] [F.PreservesFlat] [F.PreservesKFlatComplexes]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor γ (HomotopyCategory.quasiIso C (.up ℤ))]
    (δH : (postcompose₂.obj F.mapDerivedCategory).obj (curriedTensor (DerivedCategory C)) ≅
      (((whiskeringLeft₂ (DerivedCategory D)).obj F.mapDerivedCategory).obj
        F.mapDerivedCategory).obj (curriedTensor (DerivedCategory D)))
    (hH : ∀ P Q : HomotopyCategory C (.up ℤ),
      (δH.hom.app (DerivedCategory.Qh.obj P)).app (DerivedCategory.Qh.obj Q) ≫
        (F.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app Q) ≫
        LaxMonoidal.μ (DerivedCategory.Qh (C := D))
          ((F.mapHomotopyCategory (.up ℤ)).obj P) ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
      F.mapDerivedCategory.map (LaxMonoidal.μ (DerivedCategory.Qh (C := C)) P Q) ≫
        F.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
        DerivedCategory.Qh.map
          (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q))
    (δL : (postcompose₂.obj L).obj (curriedTensor (DerivedCategory C)) ≅
      (((whiskeringLeft₂ (DerivedCategory D)).obj L).obj L).obj
        (curriedTensor (DerivedCategory D)))
    (hL : ∀ (P Q : HomotopyCategory C (.up ℤ)),
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P →
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat Q →
      (δL.hom.app (DerivedCategory.Qh.obj P)).app (DerivedCategory.Qh.obj Q) ≫
        (γ.app P ⊗ₘ γ.app Q) ≫
        LaxMonoidal.μ (DerivedCategory.Qh (C := D))
          ((F.mapHomotopyCategory (.up ℤ)).obj P) ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
      L.map (LaxMonoidal.μ (DerivedCategory.Qh (C := C)) P Q) ≫ γ.app (P ⊗ Q) ≫
        DerivedCategory.Qh.map
          (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q))
    (M N : DerivedCategory C) :
    (δL.hom.app M).app N ≫
        ((F.leftDerivedExactComparison L γ).hom.app M ⊗ₘ
          (F.leftDerivedExactComparison L γ).hom.app N) =
      (F.leftDerivedExactComparison L γ).hom.app (M ⊗ N) ≫ (δH.hom.app M).app N := by
  sorry

end CategoryTheory.Functor
