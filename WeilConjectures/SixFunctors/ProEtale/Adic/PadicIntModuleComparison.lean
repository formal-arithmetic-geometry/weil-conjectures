/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Linear.Basic
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-!
# From étale towers of `ℓ`-torsion sheaves to pro-étale towers of `ℤ_ℓ,X`-modules

Let `X` be a scheme, `ℓ` a prime and `Λ` a commutative ring. The functor
`AlgebraicGeometry.ProEtale.comparisonUpperStarAb` sends an étale sheaf of `Λ`-modules `G` to the
abelian sheaf underlying `ν^* G` on `X_proét`. It is exact (it preserves finite limits and all
colimits). When `G` is killed by `ℓⁿ`, so is its image, which is then a `ℤ_ℓ,X`-module
(`AlgebraicGeometry.ProEtale.padicIntModOfTorsion`). Consequently:

* a tower `(Gₙ)` of étale sheaves of `Λ`-modules with `ℓⁿ Gₙ = 0` gives a tower of
  `ℤ_ℓ,X`-modules (`AlgebraicGeometry.ProEtale.comparisonPadicIntModTower`) whose underlying
  tower of abelian sheaves is `ν^* Gₙ`;
* if the transitions of `(Gₙ)` are cokernels of `ℓⁿ`, so are those of the pro-étale tower
  (`AlgebraicGeometry.ProEtale.exists_isColimit_comparisonPadicIntModTower`);
* a morphism of towers whose components have kernels (resp. cokernels) killed by an integer `a`
  gives a morphism of towers of `ℤ_ℓ,X`-modules with the same property
  (`AlgebraicGeometry.ProEtale.zsmul_kernel_ι_comparisonPadicIntModTowerMap_app_eq_zero`,
  `AlgebraicGeometry.ProEtale.zsmul_cokernel_π_comparisonPadicIntModTowerMap_app_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {X Y : C} (f : X ⟶ Y) {k : ℤ}

end CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory Abelian.hasFiniteBiproducts

variable {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u})

/-- The forgetful functor from `Λ`-modules to abelian groups is a left adjoint: it is the
restriction of scalars along `ℤ → Λ` followed by the identification of `ℤ`-modules with abelian
groups. -/
instance isLeftAdjoint_forget₂_moduleCat :
    (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).IsLeftAdjoint := by
  have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  exact inferInstanceAs (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).IsLeftAdjoint

/-- The underlying abelian sheaf functor on pro-étale sheaves of `Λ`-modules preserves colimits:
it is the sheafified postcomposition with the forgetful functor, a left adjoint. -/
instance preservesColimits_sheafCompose_forget₂ :
    PreservesColimitsOfSize.{u + 1, u + 1} (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) := by
  let adj := Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})
  have : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).rightAdjoint :=
    adj.rightAdjoint_preservesLimits
  have : (ProEt.topology X).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).rightAdjoint :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction (ProEt.topology X) adj).isLeftAdjoint
  exact preservesColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- The underlying abelian sheaf functor on pro-étale sheaves of `Λ`-modules preserves finite
limits, limits of sheaves being computed on sections. -/
instance preservesFiniteLimits_sheafCompose_forget₂ :
    PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

variable (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
