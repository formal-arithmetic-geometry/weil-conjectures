/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.CategoryTheory.Sites.CechInjectiveModule
public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology

/-!
# Étale cohomology of sheaves of modules over any ring

Let `Λ` be a ring and `X` a quasi-compact quasi-separated scheme. For an étale sheaf `G` of
`Λ`-modules on `X`, the derived global sections `Rᵠ Γ(X_ét, G)`, computed in sheaves of
`Λ`-modules, are, as an abelian group, the cohomology of the underlying abelian sheaf
(`AlgebraicGeometry.Etale.forgetRightDerivedSectionsIso`). The forgetful functor is exact and
sends injective sheaves of `Λ`-modules to acyclic abelian sheaves, by the Čech criterion
(`CategoryTheory.Sheaf.subsingleton_H_succ_forget₂_of_injective`); no flatness of `Λ` over `ℤ`
is needed. This applies to `Λ = ℤ/ℓᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The forgetful functor from étale sheaves of `Λ`-modules to abelian étale sheaves. -/
noncomputable abbrev sheafForget₂ :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

instance : (sheafForget₂ Λ X).Additive where
  map_add {_ _ _ _} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

instance preservesFiniteLimits_sheafForget₂ : PreservesFiniteLimits (sheafForget₂ Λ X) := by
  have : PreservesFiniteLimits (sheafForget₂ Λ X ⋙ sheafToPresheaf _ AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance preservesFiniteColimits_sheafForget₂ : PreservesFiniteColimits (sheafForget₂ Λ X) := by
  have hadj := ModuleCat.forget₂CoinduceAdj.{u + 1} Λ
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coinduce.{u + 1} Λ) :=
    hadj.rightAdjoint_preservesLimits
  have : X.smallEtaleTopology.HasSheafCompose (ModuleCat.coinduce.{u + 1} Λ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction X.smallEtaleTopology hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

end AlgebraicGeometry.Etale
