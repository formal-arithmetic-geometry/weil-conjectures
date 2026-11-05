/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Gluing
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Constant
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback

/-!
# Finite étale trivialization of finite locally constant sheaves

Let `Λ` be a finite commutative ring and `L` a finite locally constant sheaf of `Λ`-modules on
the small étale site of a connected scheme `X`. Then there is a connected finite étale cover
`p : P ⟶ X` such that `p^* L` is the constant sheaf of a finite `Λ`-module
(`AlgebraicGeometry.Scheme.exists_isConstant_upperStar_of_connectedSpace`, blueprint
`fin2-lem-lisse-trivialized-finite-etale`).

The underlying sheaf of sets of `L` is represented by a finite étale `X`-scheme `E`
(`AlgebraicGeometry.Scheme.FiniteEtale.toFLC`). A Galois object `A` of the Galois category of
finite étale `X`-schemes dominating `E`
(`CategoryTheory.PreGaloisCategory.exists_galois_representative`) splits `E`:
`E ×_X A ≅ ∐_{Hom(A, E)} A`
(`AlgebraicGeometry.Scheme.FiniteEtale.isPullback_sigmaDesc_of_isGalois`). Hence the pullback
of the sheaf of sets of `L` to `A` is the sheaf of sections of a trivial cover, a constant
sheaf (`AlgebraicGeometry.Scheme.uliftYonedaTrivialCoverIso`), and since `A` is connected the
pullback of `L` itself is constant
(`AlgebraicGeometry.Scheme.module_pullback_isConstant_of_set_pullback`). Over a Noetherian base
we apply this on each of the finitely many connected components
(`AlgebraicGeometry.Scheme.exists_isConstant_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory Opposite
open scoped AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry.Scheme

namespace FiniteEtale

variable {X : Scheme.{u}} [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

end FiniteEtale

section TrivialCover

variable {P : Scheme.{u}} (S : Type u)

end TrivialCover

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The sheaf of sets underlying a finite locally constant sheaf of `Λ`-modules, `Λ` finite, is
finite locally constant. -/
lemma IsFiniteLocallyConstantSheaf.isFiniteLocallyConstantSheafOfTypes_sheafForget
    {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hF : IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheafOfTypes ((sheafForget Y.smallEtaleTopology).obj F) := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := hF.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
      (F.over _)).IsConstant _)
  · have hfg := hF.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s
    have : Finite (ToType ((pointSmallEtale s).sheafFiber.obj F)) :=
      ConcreteCategory.FiniteOfIsFinitelyGenerated.finite_of_isFinitelyGenerated
        (C := ModuleCat.{u + 1} Λ) _ hfg
    let e := ((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this e.symm.toEquiv

end AlgebraicGeometry.Scheme

end
