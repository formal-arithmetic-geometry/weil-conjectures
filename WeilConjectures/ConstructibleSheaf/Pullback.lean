/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.UpperLowerStar.Stalk

/-!
# Pullback stability of constructible sheaves

For a morphism of schemes `g : Y ⟶ X`, the pullback `g^*` sends locally constant sheaves to
locally constant sheaves (`AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.upperStar`), finite
sheaves to finite sheaves (`IsFiniteSheaf.upperStar`), finite locally constant sheaves to
finite locally constant sheaves (`IsFiniteLocallyConstantSheaf.upperStar`) and constructible
sheaves to constructible sheaves (`IsConstructibleSheaf.upperStar`); all four notions are
invariant under isomorphism of sheaves.

The trivialising cover of `g^* F` is the pullback of a trivialising cover of `F`: the
restriction of `F` to the site localized at a member `Uᵢ` of the cover is the pullback of `F`
to `Uᵢ` (`AlgebraicGeometry.Scheme.isConstant_over_iff_upperStar`), constancy is preserved by
pullback (`AlgebraicGeometry.Scheme.isConstant_upperStar`), and the two pullbacks to
`Uᵢ ×_X Y` agree by the exchange isomorphism
`AlgebraicGeometry.Etale.upperStarCompIsoOfComm` of the cartesian square. Finiteness is
checked on stalks, which pullback preserves
(`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`), and a stratification pulls back to a
stratification (`AlgebraicGeometry.Scheme.Stratification.pullback`).
(blueprint: `prop:constructible-pullback`)
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Locally constant sheaves are invariant under isomorphism. -/
lemma IsLocallyConstantSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsLocallyConstantSheaf F] : IsLocallyConstantSheaf F' := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  exact ⟨⟨⟨𝒰, fun j ↦
    have := h𝒰 j
    Sheaf.isConstant_congr _ ((X.smallEtaleTopology.overPullback A _).mapIso i)⟩⟩⟩

/-- **Pullback of a locally constant sheaf is locally constant**: the pullback of a
trivialising cover is a trivialising cover.
(blueprint: `lemma:constructible-pullback-locally-constant`) -/
theorem IsLocallyConstantSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsLocallyConstantSheaf F] : IsLocallyConstantSheaf (((g)^*[A]).obj F) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  refine ⟨⟨⟨𝒰.pullback₂ g, fun j ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  have h₁ : (((𝒰.f j)^*[A]).obj F).IsConstant (𝒰.X j).smallEtaleTopology :=
    (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale j) F).mp (h𝒰 j)
  have h₂ : ((((𝒰.f j)^*[A]) ⋙ ((pullback.fst (𝒰.f j) g)^*[A])).obj F).IsConstant
      (Cover.etalePrecoverageToEtale (𝒰.pullback₂ g) j).left.smallEtaleTopology :=
    isConstant_upperStar A _ _
  exact Sheaf.isConstant_congr _ ((Etale.upperStarCompIsoOfComm A pullback.condition).app F)

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [HasColimitsOfSize.{u, u} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Finite sheaves are invariant under isomorphism. -/
lemma IsFiniteSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsFiniteSheaf F] : IsFiniteSheaf F' where
  finite_sheafFiber Ω _ _ s :=
    have := IsFiniteSheaf.finite_sheafFiber (FA := FA) (CA := CA) (F := F) Ω s
    Finite.of_equiv _
      ((CategoryTheory.forget A).mapIso ((pointSmallEtale s).sheafFiber.mapIso i)).toEquiv

end Finite

section FiniteLocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Pullback of a finite sheaf is finite**: the stalks of `g^* F` are stalks of `F`.
(blueprint: `lemma:constructible-pullback-finite`) -/
theorem IsFiniteSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsFiniteSheaf F] : IsFiniteSheaf (((g)^*[A]).obj F) where
  finite_sheafFiber Ω _ _ s :=
    have := IsFiniteSheaf.finite_sheafFiber (FA := FA) (CA := CA) (F := F) Ω (s ≫ g)
    Finite.of_equiv _
      ((CategoryTheory.forget A).mapIso
        ((Etale.upperStarCompSheafFiberIso A g s).app F)).toEquiv.symm

/-- Finite locally constant sheaves are invariant under isomorphism. -/
lemma IsFiniteLocallyConstantSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsFiniteLocallyConstantSheaf F] : IsFiniteLocallyConstantSheaf F' where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_iso i
  toIsFiniteSheaf := IsFiniteSheaf.of_iso i

/-- **Pullback of a finite locally constant sheaf is finite locally constant.** -/
theorem IsFiniteLocallyConstantSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf (((g)^*[A]).obj F) where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.upperStar g F
  toIsFiniteSheaf := IsFiniteSheaf.upperStar g F

end FiniteLocallyConstant

section Constructible

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Constructible sheaves are invariant under isomorphism. -/
lemma IsConstructibleSheaf.of_iso {F F' : Sheaf X.smallEtaleTopology A} (i : F ≅ F')
    [IsConstructibleSheaf F] : IsConstructibleSheaf F' := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification (FA := FA) (CA := CA) (F := F)
  exact ⟨S, fun j ↦
    have := hS j
    IsFiniteLocallyConstantSheaf.of_iso (((S.immersion j)^*[A]).mapIso i)⟩

/-- **Pullback of a constructible sheaf is constructible**: the stratification pulls back, and
the pullback of `F` to a pulled-back stratum is the pullback of the pullback of `F` to the
stratum. (blueprint: `prop:constructible-pullback`) -/
theorem IsConstructibleSheaf.upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [IsConstructibleSheaf F] : IsConstructibleSheaf (((g)^*[A]).obj F) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification (FA := FA) (CA := CA) (F := F)
  refine ⟨S.pullback g, fun j ↦ ?_⟩
  have := hS j
  -- the pullback of `F` to the stratum, further pulled back to the base-changed stratum
  have h : IsFiniteLocallyConstantSheaf
      (((((S.immersion j))^*[A]) ⋙ ((pullback.fst (S.immersion j) g)^*[A])).obj F) :=
    IsFiniteLocallyConstantSheaf.upperStar _ _
  exact IsFiniteLocallyConstantSheaf.of_iso
    ((Etale.upperStarCompIsoOfComm A (pullback.condition (f := S.immersion j) (g := g))).app F)

end Constructible

end AlgebraicGeometry.Scheme

end
