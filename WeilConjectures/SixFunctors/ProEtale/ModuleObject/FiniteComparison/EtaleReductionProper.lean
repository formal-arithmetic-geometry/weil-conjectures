/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProduct
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekMate

/-!
# Reduction modulo `ℓⁿ`, `Rf_!` and `Rf^!`: stability under composition

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). Say that a morphism `f : Z ⟶ Y` *has a
reduction comparison* if there is an isomorphism `γ : Rf_! ⋙ red_Y ≅ red_Z ⋙ Rf_!` whose
transpose `Rf^! ⋙ red_Z ⟶ red_Y ⋙ Rf^!` under the adjunctions `Rf_! ⊣ Rf^!` is an isomorphism
(`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso`). Closed immersions have one
(`ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso`).

This file shows that the property is stable under composition
(`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso.comp`): with the composition
isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on both sides, the stacked square of `γ_f` and `γ_g`
has invertible transpose (`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`).
This is the composition step of blueprint `det-prop-scalar-six-exceptional` ("compatibility
with composition"), in the weak form of `exists_etaleReductionLowerShriekIso` (no identification
of `γ` with the canonical comparison).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- A morphism `f : Z ⟶ Y` *has a reduction comparison for `Rf_!` and `Rf^!`*: there is an
isomorphism `γ : Rf_! ⋙ red_Y ≅ red_Z ⋙ Rf_!` whose transpose under `Rf_! ⊣ Rf^!` is an
isomorphism. This is the conclusion of `exists_etaleReductionLowerShriekIso`. -/
def HasEtaleReductionLowerShriekIso {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : Z ⟶ Y) : Prop :=
  have := HasCompactification.of_over f
  ∃ γ : boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
      etaleReduction ℓ E n Y ≅
    etaleReduction ℓ E n Z ⋙
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left,
    IsIso (mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γ.inv))

variable {X Y S : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- Closed immersions have a reduction comparison for `Rf_!` and `Rf^!`
(`exists_etaleReductionLowerShriekIso`). -/
theorem hasEtaleReductionLowerShriekIso_of_isClosedImmersion (f : X ⟶ Y) [IsProper f.left]
    [IsClosedImmersion f.left] : HasEtaleReductionLowerShriekIso ℓ E n f :=
  exists_etaleReductionLowerShriekIso ℓ E n f

/-- **Reduction comparisons compose**: if `f` and `g` have a reduction comparison for the
lower and upper shrieks, so does `f ≫ g`. The comparison for `f ≫ g` is the stacked square of
those for `f` and `g`, transported along the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (`boundedConstructibleLowerShriekComp_padicIntegers` and
`Etale.nonempty_iso_rightDerivedLowerShriek_comp`); its transpose is invertible by
`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`. -/
theorem HasEtaleReductionLowerShriekIso.comp {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : HasEtaleReductionLowerShriekIso ℓ E n f)
    (hg : HasEtaleReductionLowerShriekIso ℓ E n g) :
    HasEtaleReductionLowerShriekIso ℓ E n (f ≫ g) := by
  have := HasCompactification.of_over f
  have := HasCompactification.of_over g
  have := HasCompactification.of_over (f ≫ g)
  obtain ⟨γf, hγf⟩ := hf
  obtain ⟨γg, hγg⟩ := hg
  obtain ⟨e'⟩ := Etale.nonempty_iso_rightDerivedLowerShriek_comp
    (integersModPowCoeff.{u} ℓ E n) f.left g.left
  let sqf := TwoSquare.mk _ _ _ _ γf.inv
  let sqg := TwoSquare.mk _ _ _ _ γg.inv
  let c := boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g
  let sq := ((sqf.vComp sqg).whiskerLeft c.inv).whiskerRight e'.hom
  have : IsIso sq.natTrans := by
    have : IsIso sqf.natTrans := inferInstanceAs (IsIso γf.inv)
    have : IsIso sqg.natTrans := inferInstanceAs (IsIso γg.inv)
    have := sqf.isIso_vComp sqg
    have := (sqf.vComp sqg).isIso_whiskerLeft c.inv
    exact ((sqf.vComp sqg).whiskerLeft c.inv).isIso_whiskerRight e'.hom
  refine ⟨(asIso sq.natTrans).symm, ?_⟩
  exact isIso_mateEquiv_vComp_whiskerLeft_whiskerRight
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (boundedConstructibleUpperShriekAdjunction _ ℓ g)
    (Etale.rightDerivedUpperShriekAdjunction _ g.left)
    (boundedConstructibleUpperShriekAdjunction _ ℓ (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction _ (f ≫ g).left)
    (boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g) e' _ _

/-! ### Reduction of the proper case to projections -/

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
/-- **Graph factorization of a proper morphism**: a proper `f : X ⟶ Y` of separated `k`-schemes of
finite type is a closed immersion `X ⟶ P ×_k Y` followed by the second projection, for some
proper `k`-scheme `P`. Take a compactification `X ⟶[j] P ⟶ Spec k` of `X` (Nagata) and the
graph `(j, f)`: it is proper, its composite with the separated projection to `Y` being `f`, and
a monomorphism, its composite with the projection to `P` being the open immersion `j`. -/
theorem exists_isClosedImmersion_comp_overProdSnd (f : X ⟶ Y) [IsProper f.left] :
    ∃ (P : Over (Spec (.of k))) (_ : IsProper P.hom) (i : X ⟶ overProd P Y),
      IsClosedImmersion i.left ∧ i ≫ overProdSnd P Y = f := by
  let c := HasCompactification.compactification X.hom
  have := c.isProper
  have := c.isOpenImmersion
  have hc : c.i ≫ c.g = X.hom := c.comm.symm
  let i : X ⟶ overProd (Over.mk c.g) Y :=
    Over.homMk (pullback.lift c.i f.left (by simp [hc])) (by simp [overProd])
  have hi₁ : i.left ≫ pullback.fst c.g Y.hom = c.i := by simp [i]
  have hi₂ : i.left ≫ pullback.snd c.g Y.hom = f.left := by simp [i]
  refine ⟨Over.mk c.g, c.isProper, i, ?_, ?_⟩
  · rw [IsClosedImmersion.iff_isProper_and_mono]
    have : IsProper (i.left ≫ pullback.snd c.g Y.hom) := by
      rw [hi₂]
      infer_instance
    refine ⟨IsProper.of_comp i.left (pullback.snd c.g Y.hom), ?_⟩
    have : Mono (i.left ≫ pullback.fst c.g Y.hom) := by
      rw [hi₁]
      infer_instance
    exact mono_of_mono _ (pullback.fst c.g Y.hom)
  · ext1
    simpa [overProdSnd] using hi₂

/-- **Reduction of the proper case to projections**: if the second projections
`P ×_k Y ⟶ Y`, for `P` proper over `k`, have a reduction comparison for the lower and upper
shrieks, so does every proper `f : X ⟶ Y`. Indeed `f` is a closed immersion followed by such a
projection (`exists_isClosedImmersion_comp_overProdSnd`), closed immersions have a reduction
comparison (`exists_etaleReductionLowerShriekIso`), and reduction comparisons compose
(`HasEtaleReductionLowerShriekIso.comp`). -/
theorem hasEtaleReductionLowerShriekIso_of_isProper
    (hpr : ∀ (P : Over (Spec (.of k))) [IsProper P.hom],
      HasEtaleReductionLowerShriekIso ℓ E n (overProdSnd P Y))
    (f : X ⟶ Y) [IsProper f.left] : HasEtaleReductionLowerShriekIso ℓ E n f := by
  obtain ⟨P, _, i, hi, rfl⟩ := exists_isClosedImmersion_comp_overProdSnd f
  have : IsProper i.left := ((IsClosedImmersion.iff_isProper_and_mono i.left).1 hi).1
  exact (hasEtaleReductionLowerShriekIso_of_isClosedImmersion ℓ E n i).comp ℓ E n (hpr P)


/-- `exists_etaleReductionLowerShriekIso` for a proper `f`, assuming it for the second
projections `P ×_k Y ⟶ Y` with `P` proper over `k`
(`hasEtaleReductionLowerShriekIso_of_isProper`). -/
theorem exists_etaleReductionLowerShriekIso_of_isProper
    (hpr : ∀ (P : Over (Spec (.of k))) [IsProper P.hom],
      HasEtaleReductionLowerShriekIso ℓ E n (overProdSnd P Y))
    (f : X ⟶ Y) [IsProper f.left] :
    ∃ γ : boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
        etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left,
      IsIso (mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ f)
        (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γ.inv)) :=
  hasEtaleReductionLowerShriekIso_of_isProper ℓ E n hpr f

end AlgebraicGeometry.ProEtale.CondensedRing
