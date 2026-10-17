/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteDerived
public import WeilConjectures.ConstructibleSheaf.FiniteConstantModel
public import WeilConjectures.ConstructibleSheaf.Monoidal

/-!
# Constructibility inputs of the Künneth formula

This file records three constructibility statements used in the proof of the base change theorem
for a pushforward tensored with a flat sheaf (blueprint `lem-kun-0f1j`):

- `AlgebraicGeometry.Scheme.isConstructibleSheaf_constantSheaf` (blueprint
  `lem-kun-constant-constructible`): constant sheaves with finitely generated values are
  constructible;
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_isFinite`
  (blueprint `fin4-thm-finite-morphisms-constructible`): all higher direct images of a
  constructible sheaf along a finite morphism towards a scheme of finite type over a field are
  constructible, and vanish in positive degrees;
- `AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFinite_of_locallyOfFiniteType`
  (blueprint `lem-kun-095r`): the same statement in the form used for the Künneth formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lem-kun-constant-constructible`: constant sheaves are constructible.

For a finitely generated `Λ`-module `M` (for instance a finite `Λ`-module over a Noetherian, or a
finite, ring `Λ`), the constant sheaf `M_X` on the small étale site of a scheme `X` is
constructible: for the trivial stratification it is locally constant, trivialised by the identity
cover, and its stalk at every geometric point is `M`. The blueprint assumes `X` quasi-compact and
quasi-separated, which is not needed here. -/
theorem Scheme.isConstructibleSheaf_constantSheaf {X : Scheme.{u}} (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    IsConstructibleSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  refine IsFiniteLocallyConstantSheaf.isConstructibleSheaf
    { nonempty_locallyConstantDatum :=
        ⟨⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩⟩
      isFinitelyGenerated_sheafFiber := fun Ω _ _ s ↦ ?_ }
  · rw [isConstant_over_iff_upperStar]
    exact Sheaf.isConstant_of_iso _ (X := M) ((Etale.upperStarId _ X).app _)
  · exact ((ModuleCat.isFinitelyGenerated_iff _).2 ‹_›).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm

namespace Etale

variable [Finite Λ]

/-- Blueprint `fin4-thm-finite-morphisms-constructible`: finite morphisms preserve
constructibility.

Let `f : X ⟶ S` be a finite morphism with `S` of finite type over a field `k`, and let `F` be a
constructible sheaf of `Λ`-modules on `X_ét`, `Λ` a finite ring. Then the higher direct images
`R^q f_* F` are constructible on `S_ét` for every `q`, and `R^q f_* F = 0` for `q ≠ 0`
(`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFinite`, blueprint
`lem-fin-finite-morphism`). -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_isFinite {k : Type u} [Field k]
    {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) [IsFinite f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    (∀ q : ℤ, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
      ∀ q : ℤ, q ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  have hz := isZero_homology_rightDerivedLowerStar_singleFunctor_of_isFinite (Λ := Λ) f F
  refine ⟨fun q ↦ ?_, hz⟩
  by_cases hq : q = 0
  · subst hq
    have : IsConstructibleSheaf ((𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj
        ((f)_*[ModuleCat.{u + 1} Λ].obj F)) := (isConstructibleSheaf_lowerStar_of_isFinite aS f F).1
    exact IsConstructibleSheaf.of_iso
      (((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
        ((f)_*[ModuleCat.{u + 1} Λ].obj F)).symm ≪≫
        ((_root_.DerivedCategory.homologyFunctor _ 0).mapIso
          ((Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory _ f).app _ ≪≫
            (((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F)).symm)
  · exact IsConstructibleSheaf.of_isZero (hz q hq)

/-- Blueprint `lem-kun-095r`: pushforward of constructible sheaves along finite morphisms.

Let `k` be a field, `Y` a scheme of finite type over `k`, `f : X ⟶ Y` a finite morphism and `Λ` a
finite ring. If `F` is a constructible sheaf of `Λ`-modules on `X_ét`, then `f_* F` is
constructible on `Y_ét` and `R^q f_* F = 0` for every `q > 0`. The blueprint also assumes `X` of
finite type over `k` and `Λ` killed by an integer invertible in `k`, which is not needed. -/
theorem isConstructibleSheaf_lowerStar_of_isFinite_of_locallyOfFiniteType {k : Type u} [Field k]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsFinite f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    IsConstructibleSheaf ((f)_*[ModuleCat.{u + 1} Λ].obj F) ∧
      ∀ q : ℤ, 0 < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
  isConstructibleSheaf_lowerStar_of_isFinite aY f F

end Etale

end AlgebraicGeometry
