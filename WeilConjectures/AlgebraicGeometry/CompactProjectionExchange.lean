/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-!
# Coefficient-first compact-support projection maps commute with etale exchange

The compact-support projection map is taken with the coefficient first: the upstream
right-coefficient projection map `AlgebraicGeometry.Etale.projectionMap` (proper projection
of the compactification followed by the inverse open tensor comparison) conjugated by the
canonical signed derived symmetry `AlgebraicGeometry.Etale.derivedTensorSymmetry`. The exchange
map is the upstream
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`. The upstream theorem
`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap` is the
right-coefficient form of the statement.

## Main declarations

- `AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst`: the map
  `Π_{f,Q,M} : Q ⊗ᴸ Rf_!M ⟶ Rf_!(Lf^*Q ⊗ᴸ M)`.
- `AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst_baseChangeMap`: the statement.

## References

* Stacks Project, Tags 0E48, 0GL1 and 03S6
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

private lemma symmetryPasting
    {C : Type*} [Category C]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ O₁₃ : C}
    (a : O₀ ⟶ O₁) (p : O₁ ⟶ O₂) (s : O₂ ⟶ O₃)
    (b₁ : O₃ ⟶ O₄) (t₁ : O₄ ⟶ O₅) (d₁ : O₅ ⟶ O₆)
    (b₀ : O₂ ⟶ O₇) (s' : O₇ ⟶ O₄) (t₀ : O₇ ⟶ O₈) (d₀ : O₈ ⟶ O₉)
    (σ : O₉ ⟶ O₆) (c₀ : O₁ ⟶ O₁₀) (e₀ : O₁₀ ⟶ O₁₁) (p' : O₁₁ ⟶ O₉)
    (c₁ : O₀ ⟶ O₁₂) (σ₀ : O₁₂ ⟶ O₁₀) (e₁ : O₁₂ ⟶ O₁₃) (σ₁ : O₁₃ ⟶ O₁₁)
    (hb : s ≫ b₁ = b₀ ≫ s')
    (hx : s' ≫ t₁ ≫ d₁ = t₀ ≫ d₀ ≫ σ)
    (h : p ≫ b₀ ≫ t₀ ≫ d₀ = c₀ ≫ e₀ ≫ p')
    (hy : a ≫ c₀ = c₁ ≫ σ₀)
    (hs : e₁ ≫ σ₁ = σ₀ ≫ e₀) :
    a ≫ p ≫ s ≫ b₁ ≫ t₁ ≫ d₁ = c₁ ≫ e₁ ≫ σ₁ ≫ p' ≫ σ := by
  rw [reassoc_of% hb, hx, reassoc_of% h, reassoc_of% hy,
    ← reassoc_of% hs]

private lemma coefficientFirstExchange
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (T' : C' ⥤ C' ⥤ C') (S' : D' ⥤ D' ⥤ D')
    (σ : T ⟶ T.flip) (σ' : T' ⟶ T'.flip)
    (τ : S ⟶ S.flip) (τ' : S' ⟶ S'.flip)
    (F : C ⥤ D) (F' : C' ⥤ D') (G : D ⥤ D') (U : C ⥤ C')
    (b : F ⋙ G ⟶ U ⋙ F') (M N : C) (Q : D) (N' : C') (θ : U.obj N ⟶ N')
    (p : (S.obj (F.obj M)).obj Q ⟶ F.obj ((T.obj M).obj N))
    (p' : (S'.obj (F'.obj (U.obj M))).obj (G.obj Q) ⟶
      F'.obj ((T'.obj (U.obj M)).obj N'))
    (t₀ : G.obj ((S.obj (F.obj M)).obj Q) ⟶ (S'.obj (G.obj (F.obj M))).obj (G.obj Q))
    (t₁ : G.obj ((S.obj Q).obj (F.obj M)) ⟶ (S'.obj (G.obj Q)).obj (G.obj (F.obj M)))
    (u₀ : U.obj ((T.obj M).obj N) ⟶ (T'.obj (U.obj M)).obj (U.obj N))
    (u₁ : U.obj ((T.obj N).obj M) ⟶ (T'.obj (U.obj N)).obj (U.obj M))
    (h : G.map p ≫ b.app ((T.obj M).obj N) ≫ F'.map u₀ ≫
        F'.map ((T'.obj (U.obj M)).map θ) =
      t₀ ≫ ((S'.map (b.app M)).app (G.obj Q)) ≫ p')
    (hx : U.map ((σ.app M).app N) ≫ u₁ =
      u₀ ≫ (σ'.app (U.obj M)).app (U.obj N))
    (hy : G.map ((τ.app Q).app (F.obj M)) ≫ t₀ =
      t₁ ≫ (τ'.app (G.obj Q)).app (G.obj (F.obj M))) :
    G.map ((τ.app Q).app (F.obj M) ≫ p ≫ F.map ((σ.app M).app N)) ≫
        b.app ((T.obj N).obj M) ≫ F'.map u₁ ≫ F'.map ((T'.map θ).app (U.obj M)) =
      t₁ ≫ (S'.obj (G.obj Q)).map (b.app M) ≫
        (τ'.app (G.obj Q)).app (F'.obj (U.obj M)) ≫ p' ≫
          F'.map ((σ'.app (U.obj M)).app N') := by
  have hb := b.naturality ((σ.app M).app N)
  simp only [Functor.comp_map, Functor.comp_obj] at hb
  have hn := (σ'.app (U.obj M)).naturality θ
  have hs := (τ'.app (G.obj Q)).naturality (b.app M)
  have hx₁ : U.map ((σ.app M).app N) ≫ u₁ ≫ (T'.map θ).app (U.obj M) =
      u₀ ≫ (T'.obj (U.obj M)).map θ ≫ (σ'.app (U.obj M)).app N' := by
    rw [reassoc_of% hx]
    exact congrArg (u₀ ≫ ·) hn.symm
  have hx₂ := F'.congr_map hx₁
  simp only [Functor.map_comp] at hx₂
  simp only [Functor.map_comp, Category.assoc]
  exact symmetryPasting _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hx₂ h hy hs

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local irreducible] derivedTensorSymmetry

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- As in the upstream module `LowerShriekProjectionExchange`: search the braiding of
-- `ModuleCat Λ` through its symmetric structure, so that the monoidal structures agree.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

/-- The canonical compact-support projection map with the coefficient first,
`Π_{f,Q,M} : Q ⊗ᴸ Rf_!M ⟶ Rf_!(Lf^*Q ⊗ᴸ M)`: the signed symmetry, the projection map
`projectionMap` of the chosen compactification (proper counit-defined projection map followed
by the inverse extension-by-zero tensor comparison), and `Rf_!` of the signed symmetry
(Stacks, Tag 0GL1). -/
noncomputable def compactProjectionMapCoeffFirst {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj Q).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ⟶
      (R(f)_![ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app Q).app
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ≫
    ((projectionMap _ f).app M).app Q ≫
    (R(f)_![ModuleCat.{u + 1} Λ]).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app M).app
        (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q))

attribute [local irreducible] compactProjectionMapCoeffFirst

/-- **Compact-support projection maps commute with etale exchange.** For a cartesian square
`g' ≫ f = f' ≫ g` with `f` and `f'` compactifiable and finite commutative coefficients, the
projection maps `Π` satisfy
`b ∘ Lg^*(Π_{f,Q,M}) = Π_{f',Lg^*Q,Lg'^*M} ∘ (1 ⊗ b_M)` up to the tensor comparisons, where
`b` is `rightDerivedLowerShriekBaseChangeMap` (Stacks, Tags 0E48, 0GL1 and 03S6). -/
theorem compactProjectionMapCoeffFirst_baseChangeMap
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (compactProjectionMapCoeffFirst Λ f Q M) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)).obj M) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison _ g').app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)).app M) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).map
            (derivedSquareUpperStarIsoInvApp _ sq.toCommSq Q)).app
              (L((g')^*[ModuleCat.{u + 1} Λ]).obj M)) =
      ((leftDerivedUpperStarTensorComparison _ g).app Q).app
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ≫
        ((-⊗ᴸ-(Y')[ModuleCat.{u + 1} Λ]).obj (L((g)^*[ModuleCat.{u + 1} Λ]).obj Q)).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq).app M) ≫
        compactProjectionMapCoeffFirst Λ f' (L((g)^*[ModuleCat.{u + 1} Λ]).obj Q)
          (L((g')^*[ModuleCat.{u + 1} Λ]).obj M) := by
  have hp := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq M Q
  unfold compactProjectionMapCoeffFirst
  refine coefficientFirstExchange
    (derivedTensor (ModuleCat.{u + 1} Λ) X) (derivedTensor (ModuleCat.{u + 1} Λ) Y)
    (derivedTensor (ModuleCat.{u + 1} Λ) X') (derivedTensor (ModuleCat.{u + 1} Λ) Y')
    (derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom
    (derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X').hom
    (derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom
    (derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y').hom
    R(f)_![ModuleCat.{u + 1} Λ] R(f')_![ModuleCat.{u + 1} Λ]
    L((g)^*[ModuleCat.{u + 1} Λ]) L((g')^*[ModuleCat.{u + 1} Λ])
    (rightDerivedLowerShriekBaseChangeMap Λ sq)
    M (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q) Q
    (L((f')^*[ModuleCat.{u + 1} Λ]).obj (L((g)^*[ModuleCat.{u + 1} Λ]).obj Q))
    (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq Q)
    (((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app Q)
    (((projectionMap (ModuleCat.{u + 1} Λ) f').app
      (L((g')^*[ModuleCat.{u + 1} Λ]).obj M)).app (L((g)^*[ModuleCat.{u + 1} Λ]).obj Q))
    (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) g).app
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)).app Q)
    (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) g).app Q).app
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj M))
    (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) g').app M).app
      (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q))
    (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) g').app
      (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)).app M)
    ?_ ?_ ?_
  · exact hp
  · exact derivedPullback_tensorSymmetry Λ g' M (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)
  · exact derivedPullback_tensorSymmetry Λ g Q ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)

end Etale

end AlgebraicGeometry
