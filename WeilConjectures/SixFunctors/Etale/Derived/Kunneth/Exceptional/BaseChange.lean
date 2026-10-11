/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# The base change Künneth map for the right adjoint of a pushforward

Fix a commutative square of schemes
```
  Y --h--> X'
  |        |
  e        f'
  v        v
  T --g--> S'
```
and an object `M ∈ D(X'_ét)`. Write `E = M ⊗ᴸ Lf'^*(-) : D(S'_ét) ⥤ D(X'_ét)` and
`E' = Lh^*M ⊗ᴸ Le^*(-) : D(T_ét) ⥤ D(Y_ét)`. The monoidality of `Lh^*` and the composition
isomorphisms give `θ : E ⋙ Lh^* ≅ Lg^* ⋙ E'`; its mate along `Lg^* ⊣ Rg_*`, `Lh^* ⊣ Rh_*` is the
base change map `Ku : Rg_* ⋙ E ⟶ E' ⋙ Rh_*` of `lem-kun-0f1n`
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`).

If `Rg_*` and `Rh_*` are left adjoints, with right adjoints `g^×`, `h^×` (for proper `g`, the
exceptional inverse image), and `Ku` is invertible, the mate of `Ku⁻¹` is the *base change
Künneth map*
```
  α : Le^*... :  Lh^*M ⊗ᴸ Le^*(g^× L) ⟶ h^×(M ⊗ᴸ Lf'^* L),
```
the one-sided exceptional Künneth comparison from which `def-sf-kv-maps` (ii) is assembled.

## Main definitions

- `AlgebraicGeometry.Etale.tensorPullback`: `E = M ⊗ᴸ Lf'^*(-)`.
- `AlgebraicGeometry.Etale.tensorPullbackBaseChangeIso`: `θ : E ⋙ Lh^* ≅ Lg^* ⋙ E'`.
- `AlgebraicGeometry.Etale.tensorBaseChangeNatTrans`: `Ku`, the mate of `θ`.
- `AlgebraicGeometry.Etale.lowerStarRightAdjoint`: `g^×`, the right adjoint of `Rg_*`.
- `AlgebraicGeometry.Etale.exceptionalBaseChange`: `α`, the mate of `Ku⁻¹`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

section TensorPullback

variable {X' S' : Scheme.{u}}

/-- The functor `E = M ⊗ᴸ Lf'^*(-) : D(S'_ét) ⥤ D(X'_ét)` for `f' : X' ⟶ S'` and
`M ∈ D(X'_ét)`. -/
noncomputable def tensorPullback (f' : X' ⟶ S') (M : DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X'.smallEtaleTopology A) :=
  L((f')^*[A]) ⋙ (derivedTensor A X').obj M

@[simp]
lemma tensorPullback_obj (f' : X' ⟶ S') (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (tensorPullback A f' M).obj K = ((-⊗ᴸ-(X')[A]).obj M).obj (L((f')^*[A]).obj K) :=
  rfl

@[simp]
lemma tensorPullback_map (f' : X' ⟶ S') (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    {K K' : DerivedCategory (Sheaf S'.smallEtaleTopology A)} (φ : K ⟶ K') :
    (tensorPullback A f' M).map φ = ((-⊗ᴸ-(X')[A]).obj M).map (L((f')^*[A]).map φ) :=
  rfl

end TensorPullback

section Square

variable {Y X' T S' : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
  (w : h ≫ f' = e ≫ g) (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))

/-- The isomorphism `θ : Lh^*(M ⊗ᴸ Lf'^* K) ≅ Lh^* M ⊗ᴸ Le^* Lg^* K`, natural in `K`, for a
commutative square `h ≫ f' = e ≫ g`: the monoidality of `Lh^*` followed by the composition
isomorphisms `Lh^* Lf'^* ≅ L(h ≫ f')^* ≅ Le^* Lg^*`. -/
noncomputable def tensorPullbackBaseChangeIso :
    tensorPullback A f' M ⋙ L((h)^*[A]) ≅
      L((g)^*[A]) ⋙ tensorPullback A e (L((h)^*[A]).obj M) :=
  NatIso.ofComponents
    (fun K ↦ leftDerivedUpperStarTensorIso A h M (L((f')^*[A]).obj K) ≪≫
      ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).mapIso
        ((leftDerivedUpperStarComp A h f').symm.app K ≪≫
          (leftDerivedUpperStarComp A e g (h ≫ f') w).app K))
    (fun {K K'} φ ↦ by
      have h₁ := ((leftDerivedUpperStarComp A h f').inv.naturality φ)
      have h₂ := ((leftDerivedUpperStarComp A e g (h ≫ f') w).hom.naturality φ)
      have h₃ := ((leftDerivedUpperStarTensorComparison A h).app M).naturality
        (L((f')^*[A]).map φ)
      dsimp at h₁ h₂ h₃ ⊢
      simp only [Category.assoc]
      rw [reassoc_of% h₃, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
        ← Functor.map_comp]
      congr 2
      rw [reassoc_of% h₁, h₂])

lemma tensorPullbackBaseChangeIso_hom_app (K : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (tensorPullbackBaseChangeIso A h e f' g w M).hom.app K =
      ((leftDerivedUpperStarTensorComparison A h).app M).app (L((f')^*[A]).obj K) ≫
        ((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).map
          ((leftDerivedUpperStarComp A h f').inv.app K ≫
            (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app K) :=
  rfl

/-- The base change map `Ku : M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_*(Lh^* M ⊗ᴸ Le^* F)` as a natural
transformation `Rg_* ⋙ E ⟶ E' ⋙ Rh_*`: the mate of `θ` along `Lg^* ⊣ Rg_*` and
`Lh^* ⊣ Rh_*`. Its components are `AlgebraicGeometry.Etale.tensorBaseChangeMap`
(`AlgebraicGeometry.Etale.tensorBaseChangeNatTrans_app`). -/
noncomputable def tensorBaseChangeNatTrans :
    R((g)_*[A]) ⋙ tensorPullback A f' M ⟶ tensorPullback A e (L((h)^*[A]).obj M) ⋙ R((h)_*[A]) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction A g) (derivedUpperStarLowerStarAdjunction A h)
    (tensorPullbackBaseChangeIso A h e f' g w M).hom).natTrans

lemma tensorBaseChangeNatTrans_app (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (tensorBaseChangeNatTrans A h e f' g w M).app F = tensorBaseChangeMap A h e f' g w M F := by
  simp [tensorBaseChangeNatTrans, tensorBaseChangeMap, Adjunction.homEquiv_unit,
    tensorPullbackBaseChangeIso_hom_app]

end Square

section RightAdjoint

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [R((g)_*[A]).IsLeftAdjoint]

/-- The right adjoint `g^×` of the derived pushforward `Rg_* : D(X_ét) ⥤ D(Y_ét)`, when it
exists. For `g` proper and torsion coefficients, `Rg_* ≅ Rg_!` and `g^× ≅ Rg^!`. -/
noncomputable def lowerStarRightAdjoint :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (R((g)_*[A])).rightAdjoint

/-- The adjunction `Rg_* ⊣ g^×`. -/
noncomputable def lowerStarRightAdjunction : R((g)_*[A]) ⊣ lowerStarRightAdjoint A g :=
  Adjunction.ofIsLeftAdjoint _

end RightAdjoint

section ExceptionalBaseChange

variable {Y X' T S' : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
  (w : h ≫ f' = e ≫ g) (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
  [R((g)_*[A]).IsLeftAdjoint] [R((h)_*[A]).IsLeftAdjoint]
  [IsIso (tensorBaseChangeNatTrans A h e f' g w M)]

/-- The *base change Künneth map* `α : Lh^* M ⊗ᴸ Le^*(g^× L) ⟶ h^×(M ⊗ᴸ Lf'^* L)`, natural in
`L`, for a commutative square `h ≫ f' = e ≫ g` along which the base change map `Ku` of
`lem-kun-0f1n` is invertible: the mate of `Ku⁻¹` along `Rg_* ⊣ g^×` and `Rh_* ⊣ h^×`.
Equivalently, `α_L` is the transpose along `Rh_* ⊣ h^×` of
`Rh_*(Lh^* M ⊗ᴸ Le^* g^× L) ≅ M ⊗ᴸ Lf'^* Rg_* g^× L ⟶ M ⊗ᴸ Lf'^* L`. -/
noncomputable def exceptionalBaseChange :
    lowerStarRightAdjoint A g ⋙ tensorPullback A e (L((h)^*[A]).obj M) ⟶
      tensorPullback A f' M ⋙ lowerStarRightAdjoint A h :=
  (mateEquiv (lowerStarRightAdjunction A g) (lowerStarRightAdjunction A h)
    (inv (tensorBaseChangeNatTrans A h e f' g w M))).natTrans

end ExceptionalBaseChange

end Etale

end AlgebraicGeometry
