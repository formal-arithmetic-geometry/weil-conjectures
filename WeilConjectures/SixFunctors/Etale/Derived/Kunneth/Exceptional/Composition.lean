/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.Mates

/-!
# Composition of base change Künneth maps

For two commutative squares pasted vertically,
```
  Y --h₁--> Y₂ --h₂--> X'
  |e        |f₂        |f'
  v         v          v
  T --g₁--> T₂ --g₂--> S'
```
the isomorphism `θ` of `AlgebraicGeometry.Etale.tensorPullbackBaseChangeIso` of the outer square
is the pasting of those of the two inner squares
(`AlgebraicGeometry.Etale.tensorPullbackBaseChangeIso_hom_app_comp`). By the calculus of mates
(`CategoryTheory.mateEquiv_app_of_vComp`, `CategoryTheory.mateEquiv_inv_app_comp`), the base
change maps `Ku` and the base change Künneth maps `α` paste as well
(`AlgebraicGeometry.Etale.exceptionalBaseChange_app_comp`): up to the composition isomorphisms,
`α_{g₁ ≫ g₂} = h₁^×(α_{g₂}) ∘ α_{g₁}(g₂^× -)`.

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

/-- The functor `E = M ⊗ᴸ Lf'^*(-)` is functorial in isomorphisms `M ≅ M'`. -/
noncomputable def tensorPullbackIsoOfIso {X' S' : Scheme.{u}} (f' : X' ⟶ S')
    {M M' : DerivedCategory (Sheaf X'.smallEtaleTopology A)} (i : M ≅ M') :
    tensorPullback A f' M ≅ tensorPullback A f' M' :=
  Functor.isoWhiskerLeft L((f')^*[A]) ((derivedTensor A X').mapIso i)

@[simp]
lemma tensorPullbackIsoOfIso_hom_app {X' S' : Scheme.{u}} (f' : X' ⟶ S')
    {M M' : DerivedCategory (Sheaf X'.smallEtaleTopology A)} (i : M ≅ M')
    (K : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (tensorPullbackIsoOfIso A f' i).hom.app K =
      ((derivedTensor A X').map i.hom).app (L((f')^*[A]).obj K) :=
  rfl

variable {Y Y₂ X' T T₂ S' : Scheme.{u}} (h₁ : Y ⟶ Y₂) (h₂ : Y₂ ⟶ X') (e : Y ⟶ T)
  (f₂ : Y₂ ⟶ T₂) (f' : X' ⟶ S') (g₁ : T ⟶ T₂) (g₂ : T₂ ⟶ S') (w₁ : h₁ ≫ f₂ = e ≫ g₁)
  (w₂ : h₂ ≫ f' = f₂ ≫ g₂)

include w₁ w₂ in
lemma comp_comm_of_comm : (h₁ ≫ h₂) ≫ f' = e ≫ g₁ ≫ g₂ := by
  rw [Category.assoc, w₂, reassoc_of% w₁]

/-- The pseudofunctoriality of the derived pullback, in the form needed to paste the
isomorphisms `θ`. -/
lemma leftDerivedUpperStarComp_paste (K : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A h₁ h₂).hom.app (L((f')^*[A]).obj K) ≫
      L((h₁)^*[A]).map ((leftDerivedUpperStarComp A h₂ f').inv.app K ≫
        (leftDerivedUpperStarComp A f₂ g₂ (h₂ ≫ f') w₂).hom.app K) ≫
      (leftDerivedUpperStarComp A h₁ f₂).inv.app (L((g₂)^*[A]).obj K) ≫
      (leftDerivedUpperStarComp A e g₁ (h₁ ≫ f₂) w₁).hom.app (L((g₂)^*[A]).obj K) ≫
      L((e)^*[A]).map ((leftDerivedUpperStarComp A g₁ g₂).inv.app K) =
    (leftDerivedUpperStarComp A (h₁ ≫ h₂) f').inv.app K ≫
      (leftDerivedUpperStarComp A e (g₁ ≫ g₂) ((h₁ ≫ h₂) ≫ f')
        (comp_comm_of_comm h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂)).hom.app K := by
  rw [Functor.map_comp, ← Category.assoc ((leftDerivedUpperStarComp A h₁ h₂).hom.app _),
    leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app A h₁ h₂ f'
      (h₁ ≫ h₂) (h₂ ≫ f') ((h₁ ≫ h₂) ≫ f') rfl rfl rfl K]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc ((leftDerivedUpperStarComp A h₁ (h₂ ≫ f') _ _).hom.app K),
    leftDerivedUpperStarComp_assoc'_app A h₁ f₂ g₂ (h₁ ≫ f₂) (h₂ ≫ f') ((h₁ ≫ h₂) ≫ f') rfl w₂
      (by rw [Category.assoc, w₂, ← Category.assoc]) K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc ((leftDerivedUpperStarComp A (h₁ ≫ f₂) g₂ _ _).hom.app K),
    leftDerivedUpperStarComp_assoc'_app A e g₁ g₂ (h₁ ≫ f₂) (g₁ ≫ g₂) ((h₁ ≫ h₂) ≫ f') w₁ rfl
      (by rw [Category.assoc, w₂, ← Category.assoc]) K]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    Category.comp_id]

variable (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))

/-- **Pasting of the isomorphisms `θ`.** For two commutative squares pasted vertically, the
isomorphism `θ` of the outer square is that of the lower right square, pulled back along `h₁`,
followed by that of the upper left square, up to the composition isomorphisms. -/
lemma tensorPullbackBaseChangeIso_hom_app_comp
    (K : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (tensorPullbackBaseChangeIso A (h₁ ≫ h₂) e f' (g₁ ≫ g₂)
        (comp_comm_of_comm h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂) M).hom.app K =
      (leftDerivedUpperStarComp A h₁ h₂).hom.app ((tensorPullback A f' M).obj K) ≫
        L((h₁)^*[A]).map ((tensorPullbackBaseChangeIso A h₂ f₂ f' g₂ w₂ M).hom.app K) ≫
        (tensorPullbackBaseChangeIso A h₁ e f₂ g₁ w₁ (L((h₂)^*[A]).obj M)).hom.app
          (L((g₂)^*[A]).obj K) ≫
        (tensorPullback A e (L((h₁)^*[A]).obj (L((h₂)^*[A]).obj M))).map
          ((leftDerivedUpperStarComp A g₁ g₂).inv.app K) ≫
        (tensorPullbackIsoOfIso A e ((leftDerivedUpperStarComp A h₁ h₂).app M).symm).hom.app
          (L((g₁ ≫ g₂)^*[A]).obj K) := by
  have hc := leftDerivedUpperStarComp_paste A h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂ K
  have hμ := leftDerivedUpperStarTensorComparison_comp A h₁ h₂ (h₁ ≫ h₂) rfl M
    (L((f')^*[A]).obj K)
  have hn := ((leftDerivedUpperStarTensorComparison A h₁).app (L((h₂)^*[A]).obj M)).naturality
    ((leftDerivedUpperStarComp A h₂ f').inv.app K ≫
      (leftDerivedUpperStarComp A f₂ g₂ (h₂ ≫ f') w₂).hom.app K)
  simp only [tensorPullbackBaseChangeIso_hom_app, tensorPullback_obj, tensorPullback_map,
    tensorPullbackIsoOfIso_hom_app, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc] at hc hμ hn ⊢
  dsimp [derivedTensor] at hμ hn ⊢
  trace_state
  sorry

/-- The isomorphism `R(g₁ ≫ g₂)_* ⟶ Rg₁_* ⋙ Rg₂_*`, the conjugate of the composition isomorphism
of the derived pullbacks along the derived adjunctions `Lg^* ⊣ Rg_*`. -/
noncomputable def lowerStarCompConj {T T₂ S' : Scheme.{u}} (g₁ : T ⟶ T₂) (g₂ : T₂ ⟶ S') :
    R((g₁ ≫ g₂)_*[A]) ⟶ R((g₁)_*[A]) ⋙ R((g₂)_*[A]) :=
  conjugateEquiv (derivedUpperStarLowerStarAdjunction A (g₁ ≫ g₂))
    ((derivedUpperStarLowerStarAdjunction A g₂).comp (derivedUpperStarLowerStarAdjunction A g₁))
    (leftDerivedUpperStarComp A g₁ g₂).inv

instance {T T₂ S' : Scheme.{u}} (g₁ : T ⟶ T₂) (g₂ : T₂ ⟶ S') :
    IsIso (lowerStarCompConj A g₁ g₂) := by
  unfold lowerStarCompConj
  infer_instance

/-- **Pasting of the base change maps `Ku`.** -/
lemma tensorBaseChangeNatTrans_app_comp (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (tensorBaseChangeNatTrans A (h₁ ≫ h₂) e f' (g₁ ≫ g₂)
        (comp_comm_of_comm h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂) M).app F =
      (tensorPullback A f' M).map ((lowerStarCompConj A g₁ g₂).app F) ≫
        (tensorBaseChangeNatTrans A h₂ f₂ f' g₂ w₂ M).app (R((g₁)_*[A]).obj F) ≫
        R((h₂)_*[A]).map ((tensorBaseChangeNatTrans A h₁ e f₂ g₁ w₁
          (L((h₂)^*[A]).obj M)).app F) ≫
        (inv (lowerStarCompConj A h₁ h₂)).app _ ≫
        R((h₁ ≫ h₂)_*[A]).map ((tensorPullbackIsoOfIso A e
          ((leftDerivedUpperStarComp A h₁ h₂).app M).symm).hom.app F) := by
  have := mateEquiv_app_of_vComp (derivedUpperStarLowerStarAdjunction A g₁)
    (derivedUpperStarLowerStarAdjunction A g₂) (derivedUpperStarLowerStarAdjunction A (g₁ ≫ g₂))
    (derivedUpperStarLowerStarAdjunction A h₁) (derivedUpperStarLowerStarAdjunction A h₂)
    (derivedUpperStarLowerStarAdjunction A (h₁ ≫ h₂)) (leftDerivedUpperStarComp A g₁ g₂)
    (leftDerivedUpperStarComp A h₁ h₂)
    (tensorPullbackIsoOfIso A e ((leftDerivedUpperStarComp A h₁ h₂).app M).symm)
    (tensorPullbackBaseChangeIso A h₁ e f₂ g₁ w₁ (L((h₂)^*[A]).obj M)).hom
    (tensorPullbackBaseChangeIso A h₂ f₂ f' g₂ w₂ M).hom
    (tensorPullbackBaseChangeIso A (h₁ ≫ h₂) e f' (g₁ ≫ g₂)
      (comp_comm_of_comm h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂) M).hom
    (tensorPullbackBaseChangeIso_hom_app_comp A h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂ M) F
  rw [tensorBaseChangeNatTrans, this]
  congr 3
  rw [← cancel_mono ((lowerStarCompConj A h₁ h₂).app _), IsIso.inv_hom_id_app]
  -- the conjugates of `cQ.hom` and of `cQ.inv` are inverse to each other
  rw [lowerStarCompConj, ← NatTrans.comp_app, ← conjugateEquiv_comp]
  simp

variable [R((g₁)_*[A]).IsLeftAdjoint] [R((g₂)_*[A]).IsLeftAdjoint]
  [R((g₁ ≫ g₂)_*[A]).IsLeftAdjoint] [R((h₁)_*[A]).IsLeftAdjoint] [R((h₂)_*[A]).IsLeftAdjoint]
  [R((h₁ ≫ h₂)_*[A]).IsLeftAdjoint]
  [IsIso (tensorBaseChangeNatTrans A h₁ e f₂ g₁ w₁ (L((h₂)^*[A]).obj M))]
  [IsIso (tensorBaseChangeNatTrans A h₂ f₂ f' g₂ w₂ M)]
  [IsIso (tensorBaseChangeNatTrans A (h₁ ≫ h₂) e f' (g₁ ≫ g₂)
    (comp_comm_of_comm h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂) M)]

/-- **Composition of base change Künneth maps.** For two commutative squares pasted vertically,
the base change Künneth map of the outer square is, up to the composition isomorphisms
`g₂^× ⋙ g₁^× ≅ (g₁ ≫ g₂)^×`, `(h₁ ≫ h₂)^× ≅ h₂^× ⋙ h₁^×` and `L(h₁ ≫ h₂)^* M ≅ Lh₁^* Lh₂^* M`,
the composite `h₁^×(α_{g₂}) ∘ α_{g₁}(g₂^× -)`. -/
theorem exceptionalBaseChange_app_comp (L : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (exceptionalBaseChange A h₁ e f₂ g₁ w₁ (L((h₂)^*[A]).obj M)).app
        ((lowerStarRightAdjoint A g₂).obj L) ≫
      (lowerStarRightAdjoint A h₁).map ((exceptionalBaseChange A h₂ f₂ f' g₂ w₂ M).app L) =
    (tensorPullback A e (L((h₁)^*[A]).obj (L((h₂)^*[A]).obj M))).map
        ((conjugateEquiv ((lowerStarRightAdjunction A g₁).comp (lowerStarRightAdjunction A g₂))
          (lowerStarRightAdjunction A (g₁ ≫ g₂)) (lowerStarCompConj A g₁ g₂)).app L) ≫
      (tensorPullbackIsoOfIso A e ((leftDerivedUpperStarComp A h₁ h₂).app M).symm).hom.app _ ≫
      (exceptionalBaseChange A (h₁ ≫ h₂) e f' (g₁ ≫ g₂)
        (comp_comm_of_comm h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂) M).app L ≫
      (conjugateEquiv (lowerStarRightAdjunction A (h₁ ≫ h₂))
        ((lowerStarRightAdjunction A h₁).comp (lowerStarRightAdjunction A h₂))
        (inv (lowerStarCompConj A h₁ h₂))).app _ :=
  mateEquiv_inv_app_comp (lowerStarRightAdjunction A g₁) (lowerStarRightAdjunction A g₂)
    (lowerStarRightAdjunction A (g₁ ≫ g₂)) (lowerStarRightAdjunction A h₁)
    (lowerStarRightAdjunction A h₂) (lowerStarRightAdjunction A (h₁ ≫ h₂))
    (lowerStarCompConj A g₁ g₂) (inv (lowerStarCompConj A h₁ h₂))
    (tensorPullbackIsoOfIso A e ((leftDerivedUpperStarComp A h₁ h₂).app M).symm)
    (tensorBaseChangeNatTrans A h₁ e f₂ g₁ w₁ (L((h₂)^*[A]).obj M))
    (tensorBaseChangeNatTrans A h₂ f₂ f' g₂ w₂ M)
    (tensorBaseChangeNatTrans A (h₁ ≫ h₂) e f' (g₁ ≫ g₂)
      (comp_comm_of_comm h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂) M)
    (tensorBaseChangeNatTrans_app_comp A h₁ h₂ e f₂ f' g₁ g₂ w₁ w₂ M) L

end Etale

end AlgebraicGeometry
