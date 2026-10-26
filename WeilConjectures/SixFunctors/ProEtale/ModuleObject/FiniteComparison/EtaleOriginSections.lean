/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Sections of the coefficient ring of a totally disconnected ring

Let `T` be a Hausdorff totally disconnected topological commutative ring (e.g. a finite discrete
ring) and `W` a scheme. By Bhatt–Scholze, Lemma 4.2.12 (`ProEtale.isIso_continuousMapComparison`)
the coefficient ring `T_W = p_W^* T̲` is the sheaf `U ↦ C(U, T)`, so its global sections, i.e.
the endomorphisms of the regular module `T_W`, are the continuous maps `W → T`
(`ProEtale.CondensedRing.continuousMapEndRegularRingEquiv`). Restriction along `g : W' ⟶ W`
is precomposition with `g`
(`ProEtale.CondensedRing.continuousMapEndRegularRingEquiv_restrictEnd`), and the multiplication
by the constant global section `t` of `T̲` is the constant function `t`
(`ProEtale.CondensedRing.continuousMapEndRegularRingEquiv_scalar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [T2Space T] [TotallyDisconnectedSpace T]

instance : IsIso (continuousMapComparison X T) :=
  isIso_continuousMapComparison X T

/-- The global sections of `T_W = p_W^* T̲` given by continuous maps `W → T`: the global section of
`C(-, T)_W` given by a continuous map, transported along `ψ_W⁻¹ : C(-, T)_W ≅ T_W`. -/
noncomputable def continuousMapCondensedSectionRingHom :
    C(X, T) →+* Γ (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X) :=
  (Γ.map (inv (continuousMapComparison X T))).comp (continuousMapSectionRingHom X T)

/-- **The global sections of `T_W` are the continuous maps `W → T`.** -/
lemma continuousMapCondensedSectionRingHom_bijective :
    Function.Bijective (continuousMapCondensedSectionRingHom X T) := by
  rw [continuousMapCondensedSectionRingHom, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ (continuousMapSectionRingHom_bijective X T)
  refine Function.bijective_iff_has_inverse.2 ⟨Γ.map (continuousMapComparison X T), fun s ↦ ?_,
    fun s ↦ ?_⟩ <;> exact Γ.ext (by simp)

variable {X} {X' : Scheme.{u}} in
/-- The pullback of the global section of `T_W` given by a continuous map `f : W → T` is the
global section of `T_{W'}` given by `f ∘ g`. -/
lemma Γ_map_condensedPullbackHom_continuousMapCondensedSectionRingHom (g : X' ⟶ X)
    (f : C(X, T)) :
    Γ.map (condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g)
        (Γ.mapFunctor (g)^*[Ab.{u + 1}] (continuousMapCondensedSectionRingHom X T f)) =
      continuousMapCondensedSectionRingHom X' T (f.comp g.base.hom) := by
  have sq := upperStar_map_continuousMapComparison_comp_continuousMapPullbackHom g T
  have sq' : (g)^*[Ab.{u + 1}].map (inv (continuousMapComparison X T)) ≫
      condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g =
      continuousMapPullbackHom g T ≫ inv (continuousMapComparison X' T) := by
    rw [← cancel_epi ((g)^*[Ab.{u + 1}].map (continuousMapComparison X T)),
      ← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc, sq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [continuousMapCondensedSectionRingHom, continuousMapCondensedSectionRingHom,
    RingHom.comp_apply, RingHom.comp_apply, Γ.mapFunctor_map, Γ.map_map, Γ.map_congr sq',
    ← Γ.map_map, Γ_map_continuousMapPullbackHom_mapFunctor]

/-- **The constant sections**: the image under `p_W^*` of the constant global section `t` of
`T̲` is the global section of `T_W` given by the constant function `t`. -/
lemma continuousMapCondensedSectionRingHom_const (t : T) :
    (continuousMapCondensedSectionRingHom X T (ContinuousMap.const X t)).hom =
      ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom := by
  rw [continuousMapCondensedSectionRingHom, RingHom.comp_apply, Γ.map_hom, IsIso.comp_inv_eq,
    Category.assoc]
  have h : (Profinite.continuousMapConstRingHom.{u} T t).hom ≫ continuousMapToLowerStar X T =
      ε ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar) ≫
        ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar).map
          (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom := by
    refine Sheaf.unitHomEval_injective (J := coherentTopology Profinite.{u})
      Profinite.isTerminalPUnit _ ?_
    refine (Sheaf.unitHomEval_comp (J := coherentTopology Profinite.{u}) _ _ _).trans ?_
    have e : ε ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar) ≫
        ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar).map
          (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom =
        ε (profiniteToProEt.sheafPushforwardContinuous Ab.{u + 1} (coherentTopology Profinite.{u})
          (ProEt.topology specZ)) ≫
          (profiniteToProEt.sheafPushforwardContinuous Ab.{u + 1} (coherentTopology Profinite.{u})
            (ProEt.topology specZ)).map
            (ε (toSpecZ X)_*[Ab.{u + 1}] ≫ (toSpecZ X)_*[Ab.{u + 1}].map
              (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom) := by
      rw [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Category.assoc, Functor.map_comp]
      rfl
    refine Eq.trans ?_ (congrArg (Sheaf.unitHomEval (J := coherentTopology Profinite.{u}) _) e).symm
    refine Eq.trans ?_ (Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map
      (J := coherentTopology Profinite.{u}) (K := ProEt.topology specZ.{u}) profiniteToProEt
      (ProEt.isTerminalMkId specZ.{u}) (T := Profinite.of PUnit.{u + 1})
      (ε (toSpecZ X)_*[Ab.{u + 1}] ≫ (toSpecZ X)_*[Ab.{u + 1}].map
        (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom)).symm
    rw [unitHomEval_ε_comp_lowerStar_map (toSpecZ X)
      (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom]
    have h₁ := Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{u})
      (T := Profinite.of PUnit.{u + 1}) (Profinite.continuousMapRingSheaf T)
      (Profinite.continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) t
    rw [unitHomEval_continuousMapSectionRingHom, Profinite.continuousMapConstRingHom]
    erw [h₁]
    exact ULift.ext _ _ (ContinuousMap.ext fun _ ↦ rfl)
  exact ((upperStarFromPointAdjunction X).ε_comp_map_comp_homEquiv_symm_eq
    (Profinite.continuousMapConstRingHom.{u} T t).hom (continuousMapToLowerStar X T)
    (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom h).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [T2Space T]
  [TotallyDisconnectedSpace T]

/-- **The endomorphisms of the regular module `T_W` are the continuous maps `W → T`**, for a
Hausdorff totally disconnected ring `T`: they are the global sections of `T_W`
(`CategoryTheory.Mod.regularEndRingHom_bijective`), computed by
`ProEtale.continuousMapCondensedSectionRingHom_bijective`. -/
noncomputable def continuousMapEndRegularRingEquiv (W : Scheme.{u}) :
    End (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} T) W)) ≃+* C(W, T) :=
  (RingEquiv.ofBijective _ Mod.regularEndRingHom_bijective).symm.trans
    (RingEquiv.ofBijective _ (continuousMapCondensedSectionRingHom_bijective W T)).symm

lemma continuousMapEndRegularRingEquiv_symm_apply (W : Scheme.{u}) (f : C(W, T)) :
    (continuousMapEndRegularRingEquiv T W).symm f =
      Mod.regularEndRingHom (continuousMapCondensedSectionRingHom W T f) :=
  rfl

/-- Restriction of endomorphisms of `T_W` along `g : W' ⟶ W` is precomposition with `g`. -/
lemma continuousMapEndRegularRingEquiv_restrictEnd {W' W : Scheme.{u}} (g : W' ⟶ W)
    (t : End (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} T) W))) :
    continuousMapEndRegularRingEquiv T W' (restrictEnd _ g t) =
      (continuousMapEndRegularRingEquiv T W t).comp g.base.hom := by
  obtain ⟨f, rfl⟩ := (continuousMapEndRegularRingEquiv T W).symm.surjective t
  rw [RingEquiv.apply_symm_apply, continuousMapEndRegularRingEquiv_symm_apply,
    restrictEnd_regularEndRingHom, Γ_map_condensedPullbackHom_continuousMapCondensedSectionRingHom,
    ← continuousMapEndRegularRingEquiv_symm_apply, RingEquiv.apply_symm_apply]

/-- The multiplication by the constant global section `t` of `T̲` on `T_W` is the constant
function `t`. -/
lemma continuousMapEndRegularRingEquiv_symm_const (W : Scheme.{u}) (t : T) :
    (continuousMapEndRegularRingEquiv T W).symm (ContinuousMap.const W t) =
      Mod.regularLift (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} T) W))
        (ε (upperStarFromPoint W) ≫
        (upperStarFromPoint W).map (Profinite.continuousMapConstRingHom.{u} T t).hom) := by
  rw [continuousMapEndRegularRingEquiv_symm_apply, Mod.regularEndRingHom_apply,
    continuousMapCondensedSectionRingHom_const]

end AlgebraicGeometry.ProEtale.CondensedRing
