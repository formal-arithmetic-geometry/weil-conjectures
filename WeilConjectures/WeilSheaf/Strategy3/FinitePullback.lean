/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.Scalars

/-! # Independent coefficient/pullback infrastructure: FinitePullback -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Type) [TopologicalSpace T] [CommRing T]
  [IsTopologicalRing T] [DiscreteTopology T] [Finite T]

/-- The image under `p_Y^*` of a global section `s` of `Λ`, followed by `η_f : Λ_Y ⟶ f_* Λ_X`,
is the image under `f_*` of the image of `s` under `p_X^*`. -/
lemma ε_comp_map_comp_condensedPushforwardHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (s : 𝟙_ _ ⟶ Λ) :
    ε (upperStarFromPoint Y) ≫ (upperStarFromPoint Y).map s ≫ condensedPushforwardHom Λ f =
      ε (f)_*[Ab.{u + 1}] ≫
        (f)_*[Ab.{u + 1}].map (ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s) := by
  have h := NatTrans.IsMonoidal.ε_comp_map_comp_app (upperStarFromPointComp f).hom s
  have e : ε (upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}]) =
    ε (f)^*[Ab.{u + 1}] ≫ (f)^*[Ab.{u + 1}].map (ε (upperStarFromPoint Y)) := rfl
  have h' : (f)^*[Ab.{u + 1}].map (ε (upperStarFromPoint Y)) ≫
      (f)^*[Ab.{u + 1}].map ((upperStarFromPoint Y).map s) ≫ condensedPullbackHom Λ f =
      Functor.OplaxMonoidal.η (f)^*[Ab.{u + 1}] ≫ ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map s := by
    rw [← h, e, Category.assoc, Functor.Monoidal.η_ε_assoc]
    rfl
  have hadj : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  rw [← unitAlgHom_comp_map_condensedPullbackHom, Adjunction.unitAlgHom,
    ← Adjunction.unit_naturality_assoc, ← Adjunction.unit_naturality_assoc,
    ← Functor.map_comp, ← Functor.map_comp, h', Functor.map_comp,
    Adjunction.unit_app_unit_comp_map_η_assoc]

omit [DiscreteTopology T] [Finite T] in
/-- The action of the constant global section `t` of `Λ_Y` on `f_* M` is the pushforward of
its action on `M`. -/
lemma globalSmul_lowerStar_obj (t : T)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coeffRing T) X)) :
    Mod.globalSmul (ε (upperStarFromPoint Y) ≫
        (upperStarFromPoint Y).map (Profinite.continuousMapConstRingHom.{u} T t).hom)
        ((Strategy3.lowerStar (coeffRing T) f).obj M) =
      (f)_*[Ab.{u + 1}].map (Mod.globalSmul (ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom) M) := by
  simp only [Strategy3.lowerStar, Functor.comp_obj]
  rw [Mod.globalSmul_comap, Category.assoc,
    ε_comp_map_comp_condensedPushforwardHom, Mod.globalSmul_mapMod]

/-- **The comparison of the two finite-coefficient models commutes with pushforward**:
`f_* ⋙ Φ_Y ≅ Φ_X ⋙ f_*`, where `Φ` is `finiteCoefficientModEquivalence`. Both sides have
underlying abelian sheaf `f_* M`, and the actions of `t ∈ T` on sections agree, being the actions
of the constant global section `t` (`finiteCoefficientModEquivalence_smul`). -/
noncomputable def lowerStarFiniteCoefficientModEquivalenceIso :
    Strategy3.lowerStar (coeffRing T) f ⋙
        (finiteCoefficientModEquivalence Y T).functor ≅
      (finiteCoefficientModEquivalence X T).functor ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (coeffType.{u} T)) f :=
  Sheaf.natIsoMkOfSheafCompose
    (F₁ := Strategy3.lowerStar (coeffRing T) f ⋙
      (finiteCoefficientModEquivalence Y T).functor)
    (F₂ := (finiteCoefficientModEquivalence X T).functor ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (coeffType.{u} T)) f) (fun M ↦ Iso.refl _)
    (fun M U r y ↦ by
      obtain ⟨t⟩ := r
      have h1 := finiteCoefficientModEquivalence_smul Y T
        ((Strategy3.lowerStar (coeffRing T) f).obj M) U t y
      rw [globalSmul_lowerStar_obj, ProEtale.lowerStar_map_hom_app] at h1
      have h2 := finiteCoefficientModEquivalence_smul X T M
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U.unop)) t
      exact h1.trans (h2 y).symm)
    fun φ ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl

/-- **The comparison of the two finite-coefficient models commutes with pullback**:
`f^* ⋙ Φ_X ≅ Φ_Y ⋙ f^*`, the conjugate of `lowerStarFiniteCoefficientModEquivalenceIso`. -/
noncomputable def upperStarFiniteCoefficientModEquivalenceIso :
    Strategy3.upperStar (coeffRing T) f ⋙
        (finiteCoefficientModEquivalence X T).functor ≅
      (finiteCoefficientModEquivalence Y T).functor ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} T)) f :=
  ((conjugateIsoEquiv
    ((Strategy3.upperStarLowerStarAdjunction (coeffRing T) f).comp
      (finiteCoefficientModEquivalence X T).toAdjunction)
    ((finiteCoefficientModEquivalence Y T).toAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (coeffType.{u} T)) f))).symm
    (Iso.inverseCompIso (Iso.isoCompInverse (lowerStarFiniteCoefficientModEquivalenceIso f T) ≪≫
      Functor.associator _ _ _))).symm


end AlgebraicGeometry.ProEtale.Strategy3
