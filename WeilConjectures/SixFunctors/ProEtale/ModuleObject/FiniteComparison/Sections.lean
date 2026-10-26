/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Global sections of `Λ_X` for a finite discrete ring

Let `T` be a finite discrete commutative ring and `Λ_X = p_X^* T̲` the pullback to `X_proét` of
the condensed ring `T̲ = C(-, T)`. The global sections of `Λ_X` are the continuous maps `X → T`
(`AlgebraicGeometry.ProEtale.finiteSectionRingHom_bijective`), through the comparison
`ψ_X : Λ_X ≅ C(-, T)_X` (`AlgebraicGeometry.ProEtale.isIso_continuousMapComparison`). This is
compatible with pullback, which is precomposition on functions
(`AlgebraicGeometry.ProEtale.Γ_map_condensedPullbackHom_finiteSectionRingHom`), and the constant
global section `t` of `Λ_X`, the image under `p_X^*` of the constant global section of `T̲`, is
the constant function `t` (`AlgebraicGeometry.ProEtale.finiteSectionRingHom_const`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The inverse image `p_X^*` is additive, being a left adjoint (a copy of the instance of
`WeilConjectures.TraceFormula.Basic`, which is not imported here). -/
instance additive_upperStarFromPoint_of_finiteSections (X : Scheme.{u}) :
    (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T]

instance : IsIso (continuousMapComparison X T) :=
  isIso_continuousMapComparison X T

/-- The global sections of `Λ_X = p_X^* T̲` given by continuous maps `X → T`: the global section of
`C(-, T)_X` given by a continuous map, transported along `ψ_X⁻¹ : C(-, T)_X ≅ Λ_X`. -/
noncomputable def finiteSectionRingHom :
    C(X, T) →+* Γ (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X) :=
  (Γ.map (inv (continuousMapComparison X T))).comp (continuousMapSectionRingHom X T)

/-- **The global sections of `Λ_X` are the continuous maps `X → T`.** -/
lemma finiteSectionRingHom_bijective : Function.Bijective (finiteSectionRingHom X T) := by
  rw [finiteSectionRingHom, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ (continuousMapSectionRingHom_bijective X T)
  refine Function.bijective_iff_has_inverse.2 ⟨Γ.map (continuousMapComparison X T), fun s ↦ ?_,
    fun s ↦ ?_⟩ <;> exact Γ.ext (by simp)

omit [DiscreteTopology T] in
/-- The constant global sections of the pullback `C(-, T)_X` of `C(-, T)` are the constant
functions. -/
lemma Γ_map_continuousMapComparison_mapFunctor_const (t : T) :
    Γ.map (continuousMapComparison X T)
        (Γ.mapFunctor (upperStarFromPoint X) (Profinite.continuousMapConstRingHom.{u} T t)) =
      continuousMapSectionRingHom X T (ContinuousMap.const X t) := by
  refine Γ.ext ?_
  rw [Γ.map_hom, Γ.mapFunctor_hom, Category.assoc]
  refine (upperStarFromPointAdjunction X).ε_comp_map_comp_homEquiv_symm_eq _ _ _ ?_
  refine Sheaf.unitHomEval_injective (J := coherentTopology Profinite.{u})
    Profinite.isTerminalPUnit _ ?_
  refine (Sheaf.unitHomEval_comp (J := coherentTopology Profinite.{u}) _ _ _).trans ?_
  rw [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Category.assoc, ← Functor.map_comp]
  have h₁ := Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map
    (J := coherentTopology Profinite.{u}) (K := ProEt.topology specZ.{u})
    (T := Profinite.of PUnit.{u + 1}) profiniteToProEt (ProEt.isTerminalMkId specZ)
    (ε (toSpecZ X)_*[Ab.{u + 1}] ≫ (toSpecZ X)_*[Ab.{u + 1}].map
      (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom)
  rw [unitHomEval_ε_comp_lowerStar_map, unitHomEval_continuousMapSectionRingHom] at h₁
  refine Eq.trans ?_ h₁.symm
  rw [Profinite.continuousMapConstRingHom]
  have h₂ := Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{u})
    (Profinite.of PUnit.{u + 1}) (Profinite.continuousMapRingSheaf.{u} T)
    (Profinite.continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) t
  erw [h₂]
  exact ULift.ext _ _ (ContinuousMap.ext fun x ↦ rfl)

/-- The constant global section `t` of `Λ_X`, the image under `p_X^*` of the constant global
section of `T̲`, is the constant function `t`. -/
lemma finiteSectionRingHom_const (t : T) :
    finiteSectionRingHom X T (ContinuousMap.const X t) =
      Γ.mapFunctor (upperStarFromPoint X) (Profinite.continuousMapConstRingHom.{u} T t) := by
  rw [finiteSectionRingHom, RingHom.comp_apply,
    ← Γ_map_continuousMapComparison_mapFunctor_const, Γ.map_map]
  exact Γ.ext (by simp)

variable {X} {X' : Scheme.{u}} (g : X' ⟶ X)

/-- **Compatibility with pullback**: along `g : X' ⟶ X`, the global section of `Λ_X` given by a
continuous map `f : X → T` pulls back to the global section of `Λ_{X'}` given by `f ∘ g`. -/
lemma Γ_map_condensedPullbackHom_finiteSectionRingHom (f : C(X, T)) :
    Γ.map (condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g)
        (Γ.mapFunctor (g)^*[Ab.{u + 1}] (finiteSectionRingHom X T f)) =
      finiteSectionRingHom X' T (f.comp g.base.hom) := by
  have sq := upperStar_map_continuousMapComparison_comp_continuousMapPullbackHom g T
  have sq' : (g)^*[Ab.{u + 1}].map (inv (continuousMapComparison X T)) ≫
      condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g =
      continuousMapPullbackHom g T ≫ inv (continuousMapComparison X' T) := by
    rw [← cancel_epi ((g)^*[Ab.{u + 1}].map (continuousMapComparison X T)),
      ← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc, sq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [finiteSectionRingHom, finiteSectionRingHom, RingHom.comp_apply, RingHom.comp_apply,
    Γ.mapFunctor_map, Γ.map_map, Γ.map_congr sq', ← Γ.map_map,
    Γ_map_continuousMapPullbackHom_mapFunctor]

end AlgebraicGeometry.ProEtale
