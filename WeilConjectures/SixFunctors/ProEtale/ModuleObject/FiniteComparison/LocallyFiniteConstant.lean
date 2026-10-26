/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LocallyConstantPresentation

/-!
# Locally finitely presented module objects give finite locally constant sheaves

Let `T` be a finite discrete commutative ring and `Q` a module object over `Λ_Y = p_Y^* T̲`
which is finitely presented on the members of a pro-étale cover `{Uᵢ ⟶ Y}`. Then the sheaf of
`T`-modules corresponding to `Q` is locally constant with finite values
(`ProEtale.isFiniteLocallyConstant_finiteCoefficientModEquivalence_functor_obj`): refine the
cover by the finite Zariski covers `V_c ⟶ Uᵢ` on which the presentations become constant
(`ProEtale.exists_opens_iso_constantSheaf_of_isFinitelyPresented`); the comparison commutes with
the pullbacks (`ProEtale.finiteCoefficientModEquivalenceUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {T : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The members of an open cover of a scheme, indexed by a lifted type, form a pro-étale
covering family. -/
lemma ofArrows_ulift_opens_ι_mem_proetalePrecoverage {X : Scheme.{u}} {κ : Type}
    (V : κ → X.Opens) (hV : ∀ x, ∃ c, x ∈ V c) :
    Presieve.ofArrows (fun c : ULift.{u + 1} κ ↦ (V c.down : Scheme.{u})) (fun c ↦ (V c.down).ι) ∈
      Scheme.proetalePrecoverage X :=
  Scheme.zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ by
        obtain ⟨c, hc⟩ := hV x
        exact ⟨ULift.up c, by simpa using hc⟩,
        fun c ↦ inferInstanceAs (IsOpenImmersion (V c.down).ι)⟩)

/-- The comparison `Φ` commutes with the pullback along a composite `h ≫ g`:
`(h ≫ g)^* (Φ_Y Q) ≅ Φ_Z (h^* g^* Q)`. -/
noncomputable def finiteCoefficientModEquivalenceUpperStarCompIso {Z W Y : Scheme.{u}}
    (h : Z ⟶ W) (g : W ⟶ Y)
    (Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)) :
    (h ≫ g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj
        ((finiteCoefficientModEquivalence Y T).functor.obj Q) ≅
      (finiteCoefficientModEquivalence Z T).functor.obj
        ((h)^*⟦Profinite.continuousMapRingObj.{u} T⟧.obj
          ((g)^*⟦Profinite.continuousMapRingObj.{u} T⟧.obj Q)) :=
  (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) h g).app _ ≪≫
    (h)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].mapIso
      (finiteCoefficientModEquivalenceUpperStarIso g Q) ≪≫
    finiteCoefficientModEquivalenceUpperStarIso h _

/-- A sheaf of `Λ`-modules on `Y_proét` which is constant with finite values on the members of
finite Zariski covers `V_c ⟶ Uᵢ` of the members of a pro-étale cover `{Uᵢ ⟶ Y}` is locally
constant with finite values. -/
lemma isFiniteLocallyConstant_of_cover_of_opens {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (h : ∀ i, ∃ (κ : Type) (_ : Finite κ) (V : κ → (𝒰.X i).Opens), (∀ y, ∃ c, y ∈ V c) ∧
      ∀ c, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((((V c).ι ≫ 𝒰.f i))^*[ModuleCat.{u + 1} Λ].obj F ≅
          (constantSheaf (Scheme.ProEt.topology (V c)) (ModuleCat.{u + 1} Λ)).obj M)) :
    IsFiniteLocallyConstant Λ F := by
  choose κ hκ V hV hM using h
  choose M hMfin e using hM
  have hcov : Presieve.ofArrows (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down) (fun i ↦ 𝒰.f i.down) ∈
      Scheme.proetalePrecoverage Y := by
    have h : Presieve.ofArrows (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down)
        (fun i ↦ 𝒰.f i.down) = 𝒰.presieve₀ := by
      refine le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩) fun _ _ ⟨i⟩ ↦ ?_
      exact Presieve.ofArrows.mk (ULift.up i : ULift.{u + 1} 𝒰.I₀)
    rw [h]
    exact 𝒰.mem₀
  exact ⟨_, _, _, Precoverage.IsStableUnderComposition.comp_mem_coverings _ hcov
    (fun (i : ULift.{u + 1} 𝒰.I₀) (j : ULift.{u + 1} (κ i.down)) ↦ (V i.down j.down).ι)
    fun i ↦ ofArrows_ulift_opens_ι_mem_proetalePrecoverage (V i.down) (hV i.down),
    fun p ↦ ⟨M p.1.down p.2.down, hMfin _ _, e _ _⟩⟩

/-- **Locally finitely presented module objects over `Λ_Y` give finite locally constant sheaves
of `T`-modules.** -/
theorem isFiniteLocallyConstant_finiteCoefficientModEquivalence_functor_obj {Y : Scheme.{u}}
    {Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (hQ : ∀ i, Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) (𝒰.X i))
      ((𝒰.f i)^*⟦Profinite.continuousMapRingObj.{u} T⟧.obj Q)) :
    IsFiniteLocallyConstant (ULift.{u + 1} T)
      ((finiteCoefficientModEquivalence Y T).functor.obj Q) := by
  refine isFiniteLocallyConstant_of_cover_of_opens _ 𝒰 fun i ↦ ?_
  obtain ⟨κ, hκ, V, hV, hM⟩ := exists_opens_iso_constantSheaf_of_isFinitelyPresented (hQ i)
  refine ⟨κ, hκ, V, hV, fun c ↦ ?_⟩
  obtain ⟨M, hMfin, ⟨e⟩⟩ := hM c
  exact ⟨M, hMfin, ⟨finiteCoefficientModEquivalenceUpperStarCompIso _ _ Q ≪≫ e⟩⟩

end AlgebraicGeometry.ProEtale
