/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module
public import Sheaf.Paper.FiniteDiscreteRealizationFunctor
/-! # Comparing the three factors of an adjunction exchange

The construction uses the mate unit and counit equations and one coherent
pullback cube. It makes no assumption that the exchange morphism is invertible.
-/

@[expose] public section
open CategoryTheory
namespace CategoryTheory.Adjunction
variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category D₁] [Category D₂] [Category D₃] [Category D₄]
  {U : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
  {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
  (a : U ⊣ R) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
  {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
  {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}

/-- Coherent pullback and pushforward comparisons satisfying the unit and counit
identities identify the three exchange factors.
Source: Mathlib `unit_mateEquiv` and `mateEquiv_counit`
(blueprint: lem-weil-pbc-three-step-adjunction-comparison).

Proof. At the first vertex compose the horizontal pullback comparison with the
first right-adjoint comparison. At the middle vertices insert the second
right-adjoint comparison and the pullback comparisons and their functorial images.
At the last vertex use the second right-adjoint comparison and the remaining
horizontal comparison. Naturality and the unit equation give the first square.
The pullback cube and naturality give the second. The counit equation, cancellation
of inverse isomorphisms and naturality give the third. No exchange invertibility
is assumed. -/
theorem threeStepComparison
    (θ : G ⋙ V ≅ U ⋙ H) (θe : Ge ⋙ Ve ≅ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He)
    (δ : R ⋙ T₁ ≅ T₂ ⋙ Re) (δ' : S ⋙ T₃ ≅ T₄ ⋙ Se)
    (hunit : ∀ K, T₃.map (b.unit.app K) ≫ δ'.hom.app (V.obj K) ≫
      Se.map (αV.hom.app K) = be.unit.app (T₃.obj K))
    (hcounit : ∀ K, Ue.map (δ.hom.app K) ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hcube : ∀ K, T₄.map (θ.hom.app K) ≫ αH.hom.app (U.obj K) ≫
        He.map (αU.hom.app K) =
      αV.hom.app (G.obj K) ≫ Ve.map (αG.hom.app K) ≫ θe.hom.app (T₁.obj K))
    (K : C₂) :
    Nonempty (FiniteDiscreteThreeStepComparison
      (T₃.map (b.unit.app (G.obj (R.obj K))))
      (T₃.map (S.map (θ.hom.app (R.obj K))))
      (T₃.map (S.map (H.map (a.counit.app K))))
      (be.unit.app (Ge.obj (Re.obj (T₂.obj K))))
      (Se.map (θe.hom.app (Re.obj (T₂.obj K))))
      (Se.map (He.map (ae.counit.app (T₂.obj K))))) := by
  let p₀ := αG.app (R.obj K) ≪≫ Ge.mapIso (δ.app K)
  let p₁ := δ'.app (V.obj (G.obj (R.obj K))) ≪≫
    Se.mapIso (αV.app (G.obj (R.obj K))) ≪≫ Se.mapIso (Ve.mapIso p₀)
  let p₂ := δ'.app (H.obj (U.obj (R.obj K))) ≪≫
    Se.mapIso (αH.app (U.obj (R.obj K))) ≪≫
    Se.mapIso (He.mapIso (αU.app (R.obj K))) ≪≫
    Se.mapIso (He.mapIso (Ue.mapIso (δ.app K)))
  let p₃ := δ'.app (H.obj K) ≪≫ Se.mapIso (αH.app K)
  refine ⟨⟨p₀, p₁, p₂, p₃, ?_, ?_, ?_⟩⟩
  · dsimp only [p₁, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    calc
      _ = be.unit.app (T₃.obj (G.obj (R.obj K))) ≫ Se.map (Ve.map p₀.hom) := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ Se.map (Ve.map p₀.hom)) (hunit (G.obj (R.obj K)))
      _ = _ := (be.unit.naturality p₀.hom).symm
  · dsimp only [p₁, p₂, p₀, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [reassoc_of% (δ'.hom.naturality (θ.hom.app (R.obj K)))]
    dsimp only [Functor.comp_map, Functor.comp_obj]
    simp only [Category.assoc, ← Se.map_comp]
    congr 1
    congr 1
    rw [reassoc_of% (hcube (R.obj K))]
    simp only [Functor.map_comp, Category.assoc]
    have hn := θe.hom.naturality (δ.hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [hn]
  · dsimp only [p₂, p₃, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [reassoc_of% (δ'.hom.naturality (H.map (a.counit.app K)))]
    dsimp only [Functor.comp_map, Functor.comp_obj]
    simp only [Category.assoc, ← Se.map_comp]
    congr 1
    congr 1
    rw [← Category.assoc, ← He.map_comp, hcounit]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← He.map_comp, Iso.hom_inv_id_app_assoc]
    exact αH.hom.naturality (a.counit.app K)

end CategoryTheory.Adjunction
