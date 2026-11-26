/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineChainEvaluations
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import all WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension

/-! # Normalized opposite-line evaluations in the recorded derived tensor model

## References

* Stacks Project, Tags 015F and 06YU.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem single_kflat
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
      ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hp : (power l E X L m).IsFiniteLocallyFreeOfRank 1 := by
    rw [power_eq_coefficient]
    exact (signedLineTensor_equivalence.{u} X
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L m).1
  exact (SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, u, u + 2} X
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
    (power l E X L m)).2.2.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem chain_comparison
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    ∃ c : DerivedCategory.Q.{u + 2, u + 1, u + 2} ⋙ ordinary l E X L m ≅
        chainTensor l E X L m ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2},
      ∀ (P : (Good.{u, u} l E X none).FullSubcategory) (hT :
        @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
          ((integralLineSingle.{u, u} l E X).obj (power l E X L m))),
        c.app P.obj = (integralLineRepresentativeIso.{u, u} l E X P
          (power l E X L m) hT (DerivedCategory.Q.obj P.obj) (Iso.refl _)).symm := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let hT := single_kflat l E X L m
  have hId : DerivedCategory.Q.map
      ((integralLineSingle.{u, u} l E X).map (𝟙 (power l E X L m))) = 𝟙 _ :=
    (congrArg (fun f ↦ DerivedCategory.Q.map f)
      ((integralLineSingle.{u, u} l E X).map_id (power l E X L m))).trans
        (DerivedCategory.Q.map_id _)
  obtain ⟨t, ht, hn⟩ := ringedTensorComparison_extension.{u + 1, u, u, u + 2}
    (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
    (duality.{u, u} l E X none).closed (duality.{u, u} l E X none).models
  let c : DerivedCategory.Q.{u + 2, u + 1, u + 2} ⋙ ordinary l E X L m ≅
      chainTensor l E X L m ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2} :=
    NatIso.ofComponents (fun P ↦ (t P
      ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) (Or.inr hT)).symm)
      (by
        intro P Q f
        apply (cancel_epi (t P _ (Or.inr hT)).hom).mp
        apply (cancel_mono (t Q _ (Or.inr hT)).hom).mp
        simpa [ordinary, integralLineOrdinary, chainTensor, Prod.mkHom, hId] using
          (hn P _ Q _ (Or.inr hT) (Or.inr hT) f (𝟙 _)).symm)
  refine ⟨c, ?_⟩
  intro P hT'
  change (t P.obj _ (Or.inr hT)).symm = _
  rw [ht P.obj _ P.property.1 hT']
  apply Iso.ext
  simp [integralLineRepresentativeIso]
  rfl

/-- The given sheaf evaluations descend to the recorded ordinary derived tensor,
with the specified chain formula and the triangle identity. -/
theorem integral_line_normalized_evaluations
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (e : Evaluations l E X L) (he : EvaluationFormula l E X L e) (m : ℤ) :
    ∃ (v : ordinary l E X L m ⋙ ordinary l E X L (-m) ≅ 𝟭 (D.{u, u} l E X none))
      (w : ordinary l E X L (-m) ⋙ ordinary l E X L m ≅ 𝟭 (D.{u, u} l E X none)),
      DerivedEvaluationFormula l E X L m (-m) (e m) v ∧
      DerivedEvaluationFormula l E X L (-m) m (reverseEvaluation l E X L e m) w ∧
      ∀ K : D.{u, u} l E X none,
        (ordinary l E X L m).map (v.inv.app K) ≫
          w.hom.app ((ordinary l E X L m).obj K) = 𝟙 _ := by
  obtain ⟨a, b, ha, hb, hab⟩ := integral_line_chain_evaluations l E X L e he m
  obtain ⟨c, hc⟩ := chain_comparison l E X L m
  obtain ⟨d, hd⟩ := chain_comparison l E X L (-m)
  let Q := DerivedCategory.Q.{u + 2, u + 1, u + 2} (C := Mod l E X none)
  let W := HomologicalComplex.quasiIso (Mod l E X none) (.up ℤ)
  let T := chainTensor l E X L m
  let S := chainTensor l E X L (-m)
  let F := ordinary l E X L m
  let G := ordinary l E X L (-m)
  let v := SheafOfModules.LineUnbounded.localizedCancellation Q W T S F G c d a
  let w := SheafOfModules.LineUnbounded.localizedCancellation Q W S T G F d c b
  refine ⟨v, w, ?_, ?_, ?_⟩
  · intro P hm hk hS
    refine ⟨a.app P.obj, ha P.obj, ?_⟩
    have hci : c.inv.app P.obj = (integralLineRepresentativeIso.{u, u} l E X P
        (power l E X L m) hm (Q.obj P.obj) (Iso.refl _)).hom :=
      congrArg Iso.inv (hc P hm)
    have hdi : d.inv.app (T.obj P.obj) =
        (integralLineRepresentativeIso.{u, u} l E X ⟨T.obj P.obj, hS⟩
          (power l E X L (-m)) hk (Q.obj (T.obj P.obj)) (Iso.refl _)).hom :=
      congrArg Iso.inv (hd ⟨T.obj P.obj, hS⟩ hk)
    have hp : (integralLineRepresentativeIso.{u, u} l E X ⟨T.obj P.obj, hS⟩
        (power l E X L (-m)) hk (F.obj (Q.obj P.obj))
        (integralLineRepresentativeIso.{u, u} l E X P (power l E X L m) hm
          (Q.obj P.obj) (Iso.refl _))).hom =
        d.inv.app (T.obj P.obj) ≫ G.map (c.inv.app P.obj) := by
      rw [hci, hdi]
      have hId : Q.map ((integralLineSingle.{u, u} l E X).map
          (𝟙 (power l E X L (-m)))) = 𝟙 _ :=
        (congrArg (fun f ↦ Q.map f)
          ((integralLineSingle.{u, u} l E X).map_id (power l E X L (-m)))).trans
            (Q.map_id _)
      let f := (CoefficientTensorModels.iso (topology X none) (ring l E X none)
        (duality.{u, u} l E X none).closed (duality.{u, u} l E X none).models
        P.obj ((integralLineSingle.{u, u} l E X).obj (power l E X L m))
        P.property.1 hm).hom
      have h := congrArg (duality.{u, u} l E X none).closed.tensor.map
        (congrArg (Prod.mkHom f) hId.symm)
      simp [integralLineRepresentativeIso, G, F, ordinary, integralLineOrdinary]
      simpa only [f] using h
    have hnorm : (d.inv.app (T.obj P.obj) ≫ G.map (c.inv.app P.obj)) ≫
        v.hom.app (Q.obj P.obj) = Q.map (a.hom.app P.obj) := by
      rw [SheafOfModules.LineUnbounded.localizedCancellation_app]
      simp only [Category.assoc, ← G.map_comp_assoc, c.inv_hom_id_app]
      exact (congrArg (fun f ↦ d.inv.app (T.obj P.obj) ≫ f ≫
        d.hom.app (T.obj P.obj) ≫ Q.map (a.hom.app P.obj))
        (G.map_id (Q.obj (T.obj P.obj)))).trans
          ((congrArg (fun f ↦ d.inv.app (T.obj P.obj) ≫ f)
            (Category.id_comp (d.hom.app (T.obj P.obj) ≫ Q.map (a.hom.app P.obj)))).trans
              ((d.app (T.obj P.obj)).inv_hom_id_assoc (Q.map (a.hom.app P.obj))))
    exact (congrArg (fun f ↦ f ≫ v.hom.app (Q.obj P.obj)) hp).trans hnorm
  · intro P hm hk hS
    refine ⟨b.app P.obj, hb P.obj, ?_⟩
    have hdi : d.inv.app P.obj = (integralLineRepresentativeIso.{u, u} l E X P
        (power l E X L (-m)) hm (Q.obj P.obj) (Iso.refl _)).hom :=
      congrArg Iso.inv (hd P hm)
    have hci : c.inv.app (S.obj P.obj) =
        (integralLineRepresentativeIso.{u, u} l E X ⟨S.obj P.obj, hS⟩
          (power l E X L m) hk (Q.obj (S.obj P.obj)) (Iso.refl _)).hom :=
      congrArg Iso.inv (hc ⟨S.obj P.obj, hS⟩ hk)
    have hp : (integralLineRepresentativeIso.{u, u} l E X ⟨S.obj P.obj, hS⟩
        (power l E X L m) hk (G.obj (Q.obj P.obj))
        (integralLineRepresentativeIso.{u, u} l E X P (power l E X L (-m)) hm
          (Q.obj P.obj) (Iso.refl _))).hom =
        c.inv.app (S.obj P.obj) ≫ F.map (d.inv.app P.obj) := by
      rw [hdi, hci]
      have hId : Q.map ((integralLineSingle.{u, u} l E X).map
          (𝟙 (power l E X L m))) = 𝟙 _ :=
        (congrArg (fun f ↦ Q.map f)
          ((integralLineSingle.{u, u} l E X).map_id (power l E X L m))).trans
            (Q.map_id _)
      let f := (CoefficientTensorModels.iso (topology X none) (ring l E X none)
        (duality.{u, u} l E X none).closed (duality.{u, u} l E X none).models
        P.obj ((integralLineSingle.{u, u} l E X).obj (power l E X L (-m)))
        P.property.1 hm).hom
      have h := congrArg (duality.{u, u} l E X none).closed.tensor.map
        (congrArg (Prod.mkHom f) hId.symm)
      simp [integralLineRepresentativeIso, G, F, ordinary, integralLineOrdinary]
      simpa only [f] using h
    have hnorm : (c.inv.app (S.obj P.obj) ≫ F.map (d.inv.app P.obj)) ≫
        w.hom.app (Q.obj P.obj) = Q.map (b.hom.app P.obj) := by
      rw [SheafOfModules.LineUnbounded.localizedCancellation_app]
      simp only [Category.assoc, ← F.map_comp_assoc, d.inv_hom_id_app]
      exact (congrArg (fun f ↦ c.inv.app (S.obj P.obj) ≫ f ≫
        c.hom.app (S.obj P.obj) ≫ Q.map (b.hom.app P.obj))
        (F.map_id (Q.obj (S.obj P.obj)))).trans
          ((congrArg (fun f ↦ c.inv.app (S.obj P.obj) ≫ f)
            (Category.id_comp (c.hom.app (S.obj P.obj) ≫ Q.map (b.hom.app P.obj)))).trans
              ((c.app (S.obj P.obj)).inv_hom_id_assoc (Q.map (b.hom.app P.obj))))
    exact (congrArg (fun f ↦ f ≫ w.hom.app (Q.obj P.obj)) hp).trans hnorm
  · exact (SheafOfModules.LineUnbounded.localizedCancellation_triangles
      Q W T S F G c d a b hab).1

end WeilConjectures.IntegralLineReduction
