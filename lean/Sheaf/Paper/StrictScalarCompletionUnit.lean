/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
import all Sheaf.Paper.StrictQuotientScalarBalancing
import all Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat

/-! # Normalized scalar comparisons for strict quotient completion units

Source: Stacks 099M and 0940; completed scalar supplement, Steps 2 and 3.
(blueprint: lem-weil-pbc-strict-scalar-completion-unit).
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite ConstantCompletion
namespace AlgebraicGeometry.Scheme.CompletedScalarUnitProof
open StrictScalarBalancing
variable {A : Type (u + 1)} [CommRing A]

private theorem ordinary_unit_restriction (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (P : Cx (ring T d true)) :
    letI := d.noetherian
    ((res (scalar T d)).mapHomologicalComplex (.up ℤ)).map
        (ordinaryUnit (topology T) A d.ideal true P) ≫
        (limitRestriction (scalar T d)).hom.app
          (reductionComplex (topology T) A d.ideal true P) =
      ordinaryUnit (topology T) A d.ideal false
          (((res (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (ordinaryLimit (ring T d false)).map ((balanceComplex T d).hom.app P) := by
  let := d.noetherian
  apply HomologicalComplex.hom_ext
  intro q
  apply limit.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc]
  have hp := (limitRestriction_existsUnique (scalar T d)).exists.choose_spec
    (reductionComplex (topology T) A d.ideal true P) q n.unop
  change ((limitRestriction (scalar T d)).hom.app _).f q ≫ limit.π _ n = _ at hp
  rw [hp]
  rw [← Functor.map_comp]
  have hu := (ordinaryUnit_existsUnique (topology T) A d.ideal true P).exists.choose_spec
    q n.unop
  change (ordinaryUnit (topology T) A d.ideal true P).f q ≫ _ = _ at hu
  rw [hu]
  change _ = (ordinaryUnit (topology T) A d.ideal false
      (((res (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P)).f q ≫
    limMap (((balanceComplex T d).hom.app P).f q) ≫ limit.π _ n
  rw [limMap_π, ← Category.assoc]
  have hu₀ := (ordinaryUnit_existsUnique (topology T) A d.ideal false
    (((res (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P)).exists.choose_spec q n.unop
  change (ordinaryUnit (topology T) A d.ideal false _).f q ≫ _ = _ at hu₀
  erw [hu₀]
  exact congrArg (fun z ↦ z.app n) (ordinary_augmentation T d (P.X q)).symm

private theorem completion_unit_square
    {C C₀ T T₀ : Type*} [Category C] [Category C₀] [Category T] [Category T₀]
    (r : C ⥤ C₀) (s : T ⥤ T₀) (LA : T ⥤ C) (L₀ : T₀ ⥤ C₀) (R₀ : C₀ ⥤ T₀)
    (lam : LA ⋙ r ≅ s ⋙ L₀)
    {M U : C} {M₀ U₀ U' Ubar : C₀} {X P : T} {P₀ Y : T₀}
    (α : M₀ ≅ r.obj M) (γ : P₀ ≅ Y) (δ : Y ≅ s.obj P)
    (ρ : s.obj X ≅ R₀.obj (r.obj M))
    (βA : X ⟶ P) [IsIso βA] (β₀ : R₀.obj M₀ ⟶ P₀)
    (cA : M ⟶ LA.obj X) (c₀ : r.obj M ⟶ L₀.obj (R₀.obj (r.obj M)))
    (c₀' : M₀ ⟶ L₀.obj (R₀.obj M₀))
    (eA : M ⟶ U) (e₀ : M₀ ⟶ U₀)
    (jA : U ⟶ LA.obj P) (j₀ : U₀ ⟶ L₀.obj P₀) (j' : U' ⟶ L₀.obj Y)
    (a : r.obj U ⟶ Ubar) (l : Ubar ⟶ U') (v : M₀ ⟶ Ubar) (g : U₀ ⟶ U')
    (hz : R₀.map α.inv ≫ β₀ ≫ γ.hom ≫ δ.hom = ρ.inv ≫ s.map βA)
    (hA : cA ≫ LA.map βA = eA ≫ jA)
    (hlam : r.map jA ≫ lam.hom.app P = a ≫ l ≫ j' ≫ L₀.map δ.hom)
    (he : r.map eA ≫ a = α.inv ≫ v)
    (hv : v ≫ l = e₀ ≫ g)
    (hj : g ≫ j' = j₀ ≫ L₀.map γ.hom)
    (h₀ : c₀' ≫ L₀.map β₀ = e₀ ≫ j₀)
    (hc : α.inv ≫ c₀' = c₀ ≫ L₀.map (R₀.map α.inv)) :
    r.map cA ≫ lam.hom.app X ≫ L₀.map ρ.hom = c₀ := by
  let z := R₀.map α.inv ≫ β₀ ≫ γ.hom ≫ δ.hom
  have hz' : z = ρ.inv ≫ s.map βA := hz
  have : IsIso z := by rw [hz']; infer_instance
  apply (cancel_mono (L₀.map z)).mp
  simp only [Category.assoc]
  rw [← L₀.map_comp, hz']
  simp only [Functor.map_comp]
  rw [← L₀.map_comp_assoc, ρ.hom_inv_id, L₀.map_id, Category.id_comp]
  have hn := lam.hom.naturality βA
  change r.map (LA.map βA) ≫ lam.hom.app P =
    lam.hom.app X ≫ L₀.map (s.map βA) at hn
  rw [← hn, ← r.map_comp_assoc, hA, r.map_comp,
    Category.assoc, hlam, ← Category.assoc, he]
  simp only [Category.assoc]
  rw [← Category.assoc v l, hv]
  simp only [Category.assoc]
  rw [← Category.assoc g j', hj]
  simp only [Category.assoc]
  rw [← Category.assoc e₀ j₀, ← h₀]
  simp only [Category.assoc]
  rw [← Category.assoc α.inv c₀', hc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ c₀ ≫ L₀.map f) hz

private theorem quotient_unit_on_flat
    (T : Scheme.{u}) (d : AdicCoefficientDatum A) (B : Balancing d)
    (lambda : rlim (ring T d true) ⋙ dres (scalar T d) ≅
      tdres (scalar T d) ⋙ rlim (ring T d false))
    (hlambda : ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (ring T d true)) ℤ,
      (dres (scalar T d)).map ((limitComparison (ring T d true)).app P) ≫
          lambda.hom.app ((TQ (ring T d true)).obj P) =
        (resFactors (scalar T d)).inv.app ((ordinaryLimit (ring T d true)).obj P) ≫
          (Q (ring T d false)).map ((limitRestriction (scalar T d)).hom.app P) ≫
          (limitComparison (ring T d false)).app
            (((tres (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (rlim (ring T d false)).map ((tresFactors (scalar T d)).hom.app P))
    (P : Cx (ring T d true)) (hP : P.IsAcyclicTensorKFlat)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q))
    (hP₀ : CochainComplex.IsAcyclicTensorKFlat
      (((res (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P))
    (hf₀ : ∀ q : ℤ, SheafOfModules.IsFlat
      ((((res (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P).X q)) :
    (dres (scalar T d)).map ((completionUnit (topology T) A d.ideal true).app
      ((Q (ring T d true)).obj P)) ≫
      (lambda.hom.app ((reduction T d true).obj ((Q (ring T d true)).obj P)) ≫
        (rlim (ring T d false)).map ((B.ρ T).hom.app ((Q (ring T d true)).obj P))) =
    (completionUnit (topology T) A d.ideal false).app
      ((dres (scalar T d)).obj ((Q (ring T d true)).obj P)) := by
  let := d.noetherian
  let βa := (quotientPresentation (topology T) A d.ideal true).comparison.app P
  let P₀ := ((res (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P
  let β₀ := (quotientPresentation (topology T) A d.ideal false).comparison.app P₀
  let α := (resFactors (scalar T d)).app P
  let γ := (balanceComplex T d).app P
  let δ := (tresFactors (scalar T d)).app (reductionComplex (topology T) A d.ideal true P)
  have : IsIso βa := (quotientPresentation (topology T) A d.ideal true).laws.2.1 P hP hf
  apply completion_unit_square (dres (scalar T d)) (tdres (scalar T d))
    (rlim (ring T d true)) (rlim (ring T d false)) (reduction T d false) lambda
    α ((TQ (ring T d false)).mapIso γ) δ
    ((B.ρ T).app ((Q (ring T d true)).obj P)) βa β₀
    ((completionUnit (topology T) A d.ideal true).app _)
    ((completionUnit (topology T) A d.ideal false).app _)
    ((completionUnit (topology T) A d.ideal false).app _)
    ((Q (ring T d true)).map (ordinaryUnit (topology T) A d.ideal true P))
    ((Q (ring T d false)).map (ordinaryUnit (topology T) A d.ideal false P₀))
    ((limitComparison (ring T d true)).app _)
    ((limitComparison (ring T d false)).app _)
    ((limitComparison (ring T d false)).app _)
    ((resFactors (scalar T d)).inv.app
      ((ordinaryLimit (ring T d true)).obj (reductionComplex (topology T) A d.ideal true P)))
    ((Q (ring T d false)).map ((limitRestriction (scalar T d)).hom.app _))
    ((Q (ring T d false)).map
      (((res (scalar T d)).mapHomologicalComplex (.up ℤ)).map
        (ordinaryUnit (topology T) A d.ideal true P)))
    ((Q (ring T d false)).map ((ordinaryLimit (ring T d false)).map γ.hom))
  · exact B.ρ_computes T P hP hf
  · exact (quotientPresentation (topology T) A d.ideal true).laws.2.2 P hP hf
  · exact hlambda (reductionComplex (topology T) A d.ideal true P)
  · exact (resFactors (scalar T d)).inv.naturality
      (ordinaryUnit (topology T) A d.ideal true P)
  · rw [← Functor.map_comp, ordinary_unit_restriction, Functor.map_comp]
    rfl
  · exact (limitComparison (ring T d false)).naturality γ.hom
  · exact (quotientPresentation (topology T) A d.ideal false).laws.2.2 P₀ hP₀ hf₀
  · exact (completionUnit (topology T) A d.ideal false).naturality α.inv

/-- The normalized strict balancing and limit comparisons identify the actual
quotient completion units on all ambient derived objects.

Source: Stacks 099M and 0940; completed scalar supplement, proof Steps 2 and 3.
(blueprint: lem-weil-pbc-strict-scalar-completion-unit).

Proof: choose a flat-term K-flat representative P of the input. Flat scalar restriction
preserves this resolving class. The quotient-presentation laws compute both completion
units as the ordinary quotient-unit map followed by the universal right-derived limit
comparison. After restriction, the ordinary limit map has the same projection at every
level: finite balancing sends 1 tensor m to 1 tensor m. Joint monicity of the limit
projections proves equality of these chain maps. Apply the normalization of lambda and
the representative formula for B.rho, and use naturality of the universal limit
comparison. Cancel the invertible derived reduction computation map of P. This gives
the displayed equality on Q(P). Naturality and a quasi-isomorphism from P to a chosen
representative transport the equality to every derived object. No completeness of the
input is used. The empty generating list and the zero ideal obey the same calculation. -/
theorem strictScalarCompletionUnit (d : AdicCoefficientDatum A) (B : Balancing d)
    (T : Scheme.{u})
    (lambda : rlim (ring T d true) ⋙ dres (scalar T d) ≅
      tdres (scalar T d) ⋙ rlim (ring T d false))
    (hlambda : ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (ring T d true)) ℤ,
      (dres (scalar T d)).map ((limitComparison (ring T d true)).app P) ≫
          lambda.hom.app ((TQ (ring T d true)).obj P) =
        (resFactors (scalar T d)).inv.app ((ordinaryLimit (ring T d true)).obj P) ≫
          (Q (ring T d false)).map ((limitRestriction (scalar T d)).hom.app P) ≫
          (limitComparison (ring T d false)).app
            (((tres (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (rlim (ring T d false)).map ((tresFactors (scalar T d)).hom.app P))
    (L : D (ring T d true)) :
    (dres (scalar T d)).map ((completionUnit (topology T) A d.ideal true).app L) ≫
        lambda.hom.app ((reduction T d true).obj L) ≫
          (rlim (ring T d false)).map ((B.ρ T).hom.app L) =
      (completionUnit (topology T) A d.ideal false).app ((dres (scalar T d)).obj L) := by
  let := d.noetherian
  let := HasDerivedCategory.standard (Mod (ring T d true))
  let F := completion (topology T) A d.ideal true ⋙ dres (scalar T d)
  let G := dres (scalar T d) ⋙ completion (topology T) A d.ideal false
  let e : F ≅ G :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (reduction T d true) lambda ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (B.ρ T) (rlim (ring T d false)) ≪≫
      Functor.associator _ _ _
  let lhs := Functor.whiskerRight (completionUnit (topology T) A d.ideal true)
    (dres (scalar T d)) ≫ e.hom
  let rhs := Functor.whiskerLeft (dres (scalar T d))
    (completionUnit (topology T) A d.ideal false)
  have he : lhs = rhs := by
    apply model_ext (Q (ring T d true))
      (HomologicalComplex.quasiIso (Mod (ring T d true)) (.up ℤ))
      (fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ i : ℤ, SheafOfModules.IsFlat (P.X i))
      (flat_resolution T d)
    intro P hP
    have hflat := (flat_and_quotients (topology T) A d.ideal).1
    have hr := SheafOfModules.isKFlat_restrictScalars_of_flat
      (scalar T d) ((flat_iff_site _).1 hflat) P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1)
    have hpr := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hr.1
    have hfr := hr.2 (fun i ↦ (flat_iff_site _).1 (hP.2 i))
    dsimp only [lhs, rhs, e]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app]
    erw [Category.id_comp]
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.symm_hom, Category.id_comp, Category.comp_id,
      Category.assoc]
      using quotient_unit_on_flat T d B lambda hlambda P hP.1 hP.2 hpr
        (fun i ↦ (flat_iff_site _).2 (hfr i))
  have h := congrArg (fun a ↦ a.app L) he
  dsimp only [lhs, rhs, e] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app] at h
  erw [Category.id_comp] at h
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, Category.id_comp, Category.comp_id,
      Category.assoc] using h

end AlgebraicGeometry.Scheme.CompletedScalarUnitProof
