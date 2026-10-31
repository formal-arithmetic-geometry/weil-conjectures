/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions

/-! # Coefficient extension on normalized section charts

Source: Bhatt--Scholze 6.8.2 and the profinite-test realization normalization;
Stacks 00YV for reconstruction of the section ring.
(blueprint: lem-pur-normalized-realization-section-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- A map induced by continuous coefficient postcomposition is the same postcomposition
in every normalized reconstructed section chart. Source: Bhatt--Scholze 6.8.2;
Stacks 00YV (blueprint: lem-pur-normalized-realization-section-scalar).
Proof: take the adjoint of the two maps from the pulled coefficient object to continuous
F-valued functions. The chart normalizations identify their components with composition
by the profinite-test projection, followed by the given coefficient map. These commute
pointwise, so injectivity of the adjunction bijection gives the coefficient-object square.
Apply that square to a section and evaluate at a point. The section-map and section-chart
normalizations identify this equation with the asserted sectionwise coefficient formula.
Empty test spaces require no separate assumption. -/
theorem normalizedRealizationSectionScalar
    (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (hi : Continuous i) (W : Scheme.{u})
    (AE : CondensedERealization.At l E W) (AF : CondensedERealization.At l F W)
    (r : Profinite.continuousCoefficientRingObj E ⟶ Profinite.continuousCoefficientRingObj F)
    (hr : ∀ (S : Profinite.{u}) (f : C(S, E)) (x : S),
      ((r.hom.app (op S)) (ULift.up f)).down x = i (f x))
    (d : CondensedERealization.SectionRing E W ⟶ CondensedERealization.SectionRing F W)
    (hd : ∀ (U : W.ProEtᵒᵖ) (b : (CondensedERealization.SectionRing E W).obj.obj U),
      HEq (d.hom.app U b) ((coefficientMap r W).hom.app U b))
    (U : W.ProEtᵒᵖ) (b : (CondensedERealization.SectionRing E W).obj.obj U)
    (x : U.unop.left) :
    rationalCoefficientValue l F W U (AF.sectionIso.hom.hom.app U (d.hom.app U b)) x =
      i (rationalCoefficientValue l E W U (AE.sectionIso.hom.hom.app U b) x) := by
  let g : ((sheafCompose (ProEt.topology W)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf W E)) ⟶
      ((sheafCompose (ProEt.topology W)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf W F)) :=
    ⟨{ app := fun V ↦ AddCommGrpCat.ofHom
         { toFun := fun s ↦ ULift.up
             ⟨fun y ↦ i (s.down y), hi.comp s.down.continuous⟩
           map_zero' := by apply ULift.ext; ext y; exact map_zero i
           map_add' := by intro a b; apply ULift.ext; ext y; exact map_add i _ _ }
       naturality := fun _ _ _ ↦ rfl }⟩
  have hc : coefficientMap r W ≫ AF.coefficientIso.hom.hom =
      AE.coefficientIso.hom.hom ≫ g := by
    let L := pointUpperStar ⋙ (toSpecZ W)^*[Ab.{u + 1}]
    let adj := pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ W))
    let aE : L.obj (Profinite.continuousCoefficientRingObj E) ⟶
        (sheafCompose (ProEt.topology W) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (continuousCoefficientRingSheaf W E) := AE.coefficientIso.hom.hom
    let aF : L.obj (Profinite.continuousCoefficientRingObj F) ⟶
        (sheafCompose (ProEt.topology W) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (continuousCoefficientRingSheaf W F) := AF.coefficientIso.hom.hom
    change L.map r ≫ aF = aE ≫ g
    apply (adj.homEquiv_naturality_left_square_iff r aF aE g).mp
    ext S s
    apply ULift.ext
    apply ContinuousMap.ext
    intro y
    change ((((adj.homEquiv _ _ AF.coefficientIso.hom.hom).hom.app S)
        (r.hom.app S s)).down y) =
      i ((((adj.homEquiv _ _ AE.coefficientIso.hom.hom).hom.app S) s).down y)
    have hF := DFunLike.congr_fun (congrArg ULift.down
      (AF.coefficient_normalization S.unop (r.hom.app S s).down)) y
    have hE := DFunLike.congr_fun (congrArg ULift.down
      (AE.coefficient_normalization S.unop s.down)) y
    exact hF.trans ((hr S.unop s.down (profiniteTestProjection W S.unop y)).trans
      (congrArg i hE.symm))
  rw [AF.section_normalization, AE.section_normalization]
  have hv := congrArg (fun z ↦ (z.hom.app U b).down x) hc
  change ((AF.coefficientIso.hom.hom).hom.app U (d.hom.app U b)).down x = _
  rw [eq_of_heq (hd U b)]
  exact hv

end WeilConjectures
