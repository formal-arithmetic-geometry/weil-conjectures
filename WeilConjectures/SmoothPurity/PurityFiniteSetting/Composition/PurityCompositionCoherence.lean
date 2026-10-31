/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDescent
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionSingleMatePresentation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.FiniteCompositionSourceOrientationSquare
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.FiniteCompositionTensorRealization

/-! # Composition coherence for the specified smooth purity maps

Source: main-20261015, sec-smooth-purity/sk-prop-sp-composition,
thm-pur-composition-coherence (blueprint: thm-pur-composition-coherence).

The source identification is assembled from the ordered shifted Tate tensor powers,
monoidal comparison, pullback composition and the shift reassociation used by gamma.
The exceptional comparison is the recorded standing counit mate, transported through
the canonical constant-scalar equivalences. All objects are on the small pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

section Geometry
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

private theorem modelOrientation_base_congr
    {U V : Scheme.{u}} (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (n : ℕ) [SmoothOfRelativeDimension n h]
    (a b : V ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a]
    [LocallyOfFiniteType b] [QuasiCompact b] (hab : a = b) :
    P.modelOrientation n h a = P.modelOrientation n h b := by
  cases hab
  rfl

/-- Composition coherence for exactly the three canonical smooth purity maps.
Source: latest blueprint, sk-prop-sp-composition/thm-pur-composition-coherence.proof.md
(blueprint: thm-pur-composition-coherence).

Proof: orientation descent gives sigma followed by the composite orientation equal
to the tensor of the separate orientations followed by Tate multiplication. Cancel
these isomorphisms to obtain its inverse form. Precompose the finite tensor-realization
composition equation with that inverse; this identifies the two oriented tensor routes.
Present each of the three purity maps by its single-map tensor mate. Apply the source
orientation square to theta_g and postcompose with theta_f. Functoriality and the
oriented tensor equation identify the iterated purity route with gamma_fg followed
by the specified standing exceptional comparison, including its realization unit.
Finally postcompose with the inverse of that comparison. -/
theorem smoothPurityCompositionCoherence (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    P.smoothPurityMap (f ≫ g) (d + e) K hK =
      (P.compositionSourceIdentification f g d e K).hom ≫
        (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK) ≫
        P.smoothPurityMap f d ((P.compositionExceptional g).obj K)
          (P.compositionExceptional_ctf g e K hK) ≫
        (P.compositionExceptionalIso f g K hK).inv := by
  let := P.noetherian (Z ↘ Spec (.of P.field.k))
  let := P.noetherian (Y ↘ Spec (.of P.field.k))
  let := Dnc.compactifiable P f (Y ↘ Spec (.of P.field.k))
  let := Dnc.compactifiable P g (Z ↘ Spec (.of P.field.k))
  let := Dnc.compactifiable P (f ≫ g) (Z ↘ Spec (.of P.field.k))
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of P.field.k))
  let M := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K
  let E := (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor
  let U := (ProEtale.CompositionTensorMate.G P.Coefficient f).map
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.hom.app
      ((ProEtale.CompositionTensorMate.G P.Coefficient g).obj M))
  let V := P.compatibleTensorIso
    (P.modelOrientation d f (Y ↘ Spec (.of P.field.k)))
    ((ProEtale.CompositionTensorMate.S P.Coefficient f).mapIso
      (P.modelOrientation e g (Z ↘ Spec (.of P.field.k))))
  let μ := P.modelOrientationMu d e f (Y ↘ Spec (.of P.field.k))
  let O := P.modelOrientation (d + e) (f ≫ g) (Z ↘ Spec (.of P.field.k))
  let A := (ProEtale.CompositionTensorMate.S P.Coefficient (f ≫ g)).obj M
  obtain ⟨_, _, _, _, _, _, _, _, ho⟩ :=
    composition_model_orientation_descent.{u, u} P d e f g (Z ↘ Spec (.of P.field.k))
  have hor : ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫ O.hom =
      V.hom ≫ μ.hom := by
    have h := ho.1
    rw [modelOrientation_base_congr P f d (g ≫ (Z ↘ Spec (.of P.field.k)))
      (Y ↘ Spec (.of P.field.k)) (comp_over g _)] at h
    dsimp only [O, V, μ, ProEtale.CompositionTensorMate.S]
    simpa only [comp_over] using h
  have hinv : μ.inv ≫ V.inv ≫
      ProEtale.CompositionTensorMate.sigma P.Coefficient f g = O.inv := by
    apply (cancel_mono O.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [hor]
    simp
  let c := ProEtale.standingExceptionalComposition P f g
    ⟨M, P.compositionInput_bounded K hK⟩
  let B := ProEtale.CompositionTensorMate.r P.Coefficient f g M ≫
    (ProEtale.CompositionTensorMate.S P.Coefficient f).map
      (ProEtale.CompositionTensorMate.theta P.Coefficient g M) ▷
        ProEtale.CompositionTensorMate.omega P.Coefficient f ≫
    (ProEtale.CompositionTensorMate.S P.Coefficient f).map
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.hom.app
        ((ProEtale.CompositionTensorMate.G P.Coefficient g).obj M)) ▷
          ProEtale.CompositionTensorMate.omega P.Coefficient f ≫
    ProEtale.CompositionTensorMate.theta P.Coefficient f
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
        ((P.compositionExceptional g).obj K))
  have ht : A ◁ ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
      ProEtale.CompositionTensorMate.theta P.Coefficient (f ≫ g) M ≫ c ≫ U = B :=
    finiteCompositionTensorRealization P f g d e K hK
  have hroute : A ◁ (μ.inv ≫ V.inv) ≫ B =
      A ◁ O.inv ≫ ProEtale.CompositionTensorMate.theta P.Coefficient (f ≫ g) M ≫
        c ≫ U := by
    rw [← ht]
    calc
      _ = A ◁ (μ.inv ≫ V.inv ≫
          ProEtale.CompositionTensorMate.sigma P.Coefficient f g) ≫
          ProEtale.CompositionTensorMate.theta P.Coefficient (f ≫ g) M ≫ c ≫ U := by
            simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      _ = _ := by rw [hinv]
  have hcm : P.compositionExceptionalMap f g K hK = E.map (c ≫ U) := by
    change E.map (c ≫ U) = E.map (c ≫ U)
    simp only [E, M, c, U]
  have hit :
      (P.compositionSourceIdentification f g d e K).hom ≫
        (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK) ≫
        P.smoothPurityMap f d ((P.compositionExceptional g).obj K)
          (P.compositionExceptional_ctf g e K hK) =
      P.smoothPurityMap (f ≫ g) (d + e) K hK ≫
        P.compositionExceptionalMap f g K hK := by
    rw [composition_single_mate_presentation P g e K hK,
      composition_single_mate_presentation P f d ((P.compositionExceptional g).obj K)
        (P.compositionExceptional_ctf g e K hK),
      composition_single_mate_presentation P (f ≫ g) (d + e) K hK, hcm]
    have hs := finiteCompositionSourceOrientationSquare P f g d e K
      ((ProEtale.CompositionTensorMate.G P.Coefficient g).obj M)
      (ProEtale.CompositionTensorMate.theta P.Coefficient g M)
    have hs' := congrArg (fun z ↦ z ≫ E.map
      (ProEtale.CompositionTensorMate.theta P.Coefficient f
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
          ((P.compositionExceptional g).obj K)))) hs
    calc
      _ = (P.compositionMateSource (f ≫ g) (d + e) K).hom ≫
          E.map (A ◁ (μ.inv ≫ V.inv) ≫ B) := by
        simp only [B, E, M, A, μ, V,
          compositionShiftedPullback, Functor.comp_obj, Functor.comp_map,
          Functor.map_comp, Category.assoc] at hs' ⊢
        convert hs' using 1
        rfl
      _ = _ := by
        rw [hroute]
        simp only [E, M, A, O, Functor.map_comp, Category.assoc]
  have hi : P.compositionExceptionalMap f g K hK ≫
      (P.compositionExceptionalIso f g K hK).inv = 𝟙 _ :=
    (P.compositionExceptionalIso f g K hK).hom_inv_id
  calc
    _ = (P.smoothPurityMap (f ≫ g) (d + e) K hK ≫
        P.compositionExceptionalMap f g K hK) ≫
          (P.compositionExceptionalIso f g K hK).inv := by
            rw [Category.assoc, hi]
            dsimp only [compositionExceptional]
            exact (Category.comp_id _).symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun a ↦ a ≫ (P.compositionExceptionalIso f g K hK).inv) hit.symm

end Geometry
end WeilConjectures.PurityFiniteSetting
