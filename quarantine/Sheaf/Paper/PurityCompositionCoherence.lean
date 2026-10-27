/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.PurityCompositionComparisons
import Sheaf.Paper.CompositionModelOrientationDescent
import Sheaf.Paper.CompositionIteratedMateExpansion
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport

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

private theorem compositionInput_ctf
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Z
      ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K) := by
  let E := Scheme.sfIntrinsicDerivedEquivalence Z P.Ring
  refine ⟨P.compositionInput_bounded K hK, ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hK.2
  refine ⟨a, b, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    P.Ring Z a b hab (E.inverse.obj K)).mp ?_⟩
  refine ⟨hab, ?_⟩
  intro L N he f hf hN F i hi
  exact ht L N (he.map (fun e ↦ e ≪≫ E.counitIso.app K)) f hf hN F i hi

private theorem modelOrientation_base_congr
    {U V : Scheme.{u}} (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (n : ℕ) [SmoothOfRelativeDimension n h]
    (a b : V ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a]
    [LocallyOfFiniteType b] [QuasiCompact b] (hab : a = b) :
    P.modelOrientation n h a = P.modelOrientation n h b := by
  subst b
  rfl

/-- Composition coherence for exactly the three canonical smooth purity maps.
Source: main-20261015, sk-prop-sp-composition/thm-pur-composition-coherence.md
(blueprint: thm-pur-composition-coherence).
Proof: (1) transpose compact-support composition through the standing adjunctions,
whose pasted counit is eps_g after Rg_!(eps_f); this is compositionExceptionalMap.
(2) The tensor formula is the projection-formula mate. Its composition pentagon
identifies theta_fg with theta_f after pulled-back theta_g and c inverse.
(3) For the diagonal orientations, choose compatible smooth charts. The diagonal of
gf is the transverse composite of the diagonals, with tangent sequence split in
these charts. DNC invariance, normalized on standard pairs and compatible with etale
localization and base change, forces the two orientations to agree. Vector-bundle
purity respects the direct sum and gives their common chart normalization. Rank-one
sheaf Hom gluing gives global equality. The zero-dimensional case uses the unit laws.
(4) Split A(d+e)[2d+2e] into the two even-shifted powers, use pullback composition,
twist pullback and tensor/shift reassociation, precisely compositionSourceIdentification.
Substitute the orientation equality into the tensor-mate equation. This yields the
three arrows in the stated order, for the original intrinsic K and its original hK.
-/
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
  obtain ⟨_, _, _, _, hc, _, _, _, _, _, _, _, _, _, _, _, _, hinput⟩ :=
    ProEtale.CompositionTensorMate.composition_tensor_mate P f g d e
  have ht := (hinput M (compositionInput_ctf P K hK)).2.2.1
  change A ◁ ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
    ProEtale.CompositionTensorMate.theta P.Coefficient (f ≫ g) M ≫
      ProEtale.CompositionTensorMate.c P.Coefficient f g M =
        ProEtale.CompositionTensorMate.rhs P.Coefficient f g M at ht
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
  have hroute : A ◁ (μ.inv ≫ V.inv) ≫
      ProEtale.CompositionTensorMate.rhs P.Coefficient f g M =
      A ◁ O.inv ≫ ProEtale.CompositionTensorMate.theta P.Coefficient (f ≫ g) M ≫
        ProEtale.CompositionTensorMate.c P.Coefficient f g M := by
    rw [← ht]
    calc
      _ = A ◁ (μ.inv ≫ V.inv ≫
          ProEtale.CompositionTensorMate.sigma P.Coefficient f g) ≫
          ProEtale.CompositionTensorMate.theta P.Coefficient (f ≫ g) M ≫
          ProEtale.CompositionTensorMate.c P.Coefficient f g M := by
            simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      _ = _ := by rw [hinv]
  have hcm : P.compositionExceptionalMap f g K hK =
      E.map (ProEtale.CompositionTensorMate.c P.Coefficient f g M ≫ U) := by
    unfold compositionExceptionalMap
    rw [← hc ⟨M, P.compositionInput_bounded K hK⟩]
    rfl
  have hit :
      (P.compositionSourceIdentification f g d e K).hom ≫
        (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK) ≫
        P.smoothPurityMap f d ((P.compositionExceptional g).obj K)
          (P.compositionExceptional_ctf g e K hK) =
      P.smoothPurityMap (f ≫ g) (d + e) K hK ≫
        P.compositionExceptionalMap f g K hK := by
    rw [composition_iterated_mate_expansion P f g d e K hK,
      composition_single_mate_presentation P (f ≫ g) (d + e) K hK, hcm]
    change (P.compositionMateSource (f ≫ g) (d + e) K).hom ≫
      E.map (A ◁ (μ.inv ≫ V.inv) ≫
        ProEtale.CompositionTensorMate.rhs P.Coefficient f g M ≫ U) = _
    rw [← Category.assoc (A ◁ (μ.inv ≫ V.inv)), hroute]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hi : P.compositionExceptionalMap f g K hK ≫
      (P.compositionExceptionalIso f g K hK).inv = 𝟙 _ :=
    (P.compositionExceptionalIso f g K hK).hom_inv_id
  have hh := congrArg (fun a ↦ a ≫ (P.compositionExceptionalIso f g K hK).inv) hit
  symm
  calc
    _ = (P.smoothPurityMap (f ≫ g) (d + e) K hK ≫
        P.compositionExceptionalMap f g K hK) ≫
          (P.compositionExceptionalIso f g K hK).inv := by
            simpa only [Category.assoc] using hh
    _ = _ := by
      rw [Category.assoc, hi]
      exact Category.comp_id _

end Geometry
end WeilConjectures.PurityFiniteSetting
