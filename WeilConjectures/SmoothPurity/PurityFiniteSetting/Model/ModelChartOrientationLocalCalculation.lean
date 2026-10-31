/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # The beta-delta calculation in one compatible DNC coordinate triple -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem tensor_comp {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D ⥤ E) {K K' K'' : C} {L L' L'' : D}
    (a : K ≅ K') (a' : K' ≅ K'') (b : L ≅ L') (b' : L' ≅ L'') :
    compatibleBifunctorIso F a b ≪≫ compatibleBifunctorIso F a' b' =
      compatibleBifunctorIso F (a ≪≫ a') (b ≪≫ b') := by
  ext
  simp only [compatibleBifunctorIso, Functor.mapIso_trans, NatIso.trans_app, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  change (F.map a.hom).app L ≫ (F.obj K').map b.hom ≫
    (F.map a'.hom).app L' ≫ (F.obj K'').map b'.hom =
      (F.map a.hom).app L ≫ (F.map a'.hom).app L ≫
        (F.obj K'').map b.hom ≫ (F.obj K'').map b'.hom
  rw [(F.map a'.hom).naturality_assoc]
/-- The compatible-chart source pasting equation, beta identifications and affine
zero-section multiplication imply the beta-delta identity on one affine chart.
Source: model descent Steps 5--7.
(blueprint: lem-pur-model-chart-orientation-local-calculation).

Proof: fix a twist transport and use the canonical etale compact-support
normalization. From hEq take the last source-pasting equality, using its three
centred neighbourhoods. Postcompose with b_(d+e), namely modelOrientationZero
on U. Rewrite nu followed by b_(d+e) with hzero on U. Functoriality of the
derived tensor bifunctor groups the first delta with its normal comparison and
b_d, and groups the pulled-back second delta with its normal comparison,
standard-section pullback and b_e. The first and third beta identifications
replace the first group and the total normal comparison. The second beta
identification replaces the pulled-back normal comparison followed by the
standard-section comparison and b_e by the pulled-back beta followed by the
Tate pullback. Functor.mapIso_trans groups the second delta and beta. Tensor
functoriality moves the remaining Tate pullback after the two factors; by
definition this followed by modelOrientationPowerMul is modelOrientationMu.
This is the required beta-delta equation. All factors are the given canonical
maps. No frame or orientation is chosen in addition to x and y. For zero ranks
the same functorial equalities hold with the empty frame and the unit object.
-/
theorem model_chart_orientation_local_calculation (P : PurityFiniteSetting.{u})
    (G : P.ModelAffineGamma)
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f)
    (hy : y ≫ DiagonalPasting.pr e T = g)
    (hEq : CompatibleDncEquations P d e f g aT x y hx hy)
    (hzero : ∀ (B : Scheme.{u}) [IsAffine B]
      (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB],
        ModelZeroOrientationEquation P G B d e aB)
    (hbeta : ModelChartBetaIdentification P G d e f g aT) :
    ModelChartOrientationEquation P d e f g aT := by
  classical
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let hz := composition_compatible_tangent_normal P d e f g aT x y hx hy
  let := hz.2.1
  intro t
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  obtain ⟨hb1, hb2, hb3⟩ := hbeta x y hx hy t N
  obtain ⟨_, _, ⟨Cf⟩, ⟨Cg⟩, ⟨Cfg⟩, heq⟩ := hEq
  have hp := (heq t N).2.2.2 Cf Cg Cfg
  have hpaste := hp.2.2.2.2
  have hzero' := hzero U (f ≫ g ≫ aT)
  unfold ModelZeroOrientationEquation at hzero'
  rw [hb3]
  simp only [← Iso.trans_assoc] at hpaste ⊢
  erw [hpaste]
  simp only [Iso.trans_assoc]
  erw [hzero']
  simp only [modelOrientationMu, compatibleTensorIso, ← Iso.trans_assoc]
  rw [tensor_comp, tensor_comp, tensor_comp]
  simp only [Iso.trans_assoc, Functor.mapIso_trans]
  erw [← hb1, ← hb2]
  erw [Iso.trans_refl]
end WeilConjectures.PurityFiniteSetting
