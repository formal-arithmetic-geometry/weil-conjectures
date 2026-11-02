/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassPullbackFrame

/-! # Underlying normalization of the scalar and realization transposes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace CategoryTheory.MonoidalCategory MonObj
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

private theorem scalar_transpose
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {L : C ⥤ C'} {R : C' ⥤ C} {L' : D ⥤ D'} {R' : D' ⥤ D}
    (A : L ⊣ R) (B : L' ⊣ R') (G : C ⥤ D) (H : C' ⥤ D')
    (s : G ⋙ L' ≅ L ⋙ H) (t : R ⋙ G ≅ H ⋙ R')
    (hm : (mateEquiv A B (TwoSquare.mk _ _ _ _ s.hom)).natTrans = t.hom)
    {M : C} {N : C'} (a : L.obj M ⟶ N) :
    B.homEquiv _ _ (s.hom.app M ≫ H.map a) =
      G.map (A.homEquiv _ _ a) ≫ t.hom.app N := by
  have hs := unit_mateEquiv A B (TwoSquare.mk _ _ _ _ s.hom) M
  have hm' := congrArg (fun k ↦ k.app (L.obj M)) hm
  change ((mateEquiv A B (TwoSquare.mk _ _ _ _ s.hom)).app (L.obj M)) =
    t.hom.app (L.obj M) at hm'
  rw [hm'] at hs
  change G.map (A.unit.app M) ≫ t.hom.app (L.obj M) =
    B.unit.app (G.obj M) ≫ R'.map (s.hom.app M) at hs
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hs]
  have hn := t.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← G.map_comp_assoc]
  rfl

set_option maxHeartbeats 2000000 in
-- Normalize underlying sheaves of the composite direct-image adjunction.
/-- The scalar transpose and the realized transpose have the same underlying sheaf map.

Source: blueprint latest, diagonal coefficient changes (3), scalar and realization mates.
(blueprint: lem-diagonal-scalar-realization-transpose).

Proof: the unit identity for mates identifies the scalar transpose with scalar
restriction of the completed transpose followed by scalarDirect. The realization
mate identifies the other transpose with realization of the same completed
transpose followed by pushIso inverse and the normalized ordinary realization
square. Naturality of the underlying comparison cancels realization; the ordinary
square normalization cancels its underlying comparison. ScalarDirect and pushIso
both act identically on sections, so the two remaining sheaf maps are equal. -/
theorem diagonalScalarRealization_transpose
    {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {g : Y' ⟶ Y}
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
    {d : ClassLimitPresentation l Y hY D} {d' : ClassLimitPresentation l Y' hY' D'}
    {e : CompletedRealization l (diagonalSurface Y)}
    {e' : CompletedRealization l (diagonalSurface Y')}
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (M : DiagonalCompleted l (diagonalSurface Y))
    (N : DiagonalCompleted l (diagonalSurface Y'))
    (a : (diagonalRealizationPull l (baseW g)).obj M ⟶ N) :
    (diagonalForget l (diagonalSurface Y)).map
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)).homEquiv _ _
          (f.scalar.hom.app M ≫
            (diagonalCompletedRestriction l (diagonalSurface Y')).map a)) =
      e.underlying.inv.app M ≫
        ((CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
          (f.realization.inv.app M ≫ e'.F.map a)).hom ≫
        (lowerStar Ab.{u + 1} (baseW g)).map (e'.underlying.hom.app N) := by
  let A := Scheme.proEtaleRingModuleAdjunction (baseW g)
    (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
    (Scheme.purTwistZlCompletion (diagonalSurface Y') l)
    (asIso (diagonalCompletedCoefficientMap l (baseW g)))
  let B := upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)
  have ht := scalar_transpose A B
    (diagonalCompletedRestriction l (diagonalSurface Y))
    (diagonalCompletedRestriction l (diagonalSurface Y'))
    f.scalar f.scalarDirect f.scalar_mate a
  rw [ht, f.realization_mate]
  simp only [Mod.comp_hom', Functor.map_comp, Category.assoc]
  have hn := e.underlying.inv.naturality (A.homEquiv _ _ a)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  have hn' := e.underlying.inv.naturality (f.pushIso.inv.app N)
  dsimp only [Functor.comp_map] at hn'
  erw [← reassoc_of% hn']
  erw [eq_of_heq (f.ordinarySquare.normalization N)]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  congr 1
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro x
  have hp := f.push_sections N V
  have hp' : (f.pushIso.inv.app N).val.app V x = x := by
    have h := congrArg (fun k ↦ k.val.app V x) (f.pushIso.inv_hom_id_app N)
    change (f.pushIso.hom.app N).val.app V
      ((f.pushIso.inv.app N).val.app V x) = x at h
    exact (eq_of_heq (hp _)).symm.trans h
  change (f.scalarDirect.hom.app N).hom.app V x =
    (f.pushIso.inv.app N).val.app V x
  rw [hp']
  exact eq_of_heq (f.scalar_sections N V x)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
