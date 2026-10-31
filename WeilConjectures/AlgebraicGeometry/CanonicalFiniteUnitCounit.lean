/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalFiniteUnitOrientation
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence

/-! # Counit normalization of the finite unit orientation

Source: latest def-pur-smooth-purity-map and def-pur-smooth-trace.
(blueprint: lem-pur-canonical-finite-unit-counit).
-/

set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor MonoidalCategory
namespace WeilConjectures

namespace RationalSmoothPurityCanonical

attribute [local instance 3000] instCategoryDerivedCategory ScalarLocalization.category

attribute [local instance 0] ConstructibleExceptionalCoefficients.category

attribute [local irreducible] sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  Functor.mapDerivedCategory HasDerivedCategory.standard

private theorem realizedCounit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (EX : C ⥤ D) (EY : C' ≌ D') (F : D ⥤ D') (S : C ⥤ C') (R : C' ⥤ C)
    (α : EX ⋙ F ≅ S ⋙ EY.functor) {A : C} (U : C') (a : A ⟶ R.obj U)
    (εU : S.obj (R.obj U) ⟶ U)
    (εL : S.obj (R.obj (EY.inverse.obj (EY.functor.obj U))) ⟶
      EY.inverse.obj (EY.functor.obj U))
    (hn : S.map (R.map (EY.unitIso.hom.app U)) ≫ εL = εU ≫ EY.unitIso.hom.app U) :
    F.map (EX.map (a ≫ R.map (EY.unitIso.hom.app U))) ≫
        α.hom.app _ ≫ EY.functor.map εL ≫ EY.counitIso.hom.app (EY.functor.obj U) =
      α.hom.app A ≫ EY.functor.map (S.map a ≫ εU) := by
  erw [α.hom.naturality_assoc]
  change α.hom.app A ≫ EY.functor.map (S.map (a ≫ R.map _)) ≫ _ ≫ _ = _
  have h : S.map (a ≫ R.map (EY.unitIso.hom.app U)) ≫ εL =
      (S.map a ≫ εU) ≫ EY.unitIso.hom.app U := by
    simp only [Functor.map_comp, Category.assoc, hn]
  rw [← EY.functor.map_comp_assoc, h, EY.functor.map_comp, Category.assoc,
    EY.functor_unitIso_comp, Category.comp_id]

private theorem mapFourAssoc {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E G H : C} (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ G) (d : G ⟶ H) :
    F.map (a ≫ b ≫ c ≫ d) = F.map (((a ≫ b) ≫ c) ≫ d) := by
  simp only [Category.assoc]

private theorem comparisonUnitCounit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {G : E ⥤ D}
    (adj : L ⊣ R) (cmp : F ⊣ G) (U : D) :
    F.map (L.map (R.map (cmp.unit.app U)) ≫ adj.counit.app _) ≫
        cmp.counit.app (F.obj U) = F.map (adj.counit.app U) := by
  erw [adj.counit_naturality, Functor.map_comp, Category.assoc,
    cmp.left_triangle_components, Category.comp_id]
  rfl

section RelativeOrientation
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Compact support of the unit orientation has precisely the recorded finite
integration as its counit transpose, through the actual finite-image comparison.
Source: latest def-pur-smooth-trace, the exceptional counit in the first composite;
canonical rational purity realization, the finite integration construction
(blueprint: lem-pur-canonical-finite-unit-counit).
Proof: unfold finiteUnitOrientation and the bounded-below branch of the smooth
exceptional counit. The coefficient unit is the realization of a degree-zero
ordinary unit, hence is bounded below. Naturality of the intrinsic compact-support
comparison moves the realized inverse diagonal orientation to the ordinary
compact-support functor. Naturality of the exceptional counit moves the intrinsic
realization unit to the output, where the equivalence triangle cancels it with
its counit. The etale/pro-etale adjunction triangle cancels the comparison unit
against diagonalDualizingComparison. The remaining map is inverse diagonal
orientation followed by ordinary exceptional counit. The proper/open comparison
between c and the selected compactification is the recorded normalized one.
Substituting finiteIntegration leaves finiteImageIso.inv followed by its hom;
these cancel. No assertion that finite quotients detect arbitrary maps is used. -/
theorem finiteUnitOrientationTrace (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (fun [hc : HasCompactification f] ↦
      (levelSmoothCompactSupport P f n).map (finiteUnitOrientation P f c n d) ≫
        levelSmoothExceptionalCounit P f n
          ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y) =
      (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n
        (HasCompactification.compactification f)).inv.app _ ≫
        finiteIntegration P f (HasCompactification.compactification f) n d)
      (hc := c.hasCompactification) := by
  classical
  let : HasCompactification f := c.hasCompactification
  dsimp only
  let Q := AdicSmoothDualizing.levelSetting P n
  let EY := sfIntrinsicDerivedEquivalence Y Q.Ring
  let CY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
    Y).mapDerivedCategory
  let U := Etale.ordinaryFiniteUnit Q.Coefficient Y
  have hCU : DerivedCategory.TStructure.t.plus (CY.obj U) :=
    (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
      (Q.diagonalUnitPlus Y)).plus
  have hL : DerivedCategory.TStructure.t.plus (EY.inverse.obj (Q.coefficientUnit Y)) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso (EY.unitIso.app (CY.obj U)) hCU
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let c₀ := HasCompactification.compactification f
  let EX := sfIntrinsicDerivedEquivalence X Q.Ring
  let CX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
    X).mapDerivedCategory
  let G := Etale.rightDerivedUpperShriek Q.Coefficient f
  let S := ProEtale.sfFixedCompactSupport Q.Ring c₀
  let R := Q.smoothPurityExceptional f
  let α := ProEtale.sfIntrinsicCompactSupportComparison Q.Ring c₀
  let ν := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Q.Coefficient) Y
  let ε := Etale.rightDerivedUpperShriekAdjunction Q.Coefficient f
  let π := @PurityFiniteSetting.diagonalDualizingObject Q X Y d f
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f)) (inferInstanceAs (SmoothOfRelativeDimension d f))
    (Y ↘ Spec (.of P.field.k))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))
  let b := π.inv ≫ (Q.diagonalDualizingComparison f).hom
  let a := b ≫ CX.map (G.map (ν.unit.app U))
  have hn := ProEtale.rightDerivedUpperShriekCounit_naturality f hCU hL
    (EY.unitIso.hom.app (CY.obj U))
  have hr := realizedCounit EX.functor EY (levelSmoothCompactSupport P f n) S R α
    (CY.obj U) a (ProEtale.rightDerivedUpperShriekCounit f (CY.obj U) hCU)
    (ProEtale.rightDerivedUpperShriekCounit f
      (EY.inverse.obj (Q.coefficientUnit Y)) hL) hn
  have hfirst : (levelSmoothCompactSupport P f n).map (finiteUnitOrientation P f c n d) ≫
      levelSmoothExceptionalCounit P f n (Q.coefficientUnit Y) =
      α.hom.app _ ≫ EY.functor.map
        (S.map a ≫ ProEtale.rightDerivedUpperShriekCounit f (CY.obj U) hCU) := by
    have ha : finiteUnitOrientation P f c n d =
        EX.functor.map (a ≫ R.map (EY.unitIso.hom.app (CY.obj U))) := by
      unfold finiteUnitOrientation
      exact mapFourAssoc EX.functor π.inv (Q.diagonalDualizingComparison f).hom
        (CX.map (G.map (ν.unit.app U))) (R.map (EY.unitIso.hom.app (CY.obj U)))
    rw [ha]
    unfold levelSmoothExceptionalCounit PurityFiniteSetting.smoothExceptionalCounit
    rw [dif_pos hL]
    exact hr
  rw [hfirst]
  have hGU : DerivedCategory.TStructure.t.plus (G.obj U) :=
    finiteDualizingPlus P f c n d
  have hs := ProEtale.rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit f
    hGU hCU (G.map (ν.unit.app U))
  simp only [Adjunction.homEquiv_counit] at hs
  erw [comparisonUnitCounit ε ν U] at hs
  have hsecond : S.map a ≫ ProEtale.rightDerivedUpperShriekCounit f (CY.obj U) hCU =
      S.map b ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} Q.Coefficient) c₀).hom.app ⟨_, hGU⟩ ≫
        CY.map (ε.counit.app U) := by
    dsimp only [a]
    erw [Functor.map_comp, Category.assoc, hs]
    rfl
  rw [hsecond]
  have hcself : Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
      Q.Coefficient c₀ c₀ = Iso.refl _ := by
    simp [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso]
  unfold finiteIntegration
  simp only [Iso.inv_hom_id_app_assoc]
  erw [hcself]
  dsimp only [b]
  have hbcomp : S.map (π.inv ≫ (Q.diagonalDualizingComparison f).hom) =
      S.map π.inv ≫ S.map (Q.diagonalDualizingComparison f).hom :=
    S.map_comp _ _
  have hbmap : EY.functor.map (S.map (π.inv ≫ (Q.diagonalDualizingComparison f).hom)) =
      EY.functor.map (S.map π.inv) ≫
        EY.functor.map (S.map (Q.diagonalDualizingComparison f).hom) := by
    rw [hbcomp, EY.functor.map_comp]
  rw [EY.functor.map_comp]
  erw [hbmap]
  simp only [Functor.map_comp, Iso.refl_hom, NatTrans.id_app, Category.assoc]
  simp [α, EY, S, CY, U, π, c₀, Q]
  rfl

end RelativeOrientation
end RationalSmoothPurityCanonical
end WeilConjectures
