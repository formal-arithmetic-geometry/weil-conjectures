/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityDiagonalSectionPastingData
import WeilConjectures.AlgebraicGeometry.DualizingSigmaCocycleLocality
import WeilConjectures.AlgebraicGeometry.PurityDiagonalGlobalEquation
import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import all WeilConjectures.AlgebraicGeometry.PuritySectionBaseComparisonLaws
import all WeilConjectures.AlgebraicGeometry.PuritySectionRestrictionEtaleFunctorial
import all WeilConjectures.AlgebraicGeometry.SectionExceptionalFibreCoherence
import all WeilConjectures.SecSmoothPurity.FiniteEtaleDualizingNormalization

/-! # Open restrictions of diagonal section pasting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting


private noncomputable instance productOver (P : PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ S) (g : Y ⟶ S) : (pullback f g).Over (Spec (.of P.field.k)) :=
  ⟨pullback.fst f g ≫ (X ↘ Spec (.of P.field.k))⟩

private instance productFstOver (P : PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ S) (g : Y ⟶ S) :
    (pullback.fst f g).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩

private instance productSndOver (P : PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [S.Over (Spec (.of P.field.k))]
    (f : X ⟶ S) (g : Y ⟶ S)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))] :
    (pullback.snd f g).IsOver (Spec (.of P.field.k)) := ⟨by
  change pullback.snd f g ≫ (Y ↘ Spec (.of P.field.k)) =
    pullback.fst f g ≫ (X ↘ Spec (.of P.field.k))
  rw [← comp_over f _, ← comp_over g _, ← Category.assoc,
    ← pullback.condition, Category.assoc]⟩

private instance productFiniteType (P : PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pullback f g ↘ Spec (.of P.field.k)) :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.fst f g ≫ (X ↘ Spec (.of P.field.k))))

private instance productQuasiCompact (P : PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact g] :
    QuasiCompact (pullback f g ↘ Spec (.of P.field.k)) :=
  inferInstanceAs (QuasiCompact
    (pullback.fst f g ≫ (X ↘ Spec (.of P.field.k))))

private instance diagonalOver (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) :
    (pullback.diagonal f).IsOver (Spec (.of P.field.k)) := ⟨by
  change pullback.diagonal f ≫ (pullback.fst f f ≫ _) = _
  simp only [← Category.assoc, pullback.diagonal_fst, Category.id_comp]⟩


section Geometry
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]

private instance aOver : (a f g).IsOver (Spec (.of P.field.k)) := ⟨by
  change a f g ≫ (pullback.fst (f ≫ g) g ≫ _) = _
  rw [← Category.assoc, (geometry f g).2.2.1]
  rfl⟩

private instance sOver : (s f g).IsOver (Spec (.of P.field.k)) := ⟨by
  change s f g ≫ (pullback.fst (f ≫ g) g ≫ _) = _
  simp only [s, ← Category.assoc, pullback.lift_fst, Category.id_comp]⟩

private instance iOver : (i f g).IsOver (Spec (.of P.field.k)) := ⟨by
  change i f g ≫ (pullback.fst (f ≫ g) (f ≫ g) ≫ _) = _
  simp only [i, pullback.map, ← Category.assoc, pullback.lift_fst, Category.comp_id]
  rfl⟩

private instance jOver : (j f g).IsOver (Spec (.of P.field.k)) := ⟨by
  change j f g ≫ (pullback.fst g g ≫ _) = _
  simp only [j, pullback.map, ← Category.assoc, pullback.lift_fst]
  rw [Category.assoc, comp_over f _]
  rfl⟩

private instance sClosed [IsSeparated g] : IsClosedImmersion (s f g) := by
  let : IsClosedImmersion (s f g ≫ pullback.fst (f ≫ g) g) := by
    simpa only [s, pullback.lift_fst] using
      (inferInstance : IsClosedImmersion (𝟙 X))
  exact IsClosedImmersion.of_comp (s f g) (pullback.fst (f ≫ g) g)

private instance iClosed [IsSeparated g] : IsClosedImmersion (i f g) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (geometry f g).1.flip inferInstance

private instance jSeparated [IsSeparated f] : IsSeparated (j f g) :=
  MorphismProperty.of_isPullback (P := @IsSeparated) (geometry f g).2.1.flip inferInstance

private instance jFiniteType [LocallyOfFiniteType f] : LocallyOfFiniteType (j f g) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (geometry f g).2.1.flip inferInstance

private instance jQuasiCompact [QuasiCompact f] : QuasiCompact (j f g) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (geometry f g).2.1.flip inferInstance

end Geometry



namespace OpenRestrictionBeta
open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem recover_chain
    {C : Type*} [Category C] {W V Z Q R : C}
    (e : W ≅ V) (c : V ≅ Z) (j : Z ≅ Q) (i : Q ≅ R) (b : W ⟶ R)
    (h : b ≫ i.inv ≫ j.inv = e.hom ≫ c.hom) :
    (e ≪≫ c ≪≫ j ≪≫ i).hom = b := by
  have hh := congrArg (fun z ↦ z ≫ j.hom ≫ i.hom) h
  simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using hh.symm

variable (P : PurityFiniteSetting.{u})
variable {X Y X' Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [X'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
/-- The smooth base-change law at the unit, normalized by inverse target-etale locality.
Source: the restriction_beta calculation in FiniteDiagonalChosenRestriction, using only
FiniteEtaleDualizingNormalization.smooth_baseChange_law and inverse normalization. -/
private theorem canonical_restriction_beta
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f]
    (h : X' ⟶ Y') [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] [Smooth h]
    (e : X' ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v] [Etale v]
    (sq : IsPullback e h f v) :
    (ProEtale.DualizingLocality.restriction P f h e v sq.toCommSq).hom =
      ProEtale.FiniteEtaleNormalization.beta P f h v e sq := by
  let := compactification P h
  let := compactification P v
  let := compactification P (h ≫ v)
  have hb := smooth_baseChange_law P v f h e sq
  obtain ⟨s, hs, hi, _⟩ := P.dualizingComposite_inverse h v (eta P v)
  have ht : targetUnit P.Coefficient h v (rho P v) =
      dualizingCompositeTrivialization P.Coefficient h v (eta P v) := rfl
  have hσ : ProEtale.FiniteEtaleNormalization.sigma P.Coefficient h v (comp P h v) =
      dualizingCompositeSigma P.Coefficient h v := by
    simp only [ProEtale.FiniteEtaleNormalization.sigma, dualizingCompositeSigma,
      dualizingCompositeConjugate,
      finiteExceptionalComposition, comp, Etale.dualizingComplexTensorMap, Iso.app_inv]
  have hc := inverseNormalization
    (dualizingCompositeTrivialization P.Coefficient h v (eta P v)) s
    (dualizingCompositeConjugate P.Coefficient h v)
    ((ProEtale.FiniteEtaleNormalization.exceptional P h).mapIso (eta P v)) hi
  rw [hs, ← ht, ← hσ] at hc
  have hc' : (targetUnit P.Coefficient h v (rho P v)).inv ≫
      ProEtale.FiniteEtaleNormalization.sigma P.Coefficient h v (comp P h v) =
        (ProEtale.FiniteEtaleNormalization.exceptional P h).map (eta P v).inv ≫
          (comp P h v).inv.app
            (ProEtale.FiniteEtaleNormalization.coefficientUnit
              (ModuleCat.{u + 1} P.Coefficient) Y) := hc
  rw [hc'] at hb
  exact recover_chain (sourceEtale P e f).symm
    ((ProEtale.FiniteEtaleNormalization.congr P (e ≫ f) (h ≫ v) sq.w).app
      (ProEtale.FiniteEtaleNormalization.coefficientUnit
        (ModuleCat.{u + 1} P.Coefficient) Y))
    ((comp P h v).app (ProEtale.FiniteEtaleNormalization.coefficientUnit
      (ModuleCat.{u + 1} P.Coefficient) Y))
    ((ProEtale.FiniteEtaleNormalization.exceptional P h).mapIso (eta P v))
    (ProEtale.FiniteEtaleNormalization.beta P f h v e sq) hb


end OpenRestrictionBeta


open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem restriction_source (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [Etale e] [IsSeparated e] [QuasiCompact e]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI := fieldSchemeNoetherian P U
    letI := fieldSchemeNoetherian P X
    letI := fieldSchemeNoetherian P Y
    letI := compactification P f
    letI := compactification P (e ≫ f)
    etaleRestriction P.Coefficient P e f = sourceEtale P e f := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := fieldSchemeNoetherian P U
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := compactification P f
  let := compactification P (e ≫ f)
  rw [SectionRestriction.sourceEtale_locality P e f]
  let H := Etale.existsUnique_etaleAmbientAdjointLocalityIso P.Coefficient e f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (e ≫ f))
    (Etale.rightDerivedUpperShriek P.Coefficient f)
    (Etale.rightDerivedUpperShriek P.Coefficient (e ≫ f))
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (e ≫ f))
  have hc : H.exists.choose = H.choose := H.choose_spec.2 _ H.exists.choose_spec
  apply Iso.ext
  simp only [etaleRestriction, restrictionUnit, Etale.sectionStructuralLocalityIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_inv]
  change H.exists.choose.inv.app (𝟙_ _) ≫ _ = H.choose.inv.app (𝟙_ _) ≫ _
  rw [hc]

section Factor
variable (P : PurityFiniteSetting.{u})
    {U X Y X' Y' : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (p : U ⟶ Y') [p.IsOver (Spec (.of P.field.k))]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (j : X' ⟶ U) [j.IsOver (Spec (.of P.field.k))]
    [Etale j] [IsSeparated j] [QuasiCompact j]
    (a : U ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [Etale a] [IsSeparated a] [QuasiCompact a]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [Etale v] [IsSeparated v] [QuasiCompact v]

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem restriction_factor (hs : a ≫ f = p ≫ v) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) j a).app
        (omega P f) ≪≫
      (pull P j).mapIso (ProEtale.DualizingLocality.restriction P f p a v ⟨hs⟩) ≪≫
      (sourceEtale P j p).symm =
    ProEtale.DualizingLocality.restriction P f (j ≫ p) (j ≫ a) v
      ⟨by rw [Category.assoc, hs, ← Category.assoc]⟩ := by
  let := compactification P f
  let := compactification P p
  let := compactification P (p ≫ v)
  let := compactification P (j ≫ p)
  let := compactification P ((j ≫ p) ≫ v)
  let := compactification P v
  let := compactification P j
  let := compactification P a
  let := compactification P (a ≫ f)
  let := compactification P ((j ≫ a) ≫ f)
  let := compactification P (j ≫ (p ≫ v))
  let cg₀ := (ProEtale.FiniteEtaleNormalization.congr P
    ((j ≫ p) ≫ v) ((j ≫ a) ≫ f)
    (by rw [Category.assoc, Category.assoc, hs])).app (𝟙_ _)
  let cg₁ := (ProEtale.FiniteEtaleNormalization.congr P
    ((j ≫ p) ≫ v) (j ≫ (p ≫ v)) (Category.assoc j p v)).app (𝟙_ _)
  let cg₂ := (ProEtale.FiniteEtaleNormalization.congr P
    (p ≫ v) (a ≫ f) hs.symm).app (𝟙_ _)
  let C := (Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) j a).app (omega P f)
  have hh := SectionRestriction.source_comp_eq P j a f (p ≫ v)
    ((j ≫ p) ≫ v) hs.symm (Category.assoc j p v)
  change (cg₀ ≪≫ sourceEtale P (j ≫ a) f) ≪≫ C =
    (cg₁ ≪≫ sourceEtale P j (p ≫ v)) ≪≫
      (pull P j).mapIso (cg₂ ≪≫ sourceEtale P a f) at hh
  have hk : C.hom ≫ (pull P j).map (sourceEtale P a f).inv ≫
        (pull P j).map cg₂.inv =
      (sourceEtale P (j ≫ a) f).inv ≫ cg₀.inv ≫ cg₁.hom ≫
        (sourceEtale P j (p ≫ v)).hom := by
    have ht := congrArg (fun z ↦
      (sourceEtale P (j ≫ a) f).inv ≫ cg₀.inv ≫ z.hom ≫
        (pull P j).map (sourceEtale P a f).inv ≫ (pull P j).map cg₂.inv) hh
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      Category.comp_id] at ht
    simpa only [← (pull P j).map_comp, Iso.hom_inv_id, (pull P j).map_id,
      Category.comp_id] using ht
  let ev : (ProEtale.FiniteEtaleNormalization.exceptional P v).obj
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y) ≅
        coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y' := eta P v
  have hc := SectionRestriction.exceptional_assoc P j p v (𝟙_ _)
  have hn := (rho P j).hom.naturality
    ((comp P p v).hom.app (𝟙_ _) ≫ (ProEtale.FiniteEtaleNormalization.exceptional P p).map ev.hom)
  have hn' := (comp P j p).hom.naturality ev.hom
  apply Iso.ext
  simp only [ProEtale.DualizingLocality.restriction, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [SectionRestriction.congr_symm P (p ≫ v) (a ≫ f) hs.symm]
  change C.hom ≫ (pull P j).map (sourceEtale P a f).inv ≫
    (pull P j).map cg₂.inv ≫ (pull P j).map ((comp P p v).hom.app _) ≫
      (pull P j).map ((ProEtale.FiniteEtaleNormalization.exceptional P p).map ev.hom) ≫
      (sourceEtale P j p).inv =
    (sourceEtale P (j ≫ a) f).inv ≫
      (ProEtale.FiniteEtaleNormalization.congr P ((j ≫ a) ≫ f) ((j ≫ p) ≫ v)
        (by rw [Category.assoc, hs, ← Category.assoc])).hom.app _ ≫
      (comp P (j ≫ p) v).hom.app _ ≫
      (ProEtale.FiniteEtaleNormalization.exceptional P (j ≫ p)).map ev.hom
  rw [reassoc_of% hk]
  simp only [sourceEtale, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  dsimp only [omega, Etale.dualizingComplex, coefficientUnit, Functor.comp_obj] at hn ⊢
  rw [← Functor.map_comp_assoc, ← reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  dsimp only [omega, coefficientUnit, ProEtale.FiniteEtaleNormalization.exceptional,
    Etale.dualizingComplex, Functor.comp_obj] at hc hn' ⊢
  simp only [cg₁, Iso.app_hom]
  rw [reassoc_of% hc]
  rw [← reassoc_of% hn']
  simp only [Iso.hom_inv_id_app, Category.comp_id]
  rw [SectionRestriction.congr_symm P ((j ≫ p) ≫ v) ((j ≫ a) ≫ f)
    (by rw [Category.assoc, Category.assoc, hs])]
  rfl


set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem restriction_factor_endpoint (hs : a ≫ f = p ≫ v)
    (u₀ : X' ⟶ X) [u₀.IsOver (Spec (.of P.field.k))]
    [Etale u₀] [IsSeparated u₀] [QuasiCompact u₀]
    (f₀ : X' ⟶ Y') [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (hju : j ≫ a = u₀) (hjf : j ≫ p = f₀) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        j a u₀ hju.symm).app (omega P f) ≪≫
      (pull P j).mapIso (ProEtale.DualizingLocality.restriction P f p a v ⟨hs⟩) ≪≫
      (sourceEtale P j p).symm ≪≫
      (ProEtale.FiniteEtaleNormalization.congr P (j ≫ p) f₀ hjf).app (𝟙_ _) =
    ProEtale.DualizingLocality.restriction P f f₀ u₀ v
      ⟨by rw [← hju, ← hjf, Category.assoc, hs, ← Category.assoc]⟩ := by
  subst u₀
  subst f₀
  rw [SectionRestriction.congr_refl]
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.app_hom, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, omega, Etale.dualizingComplex, coefficientUnit] using
      congrArg Iso.hom (restriction_factor P f p j a v hs)


set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem dualizingCongr_eq
    {S T : Scheme.{u}} [S.Over (Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h h' : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [h'.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    (w : h = h') :
    let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    let := compactification P h
    let := compactification P h'
    dualizingCongr P.Coefficient P w =
      (ProEtale.FiniteEtaleNormalization.congr P h h' w).app (𝟙_ _) := by
  subst h'
  simp only [dualizingCongr, SectionRestriction.congr_refl]
  rfl

end Factor

section Open
variable (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (d : ℕ) (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (f' : X' ⟶ Y') [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (u' : X' ⟶ X) [u'.IsOver (Spec (.of P.field.k))] [IsOpenImmersion u']
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of P.field.k))] [IsOpenImmersion v]

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem openDualizing_eq (hf : u' ≫ f = f' ≫ v)
    (aX : X ⟶ Spec (.of P.field.k)) :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI := fieldSchemeNoetherian P X
    letI := fieldSchemeNoetherian P Y
    letI := fieldSchemeNoetherian P X'
    letI := fieldSchemeNoetherian P Y'
    openDualizing P.Coefficient P d f f' u' v hf aX =
      ProEtale.DualizingLocality.restriction P f f' u' v ⟨hf⟩ := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := fieldSchemeNoetherian P X'
  let := fieldSchemeNoetherian P Y'
  let B := pullback f v
  let p : B ⟶ Y' := pullback.snd f v
  let a : B ⟶ X := pullback.fst f v
  let j : X' ⟶ B := openFactor f f' u' v hf
  let : B.Over (Spec (.of P.field.k)) := ⟨p ≫ (Y' ↘ Spec (.of P.field.k))⟩
  let : p.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : a.IsOver (Spec (.of P.field.k)) := ⟨by
    change a ≫ (X ↘ Spec (.of P.field.k)) = p ≫ (Y' ↘ Spec (.of P.field.k))
    rw [← comp_over f _, ← comp_over v _, ← Category.assoc,
      pullback.condition, Category.assoc]⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ (Y' ↘ Spec (.of P.field.k))))
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (p ≫ (Y' ↘ Spec (.of P.field.k))))
  have hj := openFactorProperties f f' u' v hf
  let : IsOpenImmersion j := hj.1
  let : j.IsOver (Spec (.of P.field.k)) := ⟨by
    change j ≫ (p ≫ (Y' ↘ Spec (.of P.field.k))) = X' ↘ Spec (.of P.field.k)
    rw [← Category.assoc, hj.2.2, comp_over f' _]⟩
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  have hb := OpenRestrictionBeta.canonical_restriction_beta P f p a v
    (IsPullback.of_hasPullback f v)
  have he := restriction_source P j p
  have hh := restriction_factor_endpoint P f p j a v (pullback.condition (f := f) (g := v))
    u' f' hj.2.1 hj.2.2
  rw [← hh]
  change (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      j a u' hj.2.1.symm).app (omega P f) ≪≫
    (pull P j).mapIso (beta P.Coefficient P d (IsPullback.of_hasPullback f v) aX) ≪≫
    (etaleRestriction P.Coefficient P j p).symm ≪≫
    dualizingCongr P.Coefficient P hj.2.2 = _
  rw [he, dualizingCongr_eq P (j ≫ p) f' hj.2.2]
  congr 2
  apply congrArg ((pull P j).mapIso)
  apply Iso.ext
  exact hb.symm

end Open




set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem pullSquare_eq (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}} (u' : X' ⟶ X) (f : X ⟶ Y)
    (f' : X' ⟶ Y') (v : Y' ⟶ Y) (h : u' ≫ f = f' ≫ v)
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    (ProEtale.DualizingLocality.pullSquare P u' f' f v ⟨h⟩).hom.app K =
      (Etale.sectionCoherencePullbackIso P.Coefficient u' f f' v h K).hom := by
  exact congrArg Iso.hom (Etale.sectionPullback_endpoint P.Coefficient u' f f' v
    (f' ≫ v) (u' ≫ f) h.symm rfl rfl h K)

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem section_flip (A : Type (u + 1)) [CommRing A]
    {B B' W W' : Scheme.{u}} (u' : B' ⟶ B) (s : B ⟶ W)
    (s' : B' ⟶ W') (r : W' ⟶ W) (h : u' ≫ s = s' ≫ r)
    (K : Etale.DerivedCategoryModule A W) :
    (Etale.sectionCoherencePullbackIso A u' s s' r h K).inv =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' r).inv.app K ≫
        (Etale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} A) u' s (s' ≫ r) h.symm).hom.app K := by
  have he := Etale.sectionPullback_endpoint A u' s s' r
    (u' ≫ s) (s' ≫ r) rfl h h.symm rfl K
  exact congrArg Iso.inv he

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem section_comparison_natural
    (A : Type (u + 1)) [CommRing A]
    {B B' W W' : Scheme.{u}} (u' : B' ⟶ B) (p : W ⟶ B) (p' : W' ⟶ B')
    (r : W' ⟶ W) (s : B ⟶ W) (s' : B' ⟶ W')
    (hp : r ≫ p = p' ≫ u') (hs : u' ≫ s = s' ≫ r)
    (h : s ≫ p = 𝟙 B) (h' : s' ≫ p' = 𝟙 B')
    {M : Etale.DerivedCategoryModule A B} {M' : Etale.DerivedCategoryModule A B'}
    {K : Etale.DerivedCategoryModule A W} {K' : Etale.DerivedCategoryModule A W'}
    (b : (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj M ≅ K)
    (b' : (Etale.upperStar (ModuleCat.{u + 1} A) p').leftDerivedFunctor.obj M' ≅ K')
    (c : (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K ≅ K')
    (o : (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.obj M ≅ M')
    (hb : (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.map b.hom ≫
        c.hom = (Etale.sectionCoherencePullbackIso A r p p' u' hp M).hom ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) p').leftDerivedFunctor.map o.hom ≫
            b'.hom) :
    (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.map
        ((Etale.upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map b.inv ≫
          (Etale.leftDerivedUpperStarCompSectionIso
            (ModuleCat.{u + 1} A) s p h).hom.app M) ≫ o.hom =
      (Etale.sectionCoherencePullbackIso A u' s s' r hs K).hom ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map c.hom ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map b'.inv ≫
          (Etale.leftDerivedUpperStarCompSectionIso
            (ModuleCat.{u + 1} A) s' p' h').hom.app M' := by
  let U := (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor
  let S := (Etale.upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor
  let S' := (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor
  let R := (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor
  let P' := (Etale.upperStar (ModuleCat.{u + 1} A) p').leftDerivedFunctor
  have hn := ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) u' s).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' r (u' ≫ s) hs).hom.naturality b.inv
  change U.map (S.map b.inv) ≫
      (Etale.sectionCoherencePullbackIso A u' s s' r hs _).hom =
    (Etale.sectionCoherencePullbackIso A u' s s' r hs K).hom ≫
      S'.map (R.map b.inv) at hn
  have ht := Etale.leftDerivedUpperStar_map_comp_compSectionIso
    (ModuleCat.{u + 1} A) u' p p' r s s' hp hs.symm h h' M
  rw [← section_flip A u' s s' r hs _] at ht
  have hn' := (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s' p'
    h').hom.naturality o.hom
  change S'.map (P'.map o.hom) ≫
      (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s' p' h').hom.app M' =
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s' p' h').hom.app _ ≫ o.hom
      at hn'
  change S'.map (Etale.sectionCoherencePullbackIso A r p p' u' hp M).hom ≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s' p' h').hom.app _ =
      (Etale.sectionCoherencePullbackIso A u' s s' r hs _).inv ≫
        U.map ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M)
          at ht
  have hb' : c.hom ≫ b'.inv = R.map b.inv ≫
      (Etale.sectionCoherencePullbackIso A r p p' u' hp M).hom ≫ P'.map o.hom := by
    apply (cancel_epi (R.map b.hom)).1
    try simp only [Category.assoc]
    rw [reassoc_of% hb]
    simp only [Iso.hom_inv_id, Category.comp_id,
      ← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]
    rfl
  simp only [Functor.map_comp, Category.assoc]
  rw [← S'.map_comp_assoc, hb']
  simp only [S'.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hn', reassoc_of% ht]
  simp only [Iso.hom_inv_id_assoc]
  rfl

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem section_composite_natural
    (A : Type (u + 1)) [CommRing A]
    {B B' W W' V V' : Scheme.{u}} (u' : B' ⟶ B)
    (s : B ⟶ W) (s' : B' ⟶ W') (t : B ⟶ V) (t' : B' ⟶ V')
    (q : W ⟶ V) (q' : W' ⟶ V') (r : W' ⟶ W) (v : V' ⟶ V)
    (hs : u' ≫ s = s' ≫ r) (ht : u' ≫ t = t' ≫ v)
    (hq : r ≫ q = q' ≫ v) (h : s ≫ q = t) (h' : s' ≫ q' = t')
    {L : Etale.DerivedCategoryModule A V} {L' : Etale.DerivedCategoryModule A V'}
    {K : Etale.DerivedCategoryModule A W} {K' : Etale.DerivedCategoryModule A W'}
    (b : (Etale.upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj L ≅ K)
    (b' : (Etale.upperStar (ModuleCat.{u + 1} A) q').leftDerivedFunctor.obj L' ≅ K')
    (cK : (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K ≅ K')
    (cL : (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj L ≅ L')
    (hb : (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.map b.hom ≫
        cK.hom = (Etale.sectionCoherencePullbackIso A r q q' v hq L).hom ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) q').leftDerivedFunctor.map cL.hom ≫
            b'.hom) :
    (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.map
        ((Etale.upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map b.inv ≫
          (Etale.leftDerivedUpperStarComp
            (ModuleCat.{u + 1} A) s q t h.symm).inv.app L) ≫
      (Etale.sectionCoherencePullbackIso A u' t t' v ht L).hom ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) t').leftDerivedFunctor.map cL.hom =
    (Etale.sectionCoherencePullbackIso A u' s s' r hs K).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map cK.hom ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map b'.inv ≫
          (Etale.leftDerivedUpperStarComp
            (ModuleCat.{u + 1} A) s' q' t' h'.symm).inv.app L' := by
  let U := (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor
  let S := (Etale.upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor
  let S' := (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor
  let R := (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor
  let T' := (Etale.upperStar (ModuleCat.{u + 1} A) t').leftDerivedFunctor
  have hc := Etale.section_pullback_locality_comp A u' t t' s s' q q' v r
    ht hs h h' hq L
  have hn := ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) u' s).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' r (u' ≫ s) hs).hom.naturality b.inv
  change U.map (S.map b.inv) ≫
      (Etale.sectionCoherencePullbackIso A u' s s' r hs _).hom =
    (Etale.sectionCoherencePullbackIso A u' s s' r hs K).hom ≫
      S'.map (R.map b.inv) at hn
  have hn' := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' q' t'
    h'.symm).inv.naturality cL.hom
  change S'.map ((Etale.upperStar (ModuleCat.{u + 1} A) q').leftDerivedFunctor.map cL.hom) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' q' t' h'.symm).inv.app L' =
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' q' t' h'.symm).inv.app _ ≫
      T'.map cL.hom at hn'
  have hb' : cK.hom ≫ b'.inv = R.map b.inv ≫
      (Etale.sectionCoherencePullbackIso A r q q' v hq L).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) q').leftDerivedFunctor.map cL.hom := by
    apply (cancel_epi (R.map b.hom)).1
    try simp only [Category.assoc]
    rw [reassoc_of% hb]
    simp only [Iso.hom_inv_id, Category.comp_id,
      ← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]
  have hc' :
      (Etale.sectionCoherencePullbackIso A u' s s' r hs _).hom ≫
        S'.map (Etale.sectionCoherencePullbackIso A r q q' v hq L).hom ≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' q' t' h'.symm).inv.app _ =
      U.map ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s q t h.symm).inv.app L) ≫
        (Etale.sectionCoherencePullbackIso A u' t t' v ht L).hom := by
    apply (cancel_epi (U.map
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s q t h.symm).hom.app L))).1
    try simp only [Category.assoc]
    rw [reassoc_of% hc]
    simp only [Iso.hom_inv_id_app, Category.comp_id,
      ← U.map_comp_assoc, Iso.hom_inv_id_app, U.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← S'.map_comp_assoc, hb']
  simp only [S'.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hn', reassoc_of% hc']




set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem section_square_cube
    (A : Type (u + 1)) [CommRing A]
    {B B' V V' Y Y' W W' : Scheme.{u}}
    (a : B ⟶ Y) (a' : B' ⟶ Y') (t : Y ⟶ W) (t' : Y' ⟶ W')
    (s : B ⟶ V) (s' : B' ⟶ V') (q : V ⟶ W) (q' : V' ⟶ W')
    (u' : B' ⟶ B) (v : Y' ⟶ Y) (r : V' ⟶ V) (z : W' ⟶ W)
    (h : a ≫ t = s ≫ q) (h' : a' ≫ t' = s' ≫ q')
    (ha : u' ≫ a = a' ≫ v) (ht : v ≫ t = t' ≫ z)
    (hs : u' ≫ s = s' ≫ r) (hq : r ≫ q = q' ≫ z)
    (L : Etale.DerivedCategoryModule A W) :
    (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.map
        (Etale.sectionCoherencePullbackIso A a t s q h L).hom ≫
      (Etale.sectionCoherencePullbackIso A u' s s' r hs
        ((Etale.upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj L)).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map
        (Etale.sectionCoherencePullbackIso A r q q' z hq L).hom =
    (Etale.sectionCoherencePullbackIso A u' a a' v ha
        ((Etale.upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.obj L)).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.map
        (Etale.sectionCoherencePullbackIso A v t t' z ht L).hom ≫
      (Etale.sectionCoherencePullbackIso A a' t' s' q' h'
        ((Etale.upperStar (ModuleCat.{u + 1} A) z).leftDerivedFunctor.obj L)).hom := by
  let U := (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor
  have hk : u' ≫ (a ≫ t) = (a' ≫ t') ≫ z := by
    rw [← Category.assoc, ha, Category.assoc, ht, Category.assoc]
  have hc₁ := Etale.section_pullback_locality_comp A u' (a ≫ t) (a' ≫ t')
    a a' t t' z v hk ha rfl rfl ht L
  have hc₂ := Etale.section_pullback_locality_comp A u' (a ≫ t) (a' ≫ t')
    s s' q q' z r hk hs h.symm h'.symm hq L
  apply (cancel_epi (U.map ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a t).hom.app
    L))).1
  have hx : U.map (Etale.sectionCoherencePullbackIso A a t s q h L).hom =
      U.map ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a t).inv.app L) ≫
        U.map ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          s q (a ≫ t) h).hom.app L) := by
    simp only [Etale.sectionCoherencePullbackIso, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, Functor.map_comp]
  rw [hx]
  simp only [Category.assoc, ← U.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [hc₂, reassoc_of% hc₁]
  simp only [Etale.sectionCoherencePullbackIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc]

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem section_square_map_natural
    (A : Type (u + 1)) [CommRing A]
    {B B' V V' Y Y' W W' : Scheme.{u}}
    (a : B ⟶ Y) (a' : B' ⟶ Y') (t : Y ⟶ W) (t' : Y' ⟶ W')
    (s : B ⟶ V) (s' : B' ⟶ V') (q : V ⟶ W) (q' : V' ⟶ W')
    (u' : B' ⟶ B) (v : Y' ⟶ Y) (r : V' ⟶ V) (z : W' ⟶ W)
    (h : a ≫ t = s ≫ q) (h' : a' ≫ t' = s' ≫ q')
    (ha : u' ≫ a = a' ≫ v) (ht : v ≫ t = t' ≫ z)
    (hs : u' ≫ s = s' ≫ r) (hq : r ≫ q = q' ≫ z)
    {L : Etale.DerivedCategoryModule A W} {L' : Etale.DerivedCategoryModule A W'}
    {K : Etale.DerivedCategoryModule A V} {K' : Etale.DerivedCategoryModule A V'}
    (b : (Etale.upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj L ⟶ K)
    (b' : (Etale.upperStar (ModuleCat.{u + 1} A) q').leftDerivedFunctor.obj L' ⟶ K')
    (cL : (Etale.upperStar (ModuleCat.{u + 1} A) z).leftDerivedFunctor.obj L ≅ L')
    (cK : (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K ≅ K')
    (hb : (Etale.upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.map b ≫
      cK.hom = (Etale.sectionCoherencePullbackIso A r q q' z hq L).hom ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) q').leftDerivedFunctor.map cL.hom ≫ b') :
    (Etale.upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.map
        ((Etale.sectionCoherencePullbackIso A a t s q h L).hom ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map b) ≫
      (Etale.sectionCoherencePullbackIso A u' s s' r hs K).hom ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map cK.hom =
    (Etale.sectionCoherencePullbackIso A u' a a' v ha
        ((Etale.upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.obj L)).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.map
        ((Etale.sectionCoherencePullbackIso A v t t' z ht L).hom ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) t').leftDerivedFunctor.map cL.hom) ≫
      (Etale.sectionCoherencePullbackIso A a' t' s' q' h' L').hom ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map b' := by
  let C := ModuleCat.{u + 1} A
  let U := (Etale.upperStar C u').leftDerivedFunctor
  let S := (Etale.upperStar C s).leftDerivedFunctor
  let S' := (Etale.upperStar C s').leftDerivedFunctor
  let R := (Etale.upperStar C r).leftDerivedFunctor
  have hn := ((Etale.leftDerivedUpperStarComp C u' s).symm ≪≫
    Etale.leftDerivedUpperStarComp C s' r (u' ≫ s) hs).hom.naturality b
  change U.map (S.map b) ≫
      (Etale.sectionCoherencePullbackIso A u' s s' r hs K).hom =
    (Etale.sectionCoherencePullbackIso A u' s s' r hs _).hom ≫
      S'.map (R.map b) at hn
  have hc := section_square_cube A a a' t t' s s' q q' u' v r z h h' ha ht hs hq L
  have hn' := ((Etale.leftDerivedUpperStarComp C a' t').symm ≪≫
    Etale.leftDerivedUpperStarComp C s' q' (a' ≫ t') h').hom.naturality cL.hom
  change (Etale.upperStar C a').leftDerivedFunctor.map
      ((Etale.upperStar C t').leftDerivedFunctor.map cL.hom) ≫
      (Etale.sectionCoherencePullbackIso A a' t' s' q' h' L').hom =
    (Etale.sectionCoherencePullbackIso A a' t' s' q' h' _).hom ≫
      S'.map ((Etale.upperStar C q').leftDerivedFunctor.map cL.hom) at hn'
  dsimp only [C, U, S, S', R] at hn hn'
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, hb]
  simp only [Functor.map_comp]
  rw [reassoc_of% hc, ← reassoc_of% hn']





set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem tensorComparison_hom (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {X : Scheme.{u}} {K K' M M' : D P.Coefficient P X} (a : K ≅ K') (b : M ≅ M') :
    (tensorComparison P.Coefficient P a b).hom =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) a.hom b.hom := rfl

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem tensorRestriction_natural (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (hf : u' ≫ f = f' ≫ v)
    {K L : D P.Coefficient P X} {K' L' : D P.Coefficient P X'}
    {M N : D P.Coefficient P Y} {M' N' : D P.Coefficient P Y'}
    (a : K ≅ L) (a' : K' ≅ L') (b : M ≅ N) (b' : M' ≅ N')
    (cK : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.obj
      K ≅ K')
    (cL : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.obj
      L ≅ L')
    (cM : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj
      M ≅ M')
    (cN : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj
      N ≅ N')
    (ha : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.map
      a.hom ≫ cL.hom = cK.hom ≫ a'.hom)
    (hb : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.map
      b.hom ≫ cN.hom = cM.hom ≫ b'.hom) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.map
      (tensorComparison P.Coefficient P a
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          b)).hom ≫
        (tensorRestriction P.Coefficient P f f' u' v hf L N L' N' cL cN).hom =
    (tensorRestriction P.Coefficient P f f' u' v hf K M K' M' cK cM).hom ≫
      (tensorComparison P.Coefficient P a'
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f').leftDerivedFunctor.mapIso
          b')).hom := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let U := (Etale.upperStar A u').leftDerivedFunctor
  let V := (Etale.upperStar A v).leftDerivedFunctor
  let F := (Etale.upperStar A f).leftDerivedFunctor
  let F' := (Etale.upperStar A f').leftDerivedFunctor
  let sq := (Etale.leftDerivedUpperStarComp A u' f).symm ≪≫
    Etale.leftDerivedUpperStarComp A f' v (u' ≫ f) hf
  have hn := sq.hom.naturality b.hom
  change U.map (F.map b.hom) ≫ sq.hom.app N =
    sq.hom.app M ≫ F'.map (V.map b.hom) at hn
  have hsecond : U.map (F.map b.hom) ≫ sq.hom.app N ≫ F'.map cN.hom =
      sq.hom.app M ≫ F'.map cM.hom ≫ F'.map b'.hom := by
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← F'.map_comp, hb, F'.map_comp]
  simp only [tensorRestriction, Iso.trans_hom, tensorComparison_hom,
    Functor.mapIso_hom]
  rw [Etale.leftDerivedUpperStarTensorIso_hom_naturality_assoc]
  simp only [Category.assoc, Etale.derivedTensorHom_comp]
  congr 2
  simpa only [sq, A, U, F, F', Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, NatTrans.comp_app, Category.assoc] using hsecond



set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem unit_boundedBelow (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) := by
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    (_root_.DerivedCategory.singleFunctorObjUnitIso _) ⟨0, inferInstance⟩

section Alpha
variable (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (d : ℕ) (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (f' : X' ⟶ Y') [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f']
    (u' : X' ⟶ X) [u'.IsOver (Spec (.of P.field.k))] [IsOpenImmersion u']
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of P.field.k))] [IsOpenImmersion v]

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem alpha_natural (hf : u' ≫ f = f' ≫ v)
    (aX : X ⟶ Spec (.of P.field.k)) (aX' : X' ⟶ Spec (.of P.field.k)) :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.map
        (alpha P.Coefficient P d f aX).hom ≫
      (openDualizing P.Coefficient P d f f' u' v hf aX).hom =
    (openSection P.Coefficient P d f f' u' v hf aX).hom ≫
      (alpha P.Coefficient P d f' aX').hom := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let A := ModuleCat.{u + 1} P.Coefficient
  let T := openPair f f' u' v hf
  have hT := openPairProperties f f' u' v hf
  let : IsOpenImmersion T := hT.1
  let : T.IsOver (Spec (.of P.field.k)) := ⟨by
    change T ≫ (pullback.fst f f ≫ (X ↘ Spec (.of P.field.k))) =
      pullback.fst f' f' ≫ (X' ↘ Spec (.of P.field.k))
    rw [← Category.assoc, hT.2.1, Category.assoc, comp_over u' _]⟩
  have hsnd : T ≫ pullback.snd f f = pullback.snd f' f' ≫ u' := by
    simp [T, openPair]
  let O := openDualizing P.Coefficient P d f f' u' v hf aX
  let O₁ := openDualizing P.Coefficient P d (pullback.fst f f)
    (pullback.fst f' f') T u' hT.2.1 (pullback.fst f f ≫ aX)
  let b := beta P.Coefficient P d (IsPullback.of_hasPullback f f).flip aX
  let b' := beta P.Coefficient P d (IsPullback.of_hasPullback f' f').flip aX'
  have hb : (Etale.upperStar A T).leftDerivedFunctor.map b.hom ≫ O₁.hom =
      (Etale.sectionCoherencePullbackIso P.Coefficient T (pullback.snd f f)
        (pullback.snd f' f') u' hsnd (Etale.dualizingComplex P.Coefficient f)).hom ≫
      (Etale.upperStar A (pullback.snd f' f')).leftDerivedFunctor.map O.hom ≫
      b'.hom := by
    obtain ⟨_, _, _, _, _, _, _, hb, _⟩ :=
      ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality P
    have hx := hb f d (pullback.fst f f) d f (pullback.snd f f)
      f' d (pullback.fst f' f') d f' (pullback.snd f' f')
      u' v T u' (IsPullback.of_hasPullback f f).flip
      (IsPullback.of_hasPullback f' f').flip ⟨hf⟩ ⟨hT.2.1⟩ ⟨hsnd⟩ ⟨hf⟩
    rw [pullSquare_eq P T (pullback.snd f f) (pullback.snd f' f') u' hsnd] at hx
    rw [← openDualizing_eq P d f f' u' v hf aX,
      ← openDualizing_eq P d (pullback.fst f f) (pullback.fst f' f')
        T u' hT.2.1 (pullback.fst f f ≫ aX)] at hx
    exact hx
  have hx := section_comparison_natural P.Coefficient u' (pullback.snd f f)
    (pullback.snd f' f') T (pullback.diagonal f) (pullback.diagonal f')
    hsnd hT.2.2.symm (pullback.diagonal_snd f) (pullback.diagonal_snd f')
    b b' O₁ O hb
  simpa only [alpha, finiteDiagonalRestriction, openSection, O, O₁, b, b', beta,
    diagonalSection, T,
    Etale.sectionCoherencePullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using hx

end Alpha

section Triple
variable (P : PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))] [Z'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z' ↘ Spec (.of P.field.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsNoetherian X'] [IsNoetherian Y'] [IsNoetherian Z']
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [f'.IsOver (Spec (.of P.field.k))] [g'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    [u'.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
    [w.IsOver (Spec (.of P.field.k))]
    [IsOpenImmersion u'] [IsOpenImmersion v] [IsOpenImmersion w]
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
omit [AlgebraicGeometry.IsNoetherian X] in
private theorem sigma_hom_eq
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    (aX : X ⟶ Spec (.of P.field.k)) :
    (sigma P.Coefficient P d f g aX).hom =
      ProEtale.FiniteEtaleNormalization.sigma P.Coefficient f g (comp P f g) := by
  rfl

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
private theorem sigma_natural
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (aX' : X' ⟶ Spec (.of P.field.k)) :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.map
        (sigma P.Coefficient P d f g aX).hom ≫
      (openDualizing P.Coefficient P (d + e) (f ≫ g) (f' ≫ g') u' w
        (compositeSquare f g f' g' u' v w hf hg) aX).hom =
    (tensorRestriction P.Coefficient P f f' u' v hf _ _ _ _
      (openDualizing P.Coefficient P d f f' u' v hf aX)
      (openDualizing P.Coefficient P e g g' v w hg aY)).hom ≫
      (sigma P.Coefficient P d f' g' aX').hom := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  obtain ⟨_, _, _, _, _, hs, _, _, _⟩ :=
    ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality P
  have hx := hs f d g e f' d g' e u' v w ⟨hf⟩ ⟨hg⟩
  rw [pullSquare_eq P u' f f' v hf] at hx
  rw [← openDualizing_eq P d f f' u' v hf aX,
    ← openDualizing_eq P e g g' v w hg aY,
    ← openDualizing_eq P (d + e) (f ≫ g) (f' ≫ g') u' w
      (compositeSquare f g f' g' u' v w hf hg) aX] at hx
  simpa only [sigma_hom_eq, tensorRestriction, tensorComparison_hom,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Etale.sectionCoherencePullbackIso, Iso.app_inv, Category.assoc] using hx

end Triple

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
/-- The seven open naturality squares for diagonal section pasting.
Source: composition coherence Step 1, diagonal section pasting proof Steps 6--7
(blueprint: lem-route-diagonal-section-pasting-open).

Proof: identify the chosen source-etale comparison with the canonical normalized
one by uniqueness. Source-etale composition and exceptional associativity identify
openDualizing with canonical open restriction. Apply the existing OpenBeta and
OpenSigma laws. Pullback compositor and section coherence yield the three alpha
and two gamma squares. For kappa, recover the etale global pasting equations before
and after restriction by comparison faithfulness, tensor the alpha squares, paste
with the sigma square and cancel the restricted alpha. Apply the comparison
functor to all seven equalities. All restriction squares are merely compatible;
only the defining beta squares are Cartesian. Empty opens and dimension zero use
the same identities. -/
theorem diagonalSectionPastingOpen (P : PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsNoetherian X'] [IsNoetherian Y'] [IsNoetherian Z']
    [IsOpenImmersion u'] [IsOpenImmersion v] [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    OpenEquation P.Coefficient P d e f g f' g' u' v w hf hg aZ := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  let : Y.Over (Spec (.of P.field.k)) := ⟨g ≫ aZ⟩
  let : X.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ aZ⟩
  let : Z'.Over (Spec (.of P.field.k)) := ⟨w ≫ aZ⟩
  let : Y'.Over (Spec (.of P.field.k)) := ⟨v ≫ g ≫ aZ⟩
  let : X'.Over (Spec (.of P.field.k)) := ⟨u' ≫ f ≫ g ≫ aZ⟩
  let : LocallyOfFiniteType (Z ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType aZ)
  let : QuasiCompact (Z ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aZ)
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (g ≫ aZ))
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (g ≫ aZ))
  let : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (f ≫ g ≫ aZ))
  let : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (f ≫ g ≫ aZ))
  let : LocallyOfFiniteType (Z' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (w ≫ aZ))
  let : QuasiCompact (Z' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (w ≫ aZ))
  let : LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (v ≫ g ≫ aZ))
  let : QuasiCompact (Y' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (v ≫ g ≫ aZ))
  let : LocallyOfFiniteType (X' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (u' ≫ f ≫ g ≫ aZ))
  let : QuasiCompact (X' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (u' ≫ f ≫ g ≫ aZ))
  let : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : u'.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : v.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : w.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : f'.IsOver (Spec (.of P.field.k)) := ⟨by
    change f' ≫ v ≫ g ≫ aZ = u' ≫ f ≫ g ≫ aZ
    rw [← Category.assoc f' v, ← hf, Category.assoc]⟩
  let : g'.IsOver (Spec (.of P.field.k)) := ⟨by
    change g' ≫ w ≫ aZ = v ≫ g ≫ aZ
    rw [← Category.assoc g' w, ← hg, Category.assoc]⟩
  let hgeom := geometryProperties d e f g
  let := hgeom.1
  let := hgeom.2.1
  let := hgeom.2.2.1
  let := hgeom.2.2.2.1
  let := hgeom.2.2.2.2
  let hgeom' := geometryProperties d e f' g'
  let := hgeom'.1
  let := hgeom'.2.1
  let := hgeom'.2.2.1
  let := hgeom'.2.2.2.1
  let := hgeom'.2.2.2.2
  let hfg := compositeSquare f g f' g' u' v w hf hg
  let S₁ := openSection P.Coefficient P d f f' u' v hf (f ≫ g ≫ aZ)
  let S₂ := openSection P.Coefficient P e g g' v w hg (g ≫ aZ)
  let S₃ := openSection P.Coefficient P (d + e) (f ≫ g) (f' ≫ g') u' w hfg (f ≫ g ≫ aZ)
  let O₁ := openDualizing P.Coefficient P d f f' u' v hf (f ≫ g ≫ aZ)
  let O₂ := openDualizing P.Coefficient P e g g' v w hg (g ≫ aZ)
  let O₃ := openDualizing P.Coefficient P (d + e) (f ≫ g) (f' ≫ g') u' w hfg (f ≫ g ≫ aZ)
  let R := openMiddle f g f' g' u' v w hf hg
  let T := openPair (f ≫ g) (f' ≫ g') u' w hfg
  let hR := openMiddleProperties f g f' g' u' v w hf hg
  let := hR.1
  let hT := openPairProperties (f ≫ g) (f' ≫ g') u' w hfg
  let := hT.1
  let Oa := openDualizing P.Coefficient P d (a f g) (a f' g') T R hR.2.1
    (pullback.fst (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ)
  let Ob := openDualizing P.Coefficient P e (pullback.fst (f ≫ g) g)
    (pullback.fst (f' ≫ g') g') R u' hR.2.2.1
    (pullback.fst (f ≫ g) g ≫ f ≫ g ≫ aZ)
  let Ta := pullbackRestriction P.Coefficient P (pullback.diagonal (f ≫ g))
    (pullback.diagonal (f' ≫ g')) u' T hT.2.2.symm _ _ Oa
  let Tb := pullbackRestriction P.Coefficient P (s f g) (s f' g') u' R hR.2.2.2 _ _ Ob
  let Sg := pullbackRestriction P.Coefficient P f f' u' v hf _ _ S₂
  let U := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor
  let V := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor
  change SameProEtaleMap P.Coefficient P (U.map (alpha P.Coefficient P d f (f ≫ g ≫ aZ)).hom ≫
    O₁.hom)
      (S₁.hom ≫ (alpha P.Coefficient P d f' (u' ≫ f ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap P.Coefficient P (V.map (alpha P.Coefficient P e g (g ≫ aZ)).hom ≫ O₂.hom)
      (S₂.hom ≫ (alpha P.Coefficient P e g' (v ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap P.Coefficient P (U.map (alpha P.Coefficient P (d + e) (f ≫ g) (f ≫ g ≫ aZ)).hom
    ≫ O₃.hom)
      (S₃.hom ≫ (alpha P.Coefficient P (d + e) (f' ≫ g') (u' ≫ f ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap P.Coefficient P (U.map (sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom ≫ O₃.hom)
      ((tensorRestriction P.Coefficient P f f' u' v hf _ _ _ _ O₁ O₂).hom ≫
        (sigma P.Coefficient P d f' g' (u' ≫ f ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap P.Coefficient P (U.map (kappa P.Coefficient P d e f g aZ).hom ≫ S₃.hom)
      ((tensorRestriction P.Coefficient P f f' u' v hf _ _ _ _ S₁ S₂).hom ≫
        (kappa P.Coefficient P d e f' g' (w ≫ aZ)).hom) ∧
  SameProEtaleMap P.Coefficient P (U.map (gammaF P.Coefficient P d f g aZ).hom ≫ Ta.hom)
      (S₁.hom ≫ (gammaF P.Coefficient P d f' g' (w ≫ aZ)).hom) ∧
  SameProEtaleMap P.Coefficient P (U.map (gammaG P.Coefficient P e f g aZ).hom ≫ Tb.hom)
      (Sg.hom ≫ (gammaG P.Coefficient P e f' g' (w ≫ aZ)).hom)
  have ha₁ := alpha_natural P d f f' u' v hf (f ≫ g ≫ aZ) (u' ≫ f ≫ g ≫ aZ)
  have ha₂ := alpha_natural P e g g' v w hg (g ≫ aZ) (v ≫ g ≫ aZ)
  have ha₃ := alpha_natural P (d + e) (f ≫ g) (f' ≫ g') u' w hfg
    (f ≫ g ≫ aZ) (u' ≫ f ≫ g ≫ aZ)
  have hsigma := sigma_natural P d e f g f' g' u' v w hf hg
    (f ≫ g ≫ aZ) (g ≫ aZ) (u' ≫ f ≫ g ≫ aZ)
  let Tf := openPair f f' u' v hf
  let Tg := openPair g g' v w hg
  have hTf := openPairProperties f f' u' v hf
  have hTg := openPairProperties g g' v w hg
  let : IsOpenImmersion Tf := hTf.1
  let : IsOpenImmersion Tg := hTg.1
  let : R.IsOver (Spec (.of P.field.k)) := ⟨by
    change R ≫ (pullback.fst (f ≫ g) g ≫ (X ↘ Spec (.of P.field.k))) =
      pullback.fst (f' ≫ g') g' ≫ (X' ↘ Spec (.of P.field.k))
    rw [← Category.assoc, hR.2.2.1, Category.assoc, comp_over u' _]⟩
  let : T.IsOver (Spec (.of P.field.k)) := ⟨by
    change T ≫ (pullback.fst (f ≫ g) (f ≫ g) ≫ (X ↘ Spec (.of P.field.k))) =
      pullback.fst (f' ≫ g') (f' ≫ g') ≫ (X' ↘ Spec (.of P.field.k))
    rw [← Category.assoc, hT.2.1, Category.assoc, comp_over u' _]⟩
  let : Tf.IsOver (Spec (.of P.field.k)) := ⟨by
    change Tf ≫ (pullback.fst f f ≫ (X ↘ Spec (.of P.field.k))) =
      pullback.fst f' f' ≫ (X' ↘ Spec (.of P.field.k))
    rw [← Category.assoc, hTf.2.1, Category.assoc, comp_over u' _]⟩
  let : Tg.IsOver (Spec (.of P.field.k)) := ⟨by
    change Tg ≫ (pullback.fst g g ≫ (Y ↘ Spec (.of P.field.k))) =
      pullback.fst g' g' ≫ (Y' ↘ Spec (.of P.field.k))
    rw [← Category.assoc, hTg.2.1, Category.assoc, comp_over v _]⟩
  have hi : Tf ≫ i f g = i f' g' ≫ T := by
    apply pullback.hom_ext <;> simp [Tf, T, i, openPair, pullback.map, Category.assoc]
  have hj : R ≫ j f g = j f' g' ≫ Tg := by
    apply pullback.hom_ext <;>
      simp [R, Tg, j, openMiddle, openPair, pullback.map, Category.assoc, hf]
  let cF := openDualizing P.Coefficient P d (pullback.fst f f)
    (pullback.fst f' f') Tf u' hTf.2.1 (pullback.fst f f ≫ f ≫ g ≫ aZ)
  let cG := openDualizing P.Coefficient P e (pullback.fst g g)
    (pullback.fst g' g') Tg v hTg.2.1 (pullback.fst g g ≫ g ≫ aZ)
  let bF := beta P.Coefficient P d (geometry f g).1
    (pullback.fst (f ≫ g) (f ≫ g) ≫ (f ≫ g) ≫ aZ)
  let bF' := beta P.Coefficient P d (geometry f' g').1
    (pullback.fst (f' ≫ g') (f' ≫ g') ≫ (f' ≫ g') ≫ w ≫ aZ)
  let bG := beta P.Coefficient P e (geometry f g).2.1
    (pullback.fst g g ≫ g ≫ aZ)
  let bG' := beta P.Coefficient P e (geometry f' g').2.1
    (pullback.fst g' g' ≫ g' ≫ w ≫ aZ)
  obtain ⟨_, _, _, _, _, _, _, hbeta, _⟩ :=
    ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality P
  have hbF : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) Tf).leftDerivedFunctor.map
        bF.hom ≫ cF.hom =
      (Etale.sectionCoherencePullbackIso P.Coefficient Tf (i f g) (i f' g') T hi
        (Etale.dualizingComplex P.Coefficient (a f g))).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (i f' g')).leftDerivedFunctor.map
        Oa.hom ≫ bF'.hom := by
    have hx := hbeta (a f g) d (pullback.fst f f) d (s f g) (i f g)
      (a f' g') d (pullback.fst f' f') d (s f' g') (i f' g')
      T R Tf u' (geometry f g).1 (geometry f' g').1
      ⟨hR.2.1⟩ ⟨hTf.2.1⟩ ⟨hi⟩ ⟨hR.2.2.2⟩
    rw [pullSquare_eq P Tf (i f g) (i f' g') T hi] at hx
    rw [← openDualizing_eq P d (a f g) (a f' g') T R hR.2.1
        (pullback.fst (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ),
      ← openDualizing_eq P d (pullback.fst f f) (pullback.fst f' f') Tf u' hTf.2.1
        (pullback.fst f f ≫ f ≫ g ≫ aZ)] at hx
    exact hx
  have hbG : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) R).leftDerivedFunctor.map
        bG.hom ≫ Ob.hom =
      (Etale.sectionCoherencePullbackIso P.Coefficient R (j f g) (j f' g') Tg hj
        (Etale.dualizingComplex P.Coefficient (pullback.fst g g))).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (j f' g')).leftDerivedFunctor.map
        cG.hom ≫ bG'.hom := by
    have hx := hbeta (pullback.fst g g) e (pullback.fst (f ≫ g) g) e f (j f g)
      (pullback.fst g' g') e (pullback.fst (f' ≫ g') g') e f' (j f' g')
      Tg v R u' (geometry f g).2.1 (geometry f' g').2.1
      ⟨hTg.2.1⟩ ⟨hR.2.2.1⟩ ⟨hj⟩ ⟨hf⟩
    rw [pullSquare_eq P R (j f g) (j f' g') Tg hj] at hx
    rw [← openDualizing_eq P e (pullback.fst g g) (pullback.fst g' g') Tg v hTg.2.1
        (pullback.fst g g ≫ g ≫ aZ),
      ← openDualizing_eq P e (pullback.fst (f ≫ g) g) (pullback.fst (f' ≫ g') g')
        R u' hR.2.2.1 (pullback.fst (f ≫ g) g ≫ f ≫ g ≫ aZ)] at hx
    exact hx
  have hgammaF : U.map (gammaF P.Coefficient P d f g aZ).hom ≫ Ta.hom =
      S₁.hom ≫ (gammaF P.Coefficient P d f' g' (w ≫ aZ)).hom := by
    have hx := section_composite_natural P.Coefficient u'
      (pullback.diagonal f) (pullback.diagonal f')
      (pullback.diagonal (f ≫ g)) (pullback.diagonal (f' ≫ g'))
      (i f g) (i f' g') Tf T hTf.2.2.symm hT.2.2.symm hi
      (geometry f g).2.2.2.2.1 (geometry f' g').2.2.2.2.1 bF bF' cF Oa hbF
    simpa only [gammaF, openSection, pullbackRestriction, S₁, Ta, cF, bF, bF', beta,
      Etale.sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc, Tf] using hx
  have hgammaG : U.map (gammaG P.Coefficient P e f g aZ).hom ≫ Tb.hom =
      Sg.hom ≫ (gammaG P.Coefficient P e f' g' (w ≫ aZ)).hom := by
    have hx := section_square_map_natural P.Coefficient f f'
      (pullback.diagonal g) (pullback.diagonal g') (s f g) (s f' g')
      (j f g) (j f' g') u' v R Tg
      (geometry f g).2.2.2.2.2.symm (geometry f' g').2.2.2.2.2.symm
      hf hTg.2.2.symm hR.2.2.2 hj bG.hom bG'.hom cG Ob hbG
    simpa only [gammaG, openSection, pullbackRestriction, Sg, S₂, Tb, cG, bG, bG', beta,
      Etale.sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc, Tg, U, diagonalSection,
        Etale.sectionInvariant] using hx
  have hunit : _root_.DerivedCategory.TStructure.t.plus
      (ProEtale.FiniteEtaleNormalization.coefficientUnit
        (ModuleCat.{u + 1} P.Coefficient) Z) :=
    unit_boundedBelow P.Coefficient Z
  have hplus := Etale.plus_rightDerivedUpperShriek_obj P.Coefficient (f ≫ g) _ hunit
  have hE₀ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hplus).1
    (diagonalSectionPastingEquation P d e f g aZ)
  have hE : (kappa P.Coefficient P d e f g aZ).hom ≫
      (alpha P.Coefficient P (d + e) (f ≫ g) (f ≫ g ≫ aZ)).hom =
    (tensorComparison P.Coefficient P (alpha P.Coefficient P d f (f ≫ g ≫ aZ))
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (alpha P.Coefficient P e g (g ≫ aZ)))).hom ≫
      (sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom := by
    simpa only [alpha, Etale.dualizingComplex, coefficientUnit] using hE₀
  have hunit' : _root_.DerivedCategory.TStructure.t.plus
      (ProEtale.FiniteEtaleNormalization.coefficientUnit
        (ModuleCat.{u + 1} P.Coefficient) Z') :=
    unit_boundedBelow P.Coefficient Z'
  have hplus' := Etale.plus_rightDerivedUpperShriek_obj P.Coefficient (f' ≫ g') _ hunit'
  have hE₀' := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hplus').1
    (diagonalSectionPastingEquation P d e f' g' (w ≫ aZ))
  have hE' : (kappa P.Coefficient P d e f' g' (w ≫ aZ)).hom ≫
      (alpha P.Coefficient P (d + e) (f' ≫ g') (u' ≫ f ≫ g ≫ aZ)).hom =
    (tensorComparison P.Coefficient P
      (alpha P.Coefficient P d f' (u' ≫ f ≫ g ≫ aZ))
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f').leftDerivedFunctor.mapIso
        (alpha P.Coefficient P e g' (v ≫ g ≫ aZ)))).hom ≫
      (sigma P.Coefficient P d f' g' (u' ≫ f ≫ g ≫ aZ)).hom := by
    simpa only [alpha, sigma_hom_eq, Etale.dualizingComplex, coefficientUnit] using hE₀'
  have htensor := tensorRestriction_natural P f f' u' v hf
    (alpha P.Coefficient P d f (f ≫ g ≫ aZ))
    (alpha P.Coefficient P d f' (u' ≫ f ≫ g ≫ aZ))
    (alpha P.Coefficient P e g (g ≫ aZ))
    (alpha P.Coefficient P e g' (v ≫ g ≫ aZ)) S₁ O₁ S₂ O₂ ha₁ ha₂
  have hkappa : U.map (kappa P.Coefficient P d e f g aZ).hom ≫ S₃.hom =
      (tensorRestriction P.Coefficient P f f' u' v hf _ _ _ _ S₁ S₂).hom ≫
        (kappa P.Coefficient P d e f' g' (w ≫ aZ)).hom := by
    apply (cancel_mono
      (alpha P.Coefficient P (d + e) (f' ≫ g') (u' ≫ f ≫ g ≫ aZ)).hom).1
    simp only [Category.assoc]
    rw [← ha₃, ← U.map_comp_assoc, hE, U.map_comp, Category.assoc,
      hsigma, reassoc_of% htensor, hE']
  let CX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
    X').mapDerivedCategory
  let CY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
    Y').mapDerivedCategory
  refine ⟨congrArg CX.map ha₁, congrArg CY.map ha₂, congrArg CX.map ha₃,
    congrArg CX.map hsigma, congrArg CX.map hkappa,
    congrArg CX.map hgammaF, congrArg CX.map hgammaG⟩

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
