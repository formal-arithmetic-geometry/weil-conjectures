/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingSigmaCocycleLocality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionEtaleFunctorial
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
public import WeilConjectures.AlgebraicGeometry.SmoothExceptionalPasting.SmoothExceptionalTensorPasting
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorMateBaseChange

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

section Geometry
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]

end Geometry

namespace OpenRestrictionBeta
open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
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
end OpenRestrictionBeta

open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
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

private theorem pullSquare_eq (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}} (u' : X' ⟶ X) (f : X ⟶ Y)
    (f' : X' ⟶ Y') (v : Y' ⟶ Y) (h : u' ≫ f = f' ≫ v)
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    (ProEtale.DualizingLocality.pullSquare P u' f' f v ⟨h⟩).hom.app K =
      (Etale.sectionCoherencePullbackIso P.Coefficient u' f f' v h K).hom := by
  exact congrArg Iso.hom (Etale.sectionPullback_endpoint P.Coefficient u' f f' v
    (f' ≫ v) (u' ≫ f) h.symm rfl rfl h K)

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

private theorem tensorComparison_hom (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {X : Scheme.{u}} {K K' M M' : D P.Coefficient P X} (a : K ≅ K') (b : M ≅ M') :
    (tensorComparison P.Coefficient P a b).hom =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) a.hom b.hom := rfl

private theorem sigma_hom_eq
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    (aX : X ⟶ Spec (.of P.field.k)) :
    (sigma P.Coefficient P d f g aX).hom =
      ProEtale.FiniteEtaleNormalization.sigma P.Coefficient f g (comp P f g) := by
  rfl

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
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
end Open

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
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
set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
end Triple

set_option maxHeartbeats 1500000 in
-- Allow the derived-functor coherence expressions a larger elaboration budget.
end WeilConjectures.PurityFiniteSetting.DiagonalPasting
