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

/-! # Open restrictions of diagonal section pasting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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

end OpenRestrictionBeta

open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

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

end Open

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

end Triple

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
