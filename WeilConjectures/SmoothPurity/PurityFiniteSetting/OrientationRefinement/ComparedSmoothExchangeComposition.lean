/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence

/-! # Pasting of smooth dualizing exchanges in comparison coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.OrientationRefinement

/-- Changing equal scheme arrows changes only the pullback source identification.
This is dependent equality elimination, with the Cartesian square proof irrelevant.
Source: canonical functorial pullback convention.
(blueprint: lem-pur-compared-smooth-exchange-composition).
-/
theorem exchange_congr (P : PurityFiniteSetting.{u})
    {T S T' S' : Scheme.{u}} (d : ℕ) (g : T ⟶ S) (g' : T' ⟶ S')
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d g]
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (aS' : S' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS'] [QuasiCompact aS']
    {v v₂ : T' ⟶ T} {b b₂ : S' ⟶ S}
    (sq : IsPullback v g' g b) (sq₂ : IsPullback v₂ g' g b₂)
    (hv : v = v₂) (hb : b = b₂) :
    exchange P d g g' aS aS' sq =
      eqToIso (congrArg (fun j ↦ (pull P j).obj (omega P g aS)) hv) ≪≫
        exchange P d g g' aS aS' sq₂ := by
  subst v₂
  subst b₂
  simp only [eqToIso_refl, Iso.refl_trans]

/-- Smooth dualizing exchange respects two successive Cartesian base changes.
Source: blueprint fix-lem-exchanges, mate-pasting, and comparison-pullback coherence.
Proof: the ordinary dualizing exchange obeys mate pasting. Apply the comparison
functor and the derived inverse-image composition law. Naturality moves the first
exchange through the second comparison, giving the displayed composite.

(blueprint: lem-pur-compared-smooth-exchange-composition).
-/
theorem exchange_comp (P : PurityFiniteSetting.{u})
    {T S T' S' T'' S'' : Scheme.{u}}
    (d : ℕ) (g : T ⟶ S) (g' : T' ⟶ S') (g'' : T'' ⟶ S'')
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [IsSeparated g''] [LocallyOfFiniteType g''] [QuasiCompact g'']
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension d g']
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (aS' : S' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS'] [QuasiCompact aS']
    (aS'' : S'' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS''] [QuasiCompact aS'']
    {v : T' ⟶ T} {v' : T'' ⟶ T'} {b : S' ⟶ S} {b' : S'' ⟶ S'}
    (sq : IsPullback v g' g b) (sq' : IsPullback v' g'' g' b') :
    exchange P d g g'' aS aS'' (sq'.paste_horiz sq) =
      (ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) v' v).app (omega P g aS) ≪≫
        (pull P v').mapIso (exchange P d g g' aS aS' sq) ≪≫
        exchange P d g' g'' aS' aS'' sq' := by
  let := P.noetherian aS
  let := P.noetherian aS'
  let := P.noetherian aS''
  let := P.noetherian (g ≫ aS)
  let := P.noetherian (g' ≫ aS')
  let := P.noetherian (g'' ≫ aS'')
  let := Dnc.compactifiable P g aS
  let := Dnc.compactifiable P g' aS'
  let := Dnc.compactifiable P g'' aS''
  have hd := Etale.dualizing_base_comp P.Coefficient sq sq'
  have hp := Dnc.pullComparison_comp P v' v
    (Etale.dualizingComplex P.Coefficient g)
  let η := Functor.isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T').mapDerivedCategory
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) v') ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) v' ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) v').symm
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T'').mapDerivedCategory
  have hn := η.hom.naturality (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)
  change (pull P v').map
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T').mapDerivedCategory.map
          (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)) ≫
        (Dnc.pullComparison P v' _).hom =
      (Dnc.pullComparison P v' _).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T'').mapDerivedCategory.map
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v').leftDerivedFunctor.map
            (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)) at hn
  apply Iso.ext
  dsimp only [exchange, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hp, ← reassoc_of% hn]
  rfl

end WeilConjectures.PurityFiniteSetting.OrientationRefinement
