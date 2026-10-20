/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.Paper.RingedRefinementData

/-!
# Canonical coefficients and refinement transposes

Source: Stacks 03D7 and 07A6
(blueprint: lem-pur-ringed-refinement-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

set_option backward.isDefEq.respectTransparency false in
/-- Coefficients induced by the actual fibre-product associator.
Source: Stacks 03D7
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def canonicalCoefficients (m : Mode) (T : Scheme.{u}) : Coefficients m T where
  directTriangle f := Functor.sheafPushforwardContinuousComp'
    (siteTriangle m f).symm CommRingCat.{u + 1}
      (topology m T) (topology m _) (topology m _)
  sections f R W := by
    simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv]

/-- The natural transformation consisting of the three prescribed clopen factors.
Source: Bhatt--Scholze coefficient supplement, Step 5
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def OpenComparisons.hom {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p)
    {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (d : Shape u j₁ j₂) (R : Rings m T) :
    o.shriek j₂ R ⋙ (o.operation u R).left ⟶ o.shriek j₁ R :=
  (e.beta d.b d.q u j₂ d.pullback R).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (o.operation d.q R).left (e.pi d.s d.clopen R))
      (o.shriek d.b R) ≫
    Functor.whiskerRight (p.sectionPull d R).hom (o.shriek d.s R ⋙ o.shriek d.b R) ≫
    (p.openFactor d.s d.b j₁ d.openFactor R).hom

/-- The refinement is constructed by transposing the actual natural clopen map.
Source: Bhatt--Scholze coefficient supplement; Stacks 07A6
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def canonicalRefinements {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p) : Refinements e where
  map u j₁ j₂ _ _ _ _ _ _h d R :=
    Functor.whiskerLeft (o.shriek j₂ R) (o.operation u R).derivedAdjunction.unit ≫
      Functor.whiskerRight (e.hom d R) (o.operation u R).right
  adjunct u j₁ j₂ _ _ _ _ _ h d R M := by
    change (o.operation u R).derivedAdjunction.homEquiv _ _ (e.h d R M) =
      (o.operation u R).derivedAdjunction.unit.app ((o.shriek j₂ R).obj M) ≫
        (o.operation u R).right.map (e.h d R M)
    exact (o.operation u R).derivedAdjunction.homEquiv_unit _ _ _

end SheafOfModules.RingedRefinement
