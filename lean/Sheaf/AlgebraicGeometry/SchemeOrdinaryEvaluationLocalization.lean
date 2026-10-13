/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom

/-! # Localization of the ordinary evaluation equation
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-scheme-ordinary-evaluation-localization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- The ordinary-to-derived Hom map obtained from the fixed resolution augmentation.
This constructs a morphism without choosing any comparison witness.
Source: Stacks Project, Tag 08DJ.
(blueprint: lem-pc-scheme-ordinary-evaluation-localization). -/
def schemeOrdinaryHomComparison (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := Y.sheaf) P M) ⟶
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M) := by
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  exact DerivedCategory.Q.map (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map
    ((CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).app M)) ≫
    (schemeDerivedInternalHomResolutionIso Y P M).inv

/-- Localizing the componentwise ordinary evaluation gives its uncurried derived map.
No Hom-exactness, K-flatness, or invertibility of the comparison maps is asserted.
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ; representative calculation.
(blueprint: lem-pc-scheme-ordinary-evaluation-localization).

Proof: resolve both tensor inputs by K-flat complexes and the coefficient by the
fixed K-injective functor. Apply the canonical tensor-Hom representative equation.
Precompose with each total-tensor summand and postcompose with each Hom projection.
Naturality of evaluation with the coefficient augmentation and the resolution maps
reduces the equation to hf: the unit is supported in degree zero, so the component
is the unit action when r+q=0 and zero otherwise. The coproduct inclusions and product
projections detect equality. Localize and cancel the quasi-isomorphisms of the
K-flat resolutions and coefficient resolution. The unit identification is the
quotient comparison at the single complex. Finally apply three-variable naturality
of the canonical family along eK and eN. This proves a morphism equation without
inverting the ordinary Hom or tensor comparisons. For zero complexes or the empty
scheme the same component equations hold, with all maps zero. -/
theorem schemeOrdinaryEvaluation_localization (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K N : schemeDerivedCategory Y)
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj F ≅ N)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) :
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let c := schemeOrdinaryHomComparison Y P F ≫ H.map (eK.inv.op, eN.hom)
    let d := schemeOrdinaryHomComparison Y P O ≫
      H.map (eK.inv.op, ((DerivedCategory.quotientCompQhIso _).app O).inv)
    schemeDerivedTensorHomEquiv Y (N ⊗ DerivedCategory.Q.obj V) K N
        ((eN.inv ▷ DerivedCategory.Q.obj V) ≫ pullbackTensorModelMap Y F V ≫
          DerivedCategory.Q.map f ≫ c) =
      (α_ N (DerivedCategory.Q.obj V) K).hom ≫ N ◁
        (schemeDerivedTensorHomEquiv Y (DerivedCategory.Q.obj V) K
          (𝟙_ (schemeDerivedCategory Y)) d) ≫ (ρ_ N).hom := by sorry

end AlgebraicGeometry
