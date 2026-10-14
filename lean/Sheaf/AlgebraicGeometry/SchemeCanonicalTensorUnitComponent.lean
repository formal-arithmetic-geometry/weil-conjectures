/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeTensorUnitAction
public import Sheaf.Algebra.Homology.HomComplexProjections
public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # The canonical coefficient formula for a tensor-unit action
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- A tensor-unit action has the canonical dual-projection component formula.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation chain calculation, coefficient cancellation and tensor action.
(blueprint: lem-pc-scheme-canonical-tensor-unit-component).

Proof: Restrict the assumed factorization to V^q tensor P^r. The component
formula for schemeTensorHomUncurry and coefficient naturality of the Hom
projections give the uncurried old projection followed by eta_O. The
augmentation is degreewise monic: monoQuasiIso_toKInjectiveResolution_app
makes it monic as a chain map, and evaluation preserves finite limits.
Cancel it to determine the component of e. For r+q=0, postcompose this
component with singleObjXSelf and use tensor-Hom coefficient naturality to
move this identification inside uncurrying. Restrict the total tensor action
to (F^p tensor V^q) tensor P^r: the total associator acts by the component
associator without a sign, and tensor-map naturality gives the component of e.
The single-unit right unitor is the coefficient identification followed by
rho and XIsoOfEq; the degree equations give p=k. Thus the displayed formula
holds when r+q=0. Otherwise O^(r+q) is zero, so the tensor action component
vanishes. Finally postcompose with eta_F; the component of a composition is
the composition of components. No ordinary evaluation map f, no ordinary
component predicate, no boundedness or flatness, and no existence of e are
used. Zero maps, zero complexes, negative degrees and the empty scheme are
included by the same argument. -/
theorem schemeCanonicalTensorUnit_component (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (e : pullbackTensorTotal Y
      (homComplex (R := Y.sheaf) P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) P ⟶
      (HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    schemeTensorHomUncurry Y V P O
      (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)) =
        e ≫ eta.app O →
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
      ≫ HomologicalComplex.ιMapBifunctor (pullbackTensorTotal Y F V) P
        (curriedTensor _) (.up ℤ) n r k hnr ≫
          (schemeTensorUnitAction Y F V P e ≫ eta.app F).f k =
    (if h : r + q = 0 then
      (α_ (F.X p) (V.X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ (V.X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (V.X q)
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).symm
              (π P O q r 0 h ≫ SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = k)).hom
    else 0) ≫ (eta.app F).f k := by sorry

end AlgebraicGeometry
