/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Algebra.Homology.HomComplexProjections
public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Naturality of uncurrying on tensor summands
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

/-- Restricting uncurrying and postcomposition to an arbitrary tensor summand.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation chain calculation, step 3, naturality portion.
(blueprint: lem-pc-scheme-uncurry-summand-naturality).

Proof: Apply schemeTensorHomUncurry_component to the outer inclusion in degrees
n,r,k. Its inverse tensor-Hom expression uses the projection of Hom(P,I(F)).
The naturality equation of homComplex_projections_exists with identity on P and
eta_F on F moves this projection across Hom(P,eta_F). Naturality of uncurrying in
its target moves eta_F to the last factor. Naturality of the symmetric braiding
and of uncurrying in its source then moves the inner tensor inclusion into the
argument of tensorHomEquiv.symm. Reassociate composition to obtain the displayed
formula. Only n+r=k is used for the Hom projection; p+q=n indexes the inclusion.
This argument imposes no boundedness or nonvanishing hypotheses and works for
zero complexes and the empty scheme. -/
theorem schemeTensorHomUncurry_summand_naturality (Y : Scheme.{u})
    (P F V : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F V ⟶ homComplex (R := Y.sheaf) P F)
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
      ≫ HomologicalComplex.ιMapBifunctor (pullbackTensorTotal Y F V) P
        (curriedTensor _) (.up ℤ) n r k hnr ≫
          (schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F
            (f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F))).f k =
    (β_ (F.X p ⊗ V.X q) (P.X r)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (F.X p ⊗ V.X q)
        (F.X k)).symm
        (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ≫
          f.f n ≫ π P F n r k (by omega)) ≫ (eta.app F).f k := by sorry

end AlgebraicGeometry
