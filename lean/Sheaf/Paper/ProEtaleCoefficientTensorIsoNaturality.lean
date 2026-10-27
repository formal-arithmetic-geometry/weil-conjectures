/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProEtaleCoefficientPullback
public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import Sheaf.Algebra.Homology.TensorTotalComparisonSquare

/-! # Naturality of normalized coefficient restriction on total tensor complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- Naturality of the given normalized total comparison.
Source: RingIsoTensorTransport.total_naturality
(blueprint: lem-pbc-coefficient-restriction-tensor-iso-naturality). -/
theorem tensorIso_naturality (o : SheafOfModules.RingIsoTensorTransport
    (J := ProEt.topology X)
    (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (Z W : CochainComplex (proEtaleRingModules X S) ℤ ×
      CochainComplex (proEtaleRingModules X S) ℤ) (v : Z ⟶ W) :
    (total X S ⋙ (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).map v ≫
        (o.totalIso W.1 W.2).hom =
      (o.totalIso Z.1 Z.2).hom ≫
        (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).prod
          ((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)) ⋙
            total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map v := by
  dsimp only [Functor.comp_map, Functor.prod_map]
  rw [HomologicalComplex.mapTotalBifunctor, HomologicalComplex.mapTotalBifunctor]
  exact o.total_naturality v.1 v.2

end AlgebraicGeometry.Scheme.CoefficientTensorChain
