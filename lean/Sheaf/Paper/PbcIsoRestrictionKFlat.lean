/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import all Sheaf.Paper.IntegralCoefficientPresentationComparison
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # K-flatness under an isomorphism of coefficient sheaves

Source: the coefficient-transport argument in clause (3) of the proof of
prop-trf-rational-frobenius-integral-model, as recorded in step 7 of
lem-trf-point-quotient-tower-homotopy; Stacks Tag 06YN.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

attribute [local instance 10000] essentiallySmall_of_small_of_locallySmall

attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective in
/-- Restriction along a coefficient isomorphism preserves K-flatness.
Source: Stacks Tag 06YN and the coefficient-transport calculation in step 7 of
lem-trf-point-quotient-tower-homotopy
(blueprint: lem-trf-pbc-iso-restriction-kflat).

Proof: ordinary scalar extension along e.inv preserves every K-flat complex by
changeOfRings_isKFlat_independentCoefficients. Restriction along e.hom and e.inv
are inverse equivalences: use the sectionwise restriction compositors and the
identity restriction isomorphism. Consequently restriction along e.hom is left
adjoint to restriction along e.inv. Ordinary extension along e.inv has this same
right adjoint, so uniqueness of left adjoints identifies these two functors.
Apply that natural isomorphism to cochain complexes. Tensoring it with any acyclic
test complex gives an isomorphism of total tensor complexes. Acyclicity transports
along this isomorphism, proving K-flatness of the restricted complex. No flatness
of terms or boundedness is used. The zero complex and zero ring are included. -/
theorem pbcIsoRestriction_isKFlat (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (e : R ≅ S)
    (P : CochainComplex (pbcModules T S) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := S) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((pbcRestrict e.hom).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let F : pbcModules T S ⥤ pbcModules T R := reductionChange T e.inv
  have hK : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    SheafOfModules.changeOfRings_isKFlat_independentCoefficients.{u + 1, u, u + 1}
      e.inv P F (reductionChange_obj_eq T e.inv) (reductionChange_map_eq T e.inv) hP
  obtain ⟨adj, _⟩ := ordinaryAdjunction_exists.{u} T e.inv
  let i : pbcRestrict e.hom ⋙ pbcRestrict e.inv ≅ 𝟭 (pbcModules T S) :=
    pbcRestrictComp e.inv e.hom (𝟙 S) e.inv_hom_id ≪≫
    WeilConjectures.IntegralCoefficientPresentation.restrictId S
  let j : pbcRestrict e.inv ⋙ pbcRestrict e.hom ≅ 𝟭 (pbcModules T R) :=
    pbcRestrictComp e.hom e.inv (𝟙 R) e.hom_inv_id ≪≫
    WeilConjectures.IntegralCoefficientPresentation.restrictId R
  let t : pbcModules T S ≌ pbcModules T R :=
    CategoryTheory.Equivalence.mk (pbcRestrict e.hom) (pbcRestrict e.inv) i.symm j
  let a : F ≅ pbcRestrict e.hom := Adjunction.leftAdjointUniq adj t.toAdjunction
  let c := (NatIso.mapHomologicalComplex a (.up ℤ)).app P
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let : MonoidalCategory (pbcModules T R) := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro G hG n
  exact (hK G hG n).of_iso
    (HomologicalComplex₂.total.mapIso
      ((((MonoidalCategory.curriedTensor (pbcModules T R)).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj G).mapIso c) (.up ℤ))

end AlgebraicGeometry.Scheme
