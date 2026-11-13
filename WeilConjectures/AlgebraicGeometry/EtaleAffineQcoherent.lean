/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.EtaleULiftInjectiveResolution
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation

/-!
# Étale acyclicity of a quasi-coherent module on an affine scheme

Source: Stacks Project, Étale Cohomology, Theorem 03P2 (affine case).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Higher étale cohomology of the associated quasi-coherent sheaf vanishes on an affine.
(Stacks, Tag 03P2) -/
theorem etale_affine_qcoherent
    (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) q) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let G := Scheme.Modules.etaleTensorSectionsSheaf F
  let L := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let G' := (sheafCompose X.smallEtaleTopology L).obj G
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  have hT : CategoryTheory.Limits.IsTerminal T :=
    CategoryTheory.MorphismProperty.Over.mkIdTerminal _ _
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op T)
  let E' := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op T)
  let R := injectiveResolution G
  obtain ⟨S, hS⟩ := Scheme.exists_etale_ulift_injectiveResolution X G R
  obtain ⟨eS⟩ := hS T
  have hG' : Subsingleton (Sheaf.H G' (n + 1)) :=
    etale_affine_qcoherent_ulift X F (n + 1) (Nat.zero_lt_succ n)
  obtain ⟨e'⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology T hT G' n
  let := hG'
  let : Subsingleton ((E'.rightDerived (n + 1)).obj G') :=
    Function.Injective.subsingleton e'.symm.injective
  have hz : CategoryTheory.Limits.IsZero
      (((E'.mapHomologicalComplex (.up ℕ)).obj S.cocomplex).homology (n + 1)) :=
    CategoryTheory.Limits.IsZero.of_iso
      (AddCommGrpCat.isZero_iff_subsingleton.mpr inferInstance)
      (S.isoRightDerivedObj E' (n + 1)).symm
  have hc := (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso eS
  let hm := ((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).sc (n + 1)
  have ei := (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ L))
    (.up ℕ)).app R.cocomplex
  have hj := (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso ei
  have hl : CategoryTheory.Limits.IsZero
      (L.obj (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))) :=
    CategoryTheory.Limits.IsZero.of_iso hz
      (hc ≪≫ hj.symm ≪≫ hm.mapHomologyIso L).symm
  let : Subsingleton (ULift.{u + 1}
      (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hl
  have hsmall : Subsingleton
      (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1)) :=
    Function.Injective.subsingleton (f := fun x ↦
      (ULift.up x : L.obj
        (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))))
      ULift.up_injective
  obtain ⟨e⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology T hT G n
  exact @Function.Injective.subsingleton _ _ _
    ((R.isoRightDerivedObj E (n + 1)).addCommGroupIsoToAddEquiv.injective.comp e.injective)
    hsmall

end AlgebraicGeometry.Etale
