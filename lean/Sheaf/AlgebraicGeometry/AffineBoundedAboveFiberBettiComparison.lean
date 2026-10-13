/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel
import Sheaf.Topology.PointModuleEvaluationEquivalence
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Fibre Betti numbers of a supplied affine bounded-above free model

Source: Stacks Project, Tags 08DW, 08E7 and 0BDI.
(blueprint: lem-sc-affine-bounded-above-fiber-betti-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A supplied bounded-above free module model on an affine open computes the ambient
object's fibre Betti numbers. No neighbourhood or representative is constructed here.

Source: Stacks Project, Tag 0BDI, proof, affine reduction; Tag 08DW(2), affine derived
pullback; Tag 064K, bounded-above flat complexes are K-flat.
(blueprint: lem-sc-affine-bounded-above-fiber-betti-comparison).

Proof:
1. For z in U, factor the residue-field point through U.toScheme. The over equivalence
   and hU.isoSpec identify the supplied sheafification with the associated sheaf of F.
   Restriction is exact. The given derived isomorphism therefore identifies the local
   restriction of E with Q(tilde F). Derived pullback commutes with open restriction.
2. Free modules are flat, and the supplied upper bound makes F K-flat. The affine
   derived-pullback formula identifies pullback of Q(tilde F) with Q of the associated
   sheaf of F tensor_A kappa(p), where p = hU.isoSpec.hom z. The residue-field isomorphism
   of the open immersion and that of Spec identify this field with X.residueField z.
   These identifications commute with the ring maps from A: the map sends a section
   to its germ followed by its residue, equivalently to its value at p.
3. Apply degree-i cohomology. Associated sheaves are exact, and on the spectrum of a
   field evaluation at the whole space recovers the module. Thus the resulting vector
   space is homology of the termwise scalar extension of F. The scalar transport in
   derivedFiberCohomology is precisely the inverse of GammaSpecIso. Transport along the
   above residue-field isomorphism gives a semilinear bijection, so the two finranks
   agree. This holds for every integer i, including i above the upper bound, where both
   spaces vanish. Rank zero and the zero complex cause no change; if U is empty there
   is no z. No lower bound, finite-dimensionality assumption, or pseudo-coherence of E
   is needed once the representative is supplied. -/
theorem affine_boundedAbove_fiberBetti_eq (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (U : X.Opens) (hU : IsAffineOpen U)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (b : ℤ) (hb : F.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free (X.presheaf.obj (.op U)) (F.X n))
    (hmodel : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj F)))
    (i : ℤ) (z : U) :
    derivedFiberBetti X E i z =
      Module.finrank (hU.isoSpec.hom z).asIdeal.ResidueField
        ((((ModuleCat.extendScalars
          (algebraMap (X.presheaf.obj (.op U))
            (hU.isoSpec.hom z).asIdeal.ResidueField)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F).homology i) := by
  classical
  let A := X.presheaf.obj (.op U)
  let k := X.residueField z
  let p := hU.isoSpec.hom z
  let e : k ≅ CommRingCat.of p.asIdeal.ResidueField :=
    asIso (U.ι.residueFieldMap z) ≪≫
      (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫ Spec.residueFieldIso A p
  let C := ((ModuleCat.extendScalars (algebraMap A p.asIdeal.ResidueField)).mapHomologicalComplex
    (.up ℤ)).obj F
  let R := ModuleCat.restrictScalars e.hom.hom
  let V := (R.mapHomologicalComplex (.up ℤ)).obj C
  have hacyclic := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat F
    ⟨b, (F.isStrictlyLE_iff b).mp hb⟩ (fun n ↦ by
      have := hfree n
      exact Module.Flat.of_free)
  have hF : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat F := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor N F (MonoidalCategory.curriedTensor _))).2
        (hacyclic N hN)
    refine ⟨?_, hr⟩
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr
  let α := Classical.choice (affine_kFlat_residuePullback_model X E U hU F hF hmodel z)
  let S := SheafOfModules.{u} (moduleRings (Spec k).toRingedSpace)
  let Γ : S ⥤ ModuleCat.{u} k :=
    SheafOfModules.evaluation (moduleRings (Spec k).toRingedSpace) (.op ⊤) ⋙
      ModuleCat.restrictScalars (ΓSpecIso k).inv.hom
  have : (RingedSpace.globalSectionsFunctor (Spec k).toRingedSpace).IsEquivalence :=
    RingedSpace.globalSectionsFunctor_isEquivalence_of_unique _
  have : Limits.PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings (Spec k).toRingedSpace) (.op ⊤)) :=
    inferInstanceAs (Limits.PreservesFiniteLimits
      (RingedSpace.globalSectionsFunctor (Spec k).toRingedSpace))
  have : Limits.PreservesFiniteColimits
      (SheafOfModules.evaluation (moduleRings (Spec k).toRingedSpace) (.op ⊤)) :=
    inferInstanceAs (Limits.PreservesFiniteColimits
      (RingedSpace.globalSectionsFunctor (Spec k).toRingedSpace))
  have : Limits.PreservesFiniteLimits Γ := Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteColimits Γ := Limits.comp_preservesFiniteColimits _ _
  have : Γ.PreservesHomology := inferInstance
  let T := tilde.functor k
  let TV := (T.mapHomologicalComplex (.up ℤ)).obj V
  let a : derivedFiberCohomology X E i z ≅ Γ.obj (TV.homology i) :=
    Γ.mapIso ((DerivedCategory.homologyFunctor S i).mapIso α ≪≫
      (DerivedCategory.homologyFunctorFactors S i).app TV)
  have : (moduleSpecΓFunctor (R := k)).Additive :=
    (tilde.adjunction (R := k)).right_adjoint_additive
  let c : ((Γ.mapHomologicalComplex (.up ℤ)).obj TV) ≅ V :=
    (Functor.mapHomologicalComplexCompIso (tilde.toTildeΓNatIso (R := k)).symm
      (.up ℤ)).app V ≪≫ (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} k) (.up ℤ)).app V
  let d := (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) i).mapIso c
  let av : derivedFiberCohomology X E i z ≅ V.homology i :=
    a ≪≫ ((TV.sc i).mapHomologyIso Γ).symm ≪≫ d
  let ar : V.homology i ≅ R.obj (C.homology i) := (C.sc i).mapHomologyIso R
  have hr := (av ≪≫ ar).toLinearEquiv.finrank_eq
  have hdim : Module.rank k (R.obj (C.homology i)) =
      Module.rank p.asIdeal.ResidueField (C.homology i) :=
    rank_eq_of_equiv_equiv e.hom.hom (AddEquiv.refl _) e.commRingCatIsoToRingEquiv.bijective
      (fun _ _ ↦ rfl)
  unfold derivedFiberBetti
  exact hr.trans (congrArg Cardinal.toNat hdim)

end AlgebraicGeometry.Scheme
