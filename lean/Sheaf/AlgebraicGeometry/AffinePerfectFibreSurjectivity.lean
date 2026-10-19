/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.AlgebraicGeometry.DegreeZeroFibreSurjective
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Sheaf.AlgebraicGeometry.AffineModelStalkBaseChange
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Fibre-map surjectivity in an affine free representative

Source: Stacks Project, More on Algebra, Tag 0A1U, affine reduction;
Cohomology, Tag 06YB; Cohomology on Sites, Tag 06YS.
(blueprint: lem-sc-affine-perfect-fibre-surjectivity).
-/

@[expose] public section

set_option autoImplicit false
universe u w v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact open stalks transport a supplied local derived model to the original stalk ring.
Source: Stacks Project, Tags 01AG, 008H and 0098. The open stalk-ring map is invertible.
The extension-restriction unit, the restriction-stalk comparison and overFunctorEquiv
therefore identify the two literal stalk complexes. Apply the exact open stalk derived
functor to the given local model and use its comparison with Q at both ends. -/
private theorem local_model_derived_stalk_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (U : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (L : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj L)
    (s : X) (hs : s ∈ U)
    [hD : HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk s))] :
    Nonempty (DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace s).mapHomologicalComplex
        (.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj (((openModuleStalkFunctor X U ⟨s, hs⟩).mapHomologicalComplex
        (.up ℤ)).obj L)) := by
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let S := openModuleStalkFunctor X U ⟨s, hs⟩
  let : HasDerivedCategory.{v}
      (ModuleCat.{u} (X.presheaf.stalk (U.ι ⟨s, hs⟩))) := hD
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let eD : DerivedCategory.Q.{v}.obj
      ((S.mapHomologicalComplex (.up ℤ)).obj (Fc.obj P)) ≅
      DerivedCategory.Q.{v}.obj ((S.mapHomologicalComplex (.up ℤ)).obj L) :=
    (S.mapDerivedCategoryFactors.app (Fc.obj P)).symm ≪≫
    S.mapDerivedCategory.mapIso ((F.mapDerivedCategoryFactors.app P).symm ≪≫ eL) ≪≫
      S.mapDerivedCategoryFactors.app L
  let j := U.ι
  let ρ := (j.stalkMap ⟨s, hs⟩).hom
  let R := ModuleCat.restrictScalars ρ
  have : R.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (RingEquiv.ofBijective ρ (ConcreteCategory.bijective_of_isIso (j.stalkMap ⟨s, hs⟩)))
  let G := RingedSpace.moduleStalkFunctor X.toRingedSpace s
  let T := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩
  obtain ⟨a⟩ := nonempty_restriction_stalk_extension_iso j ⟨s, hs⟩ P
  let η := (NatIso.mapHomologicalComplex
    (asIso (ModuleCat.extendRestrictScalarsAdj ρ).unit) (.up ℤ)).app
      ((G.mapHomologicalComplex (.up ℤ)).obj P)
  have : (SheafOfModules.overFunctor X.ringCatSheaf U).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (Scheme.Modules.restrictFunctor U.ι).Additive :=
    Functor.additive_of_iso (Scheme.Modules.overFunctorEquiv U)
  let b := (NatIso.mapHomologicalComplex (Scheme.Modules.overFunctorEquiv U)
    (.up ℤ)).app P
  let c := η ≪≫ (R.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
    ((T ⋙ R).mapHomologicalComplex (.up ℤ)).mapIso b.symm
  let c' : (G.mapHomologicalComplex (.up ℤ)).obj P ≅
      (S.mapHomologicalComplex (.up ℤ)).obj (Fc.obj P) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (HomologicalComplex.eval _ _ i).mapIso c)
      (by intro i j _; exact c.hom.comm i j)
  exact ⟨DerivedCategory.Q.{v}.mapIso c' ≪≫ eD⟩

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the canonical base-change arrow, from its adjunction-unit formula.
Source: Stacks Project, Tag 0A1U, the canonical cohomology base-change map. -/
private theorem cohomologyBaseChange_naturality {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ Q) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap R B)).map
        (HomologicalComplex.homologyMap g i) ≫ ModuleCat.cohomologyBaseChange Q i =
      ModuleCat.cohomologyBaseChange P i ≫ HomologicalComplex.homologyMap
        ((RingTensorCohomology.extend R B).map g) i := by
  let E := ModuleCat.extendScalars (algebraMap R B)
  let U := ModuleCat.restrictScalars (algebraMap R B)
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R B)
  let σ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) i).map g
  have hσ : σ ≫ (Q.sc i).mapNatTrans adj.unit =
      (P.sc i).mapNatTrans adj.unit ≫ U.mapShortComplex.map (E.mapShortComplex.map σ) := by
    apply ShortComplex.hom_ext <;> exact adj.unit.naturality _
  have hH := congrArg (fun f ↦ ShortComplex.homologyMap f) hσ
  simp only [ShortComplex.homologyMap_comp] at hH
  have hU := ShortComplex.mapHomologyIso_hom_naturality (E.mapShortComplex.map σ) U
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [ModuleCat.cohomologyBaseChange, adj, Equiv.apply_symm_apply]
  change ShortComplex.homologyMap σ ≫
      (ShortComplex.homologyMap ((Q.sc i).mapNatTrans adj.unit) ≫
        (((Q.sc i).map E).mapHomologyIso U).hom) = _
  rw [← Category.assoc, hH, Category.assoc]
  erw [hU]
  rfl

/-- A quasi-isomorphism preserved by scalar extension transports fibre-map surjectivity.
Source: Stacks Project, Tags 064L and 06Y0; cancel the isomorphisms in naturality. -/
private theorem epi_cohomologyBaseChange_iff_of_quasiIso {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ Q) (i : ℤ)
    [QuasiIso g] [QuasiIso ((RingTensorCohomology.extend R B).map g)] :
    Epi (ModuleCat.cohomologyBaseChange (B := B) P i) ↔
      Epi (ModuleCat.cohomologyBaseChange (B := B) Q i) := by
  let E := ModuleCat.extendScalars (algebraMap R B)
  rw [← epi_comp_iff_of_epi (E.map (HomologicalComplex.homologyMap g i)),
    cohomologyBaseChange_naturality P Q g i, epi_comp_iff_of_isIso]

/-- Common K-flat roofs preserve surjectivity of the canonical base-change map.
Source: Stacks Project, Tags 064L, 06Y0 and 06YS. The naturality square is proved
above directly from the adjunction unit defining cohomologyBaseChange. Resolve a
common derived roof, apply that square to its two quasi-isomorphisms, and cancel
the invertible source and target homology maps. -/
private theorem epi_cohomologyBaseChange_iff_of_kFlat_derivedIso {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat Q)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    Epi (ModuleCat.cohomologyBaseChange (B := B) P i) ↔
      Epi (ModuleCat.cohomologyBaseChange (B := B) Q i) := by
  classical
  obtain ⟨L, s, hs, t, he⟩ := DerivedCategory.right_fac e.hom
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs
  have ht : IsIso (DerivedCategory.Q.map t) := by
    have h : DerivedCategory.Q.map t = DerivedCategory.Q.map s ≫ e.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [h]
    infer_instance
  have : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).mp ht
  let Λ := RingTensorCohomology.flatResolution R
  let L' := Λ.resolutionFunctor.obj L
  let r := Λ.resolutionNatTrans.app L
  have : QuasiIso r := inferInstance
  have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le L
  let E := ModuleCat.extendScalars (algebraMap R B)
  have : E.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  have : E.PreservesKFlatQuasiIso := ModuleCat.extendScalars_preservesKFlatQuasiIso _
  have : QuasiIso ((RingTensorCohomology.extend R B).map (r ≫ s)) :=
    E.quasiIso_mapHomologicalComplex_map_of_kFlat hk hP (r ≫ s)
  have : QuasiIso ((RingTensorCohomology.extend R B).map (r ≫ t)) :=
    E.quasiIso_mapHomologicalComplex_map_of_kFlat hk hQ (r ≫ t)
  exact (epi_cohomologyBaseChange_iff_of_quasiIso L' P (r ≫ s) i).symm.trans
    (epi_cohomologyBaseChange_iff_of_quasiIso L' Q (r ≫ t) i)

/-- Translate the acyclic-total-tensor formulation of K-flatness to the localization API.
Source: Stacks Project, Tags 064L and 06YB, through the homotopy quotient. -/
private theorem kFlat_of_acyclic_tensor {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (MonoidalCategory.curriedTensor _))).mpr (hP N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    (β_ _ _) hr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical degree-zero fibre map of a bounded-above free affine representative
is surjective if the corresponding sheaf-derived fibre map is surjective.
Source: Stacks Project, Tag 0A1U, affine reduction; Cohomology, Tag 06YB;
Cohomology on Sites, Tag 06YS.
(blueprint: lem-sc-affine-perfect-fibre-surjectivity).

Proof: Choose the K-flat sheaf representative in the definition of hs. Its stalk
is K-flat, and exact stalks identify its degree-zero homology with H0(K)_s.
The associated sheaf of M is bounded above and termwise free, hence K-flat.
The given derived isomorphism and the exact stalk functor identify the two
stalk models in the derived category. The proved private theorem
epi_cohomologyBaseChange_iff_of_kFlat_derivedIso transports surjectivity between
these K-flat models: resolve a common roof and tensor with the residue field.
The naturality square identifies their canonical cohomology base-change maps:
this follows from naturality of the extension-restriction unit defining
ModuleCat.cohomologyBaseChange. Both source and target comparisons are
isomorphisms. On the affine chart the stalk is localization at the prime
hU.isoSpec.hom(s); flat localization commutes with homology, and its residue
field is canonically the residue field of that prime. The named affine comparison
affine_model_stalk_baseChange supplies K-flatness of this stalk and the equivalence
of epimorphy under these scalar and homology identifications. Conjugating the
epimorphism in hs by these isomorphisms proves it.
No vanishing of negative cohomology or minimality of the free ranks is used.
The empty open has no s, and zero modules give epimorphisms between zero objects. -/
theorem affine_perfect_fibre_surjectivity (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) (s : X) (hs : degreeZeroFibreSurjective X K s)
    (U : X.Opens) (hsU : s ∈ U) (hU : IsAffineOpen U)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (hb : ∃ b : ℤ, M.IsStrictlyLE b)
    (hf : ∀ i : ℤ, Module.Free (X.presheaf.obj (.op U)) (M.X i) ∧
      Module.Finite (X.presheaf.obj (.op U)) (M.X i))
    (eM : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((Scheme.affinePerfectSheafification X U hU).mapHomologicalComplex
            (.up ℤ)).obj M))) :
    Epi (ModuleCat.cohomologyBaseChange
      (B := (hU.isoSpec.hom ⟨s, hsU⟩).asIdeal.ResidueField) M 0) := by
  classical
  let L := ((Scheme.affinePerfectSheafification X U hU).mapHomologicalComplex
    (.up ℤ)).obj M
  let C := ((openModuleStalkFunctor X U ⟨s, hsU⟩).mapHomologicalComplex (.up ℤ)).obj L
  let hD : HasDerivedCategory.{u} (ModuleCat.{u} (X.presheaf.stalk s)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : HasDerivedCategory.{u} (ModuleCat.{u} (X.presheaf.stalk s)) := hD
  let : HasDerivedCategory.{u}
      (ModuleCat.{u} (X.presheaf.stalk (U.ι ⟨s, hsU⟩))) := hD
  have hM : (HomologicalComplex.quasiIso
      (ModuleCat.{u} (X.presheaf.obj (.op U))) (.up ℤ)).kFlat M := by
    apply kFlat_of_acyclic_tensor
    apply CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat M
    · obtain ⟨b, hb⟩ := hb
      exact ⟨b, (M.isStrictlyLE_iff b).mp hb⟩
    · intro i
      have := (hf i).1
      infer_instance
  obtain ⟨hC, hiff⟩ := affine_model_stalk_baseChange X U hU ⟨s, hsU⟩ M hM
  obtain ⟨P, hP, ⟨eP⟩, hsurj⟩ := hs
  obtain ⟨eS⟩ := local_model_derived_stalk_iso.{u, w, u} X P U L
    ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso
      eP ≪≫ eM.some) s hsU
  have hPS := (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace P).mp hP s
  exact hiff.mpr ((epi_cohomologyBaseChange_iff_of_kFlat_derivedIso _ C
    (kFlat_of_acyclic_tensor _ hPS) hC eS 0).mp hsurj)

end AlgebraicGeometry
