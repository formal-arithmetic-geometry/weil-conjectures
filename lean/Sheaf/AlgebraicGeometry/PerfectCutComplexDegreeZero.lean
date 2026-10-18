/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DegreeZeroFibreSurjective
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import Sheaf.Algebra.Homology.AffinePerfectCutDegreeZero
import Sheaf.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import Sheaf.AlgebraicGeometry.AffinePerfectFibreSurjectivity
import Sheaf.AlgebraicGeometry.AffinePerfectCutSheafRealization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Splitting a perfect complex at degree zero near a point

Source: Stacks Project, More on Algebra, Lemma 15.78.2, Tag 0A1U
(blueprint: lem-sc-perfect-cut-complex-degree-zero).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Finite free modules sheafify to finite free sheaves on the localized affine site.
Source: Stacks Project, Tags 01HV and 01IB; proof by tildeFinsupp and mapFreeIso. -/
private theorem affine_free_iso (S : Scheme.{u}) (U : S.Opens)
    (hU : IsAffineOpen U) (m : ℕ) :
    Nonempty ((Scheme.affinePerfectSheafification S U hU).obj
      (ModuleCat.of (S.presheaf.obj (.op U))
        (ULift.{u} (Fin m) →₀ (S.presheaf.obj (.op U)))) ≅
      SheafOfModules.free (R := (moduleRings S.toRingedSpace).over U)
        (ULift.{u} (Fin m))) := by
  let R := S.presheaf.obj (.op U)
  let F := Scheme.Modules.restrictFunctor hU.isoSpec.hom
  let G := (Scheme.Modules.overEquiv U).inverse
  have : F.IsLeftAdjoint := (Scheme.Modules.restrictAdjunction hU.isoSpec.hom).isLeftAdjoint
  let eF := (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m))
    (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm).symm
  let eG := (SheafOfModules.mapFreeIso G (ULift.{u} (Fin m))
    (U.sheafOfModulesEquivOverInverseUnit S.ringCatSheaf).symm).symm
  exact ⟨G.mapIso (F.mapIso (tildeFinsupp (R := R) (ULift.{u} (Fin m))) ≪≫ eF) ≪≫ eG⟩

/-- Lift a bounded-above free complex directly through affine sheafification.
Source: Stacks Project, Tags 08E7, 01I7 and 01IB.
Proof: Choose each finite rank, conjugate the differentials through the free-term
isomorphisms, and lift them by full faithfulness. Faithfulness proves square-zero
and transfers vanishing above the given bound. The resulting modules are finite free.
This follows the proved private construction in PseudoCoherentFiberBoundedAboveModel;
its helpers are private there, so the construction is reproduced in this proof. -/
private theorem affine_local_finiteFree_model (S : Scheme.{u}) (U : S.Opens)
    (hU : IsAffineOpen U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → Limits.IsZero (P.X i))
    (hf : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin r)))) :
    ∃ M : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ,
      ∃ b : ℤ, M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Free (S.presheaf.obj (.op U)) (M.X i) ∧
          Module.Finite (S.presheaf.obj (.op U)) (M.X i)) ∧
        Nonempty (((Scheme.affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj M
          ≅ P) := by
  classical
  let R := S.presheaf.obj (.op U)
  let rF := Scheme.Modules.restrictFunctor hU.isoSpec.hom
  let rG := Scheme.Modules.restrictFunctor hU.isoSpec.inv
  let e := CategoryTheory.Equivalence.mk rF rG
    ((Scheme.Modules.restrictFunctorId).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp) ≪≫
      Scheme.Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp) ≪≫ Scheme.Modules.restrictFunctorId)
  have : rF.IsEquivalence := e.isEquivalence_functor
  let F := Scheme.affinePerfectSheafification S U hU
  have : F.Full := by unfold F Scheme.affinePerfectSheafification; infer_instance
  have : F.Faithful := by unfold F Scheme.affinePerfectSheafification; infer_instance
  choose r hr using hf
  let X (i : ℤ) := ModuleCat.of R (ULift.{u} (Fin (r i)) →₀ R)
  let ei (i : ℤ) : F.obj (X i) ≅ P.X i :=
    (affine_free_iso S U hU (r i)).some ≪≫ (hr i).some.symm
  let d (i j : ℤ) : X i ⟶ X j := F.preimage ((ei i).hom ≫ P.d i j ≫ (ei j).inv)
  have hd (i j : ℤ) : F.map (d i j) = (ei i).hom ≫ P.d i j ≫ (ei j).inv :=
    F.map_preimage _
  let M : CochainComplex (ModuleCat.{u} R) ℤ :=
    { X := X
      d := d
      shape := by
        intro i j hij
        apply F.map_injective
        rw [hd, P.shape i j hij]
        simp
      d_comp_d' := by
        intro i j k _ _
        apply F.map_injective
        rw [Functor.map_comp, hd, hd]
        simp [Category.assoc] }
  let eC : (F.mapHomologicalComplex (.up ℤ)).obj M ≅ P :=
    HomologicalComplex.Hom.isoOfComponents ei (by
      intro i j _
      change (ei i).hom ≫ P.d i j = F.map (d i j) ≫ (ei j).hom
      rw [hd]
      simp)
  obtain ⟨b, hb⟩ := hb
  refine ⟨M, b, ?_, fun _ ↦ ⟨inferInstance, inferInstance⟩, ⟨eC⟩⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact ((ei i).isZero_iff.mpr (hb i hi)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem isGE_zero_of_tensor_vanishing (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X)
    (hKa : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < 0 → schemeDerivedTensorCohomologyVanishes X K F i) :
    K.IsGE 0 := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  let : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  apply (DerivedCategory.isGE_iff K 0).mpr
  intro i hi
  obtain ⟨P, _, ⟨eP⟩, hP⟩ := hKa (SheafOfModules.unit _) i hi
  let e : CochainComplex.mapBifunctor P
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit _)) (MonoidalCategory.curriedTensor _) ≅ P :=
    HomologicalComplex.rightUnitor P
  exact (hP.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso e).symm).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso eP.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P)

private theorem truncLT_one_iso_single_homology
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) [K.IsGE 0] :
    Nonempty ((DerivedCategory.TStructure.t.truncLT 1).obj K ≅
      (DerivedCategory.singleFunctor C 0).obj
        ((DerivedCategory.homologyFunctor C 0).obj K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let A := (t.truncLT 1).obj K
  have : A.IsGE 0 := inferInstanceAs (t.IsGE ((t.truncLT 1).obj K) 0)
  have : A.IsLE 0 := t.isLE_truncLT_obj K 1 0 (by omega)
  obtain ⟨M, ⟨eM⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE A 0
  have : IsIso ((DerivedCategory.homologyFunctor C 0).map ((t.truncLTι 1).app K)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K 1 0 (by omega)
  let eH : M ≅ (DerivedCategory.homologyFunctor C 0).obj K :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).symm ≪≫
      (DerivedCategory.homologyFunctor C 0).mapIso eM.symm ≪≫
      asIso ((DerivedCategory.homologyFunctor C 0).map ((t.truncLTι 1).app K))
  exact ⟨eM ≪≫ (DerivedCategory.singleFunctor C 0).mapIso eH⟩

set_option backward.isDefEq.respectTransparency false in
/-- A perfect complex of nonnegative Tor amplitude splits locally at a point where
its degree-zero cohomology maps onto the degree-zero cohomology of its derived fibre.
The first summand is the restricted degree-zero cohomology sheaf in degree zero;
the second is perfect of Tor amplitude in `[1, ∞)`.
Restriction is the exact over-site functor followed by the canonical equivalence
with module sheaves on the open subscheme. Derived-category existence binders
use the shared Mathlib abelian structures, including on all the opens in question.
Source: Stacks Project, Tag 0A1U, i = 0
(blueprint: lem-sc-perfect-cut-complex-degree-zero).

Proof:
1. Refine a strictly perfect local model to a bounded finite-free model on an
   affine neighbourhood. Lift its terms and differentials through fully faithful
   affine sheafification. This gives a bounded-above finite-free module complex;
   prescribed residue-field ranks are unnecessary.
2. Transport the fibre-surjectivity hypothesis to that affine representative.
   Apply lem-pc-affine-perfect-cut-degree-zero (Tag 0A1U) and realize its supplied
   principal-localization splitting and positive projective model as sheaves.
3. Tensoring the negative-vanishing witness with the unit proves K.IsGE 0.
   Exact restriction preserves this bound. Its nonpositive truncation therefore
   equals restricted H⁰(K) in degree zero. Substitute in the sheaf splitting. -/
theorem exists_perfect_split_degree_zero (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ (U : X.Opens) (V : U.toScheme.Opens),
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (K : schemeDerivedCategory X) (hKq : schemeDerivedQCohProperty X K)
    (hKp : Scheme.IsPerfect X K)
    (hKa : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < 0 → schemeDerivedTensorCohomologyVanishes X K F i)
    (s : X) (hs : degreeZeroFibreSurjective X K s) :
    ∃ U : X.Opens, s ∈ U ∧ ∃ P : schemeDerivedCategory U.toScheme,
      Scheme.IsPerfect U.toScheme P ∧
      (∀ F : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
        ∀ i : ℤ, i < 1 → schemeDerivedTensorCohomologyVanishes U.toScheme P F i) ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj K ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
              (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                  (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv U)).obj
                    ((DerivedCategory.homologyFunctor
                      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj K)) ⊞ P) := by
  classical
  have _hQCoh := hKq
  obtain ⟨U, hsU, P, hP, eP⟩ := hKp s
  obtain ⟨V, hsV, _, hVaff, F, hb, hf, ⟨eF⟩⟩ :=
    Scheme.exists_finiteFree_refinement_of_isStrictlyPerfect X K U P hP eP s hsU
  have hV : IsAffineOpen V := hVaff
  obtain ⟨M, b, hMb, hMf, ⟨eM⟩⟩ := affine_local_finiteFree_model X V hV F
    (by obtain ⟨a, b, h⟩ := hb; exact ⟨b, fun i hi ↦ h i (Or.inr hi)⟩) hf
  let eVM := eF ≪≫ (DerivedCategory.Q.mapIso eM).symm
  let : ∀ f : X.presheaf.obj (.op V),
      HasDerivedCategory.{u} (ModuleCat.{u} (Localization.Away f)) :=
    fun f ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  have hsurj := affine_perfect_fibre_surjectivity X K s hs V hsV hV M
    ⟨b, hMb⟩ hMf ⟨eVM⟩
  obtain ⟨f, hfs, esplit, hpos, _, _⟩ :=
    DerivedCategory.affine_perfect_cut_degree_zero
      (hV.isoSpec.hom ⟨s, hsV⟩).asIdeal M ⟨b, hMb⟩ hMf hsurj
  obtain ⟨W, hsW, Q, hQp, hQa, ⟨es⟩⟩ :=
    affine_perfect_cut_sheaf_realization X K s V hsV hV M ⟨eVM⟩ f hfs esplit hpos
  let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
      (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv W)
  have hKge := isGE_zero_of_tensor_vanishing X K hKa
  have : (R.mapDerivedCategory.obj K).IsGE 0 := R.isGE_mapDerivedCategory_obj K 0
  obtain ⟨eH⟩ := truncLT_one_iso_single_homology (R.mapDerivedCategory.obj K)
  refine ⟨W, hsW, Q, hQp, hQa, ⟨es ≪≫ biprod.mapIso ?_ (Iso.refl Q)⟩⟩
  exact eH ≪≫ (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).mapIso
      ((R.mapDerivedCategoryHomologyFunctorIso 0).app K).symm

end AlgebraicGeometry
