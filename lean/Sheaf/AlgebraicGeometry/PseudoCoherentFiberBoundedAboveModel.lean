/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups H4 and K1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Local bounded-above algebraic models of pseudo-coherent fibres

Source: Stacks Project, Tags 08E7 and 0BDI.
(blueprint: lem-sc-pseudo-coherent-fiber-bounded-above-model).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finite free modules sheafify to finite free sheaves on the localized affine site.
Source: Stacks Project, Tags 01HV and 01IB; proof by tildeFinsupp and mapFreeIso. -/
private theorem affine_free_iso (S : Scheme.{u}) (U : S.Opens)
    (hU : IsAffineOpen U) (m : ℕ) :
    Nonempty ((affinePerfectSheafification S U hU).obj
      (ModuleCat.of (S.presheaf.obj (.op U))
        (ULift.{u} (Fin m) →₀ (S.presheaf.obj (.op U)))) ≅
      SheafOfModules.free (R := (moduleRings S.toRingedSpace).over U)
        (ULift.{u} (Fin m))) := by
  let R := S.presheaf.obj (.op U)
  let F := Modules.restrictFunctor hU.isoSpec.hom
  let G := (Modules.overEquiv U).inverse
  have : F.IsLeftAdjoint := (Modules.restrictAdjunction hU.isoSpec.hom).isLeftAdjoint
  let eF := (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m))
    (Modules.restrictUnitIso hU.isoSpec.hom).symm).symm
  let eG := (SheafOfModules.mapFreeIso G (ULift.{u} (Fin m))
    (U.sheafOfModulesEquivOverInverseUnit S.ringCatSheaf).symm).symm
  exact ⟨G.mapIso (F.mapIso (tildeFinsupp (R := R) (ULift.{u} (Fin m))) ≪≫ eF) ≪≫ eG⟩

/-- Lift a bounded-above free complex directly through affine sheafification.
Source: Stacks Project, Tags 08E7, 01I7 and 01IB.
Proof: Choose each finite rank, conjugate the differentials through the free-term
isomorphisms, and lift them by full faithfulness. Faithfulness proves square-zero
and transfers vanishing above the given bound. The resulting modules are finite free.
This is the proved local construction used in PerfectOfPseudoCoherentFiniteTorDimension;
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
        Nonempty (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj M
          ≅ P) := by
  classical
  let R := S.presheaf.obj (.op U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let e := CategoryTheory.Equivalence.mk rF rG
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  have : rF.IsEquivalence := e.isEquivalence_functor
  let F := affinePerfectSheafification S U hU
  have : F.Full := by unfold F affinePerfectSheafification; infer_instance
  have : F.Faithful := by unfold F affinePerfectSheafification; infer_instance
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

/-- A single bounded-above finite-free algebraic complex computes all fibre degrees
on an affine neighbourhood. This does not assert a bounded representative.

Source: Stacks Project, Tags 08E7 and 0BDI, affine reduction.
(blueprint: lem-sc-pseudo-coherent-fiber-bounded-above-model).

Proof: Use pseudo-coherence to choose a bounded-above finite-free sheaf complex
on a neighbourhood of x. Choose an affine open inside that neighbourhood containing x.
Restrict its terms and derived comparison, and transport along the affine chart.
Restriction preserves free sheaves of finite rank and zero terms. Full faithfulness
of affinePerfectSheafification lifts the resulting complex to an algebraic complex F,
with the same upper bound and finite free terms (affine_local_finiteFree_model).
Finite free terms are flat. The bounded-above flat derived-pullback comparison therefore
computes the derived pullback to each residue field termwise. Derived pullback commutes
with restriction to the open neighbourhood. On the residue-field spectrum, evaluation
of the cohomology sheaf identifies it with the homology of F tensor the residue field.
The canonical residue-field isomorphism attached to the affine chart transports the
scalar action. The separate affine_boundedAbove_fiberBetti_eq comparison gives the
equality for every degree and point.
This also covers an upper bound below the degree: both vector spaces then vanish. -/
theorem exists_pseudoCoherent_fiber_boundedAbove_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ (A : Type u) (_ : CommRing A) (e : ↥(U : Set X) ≃ₜ PrimeSpectrum A)
        (F : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ),
        F.IsStrictlyLE b ∧
        (∀ n : ℤ, Module.Free A (F.X n) ∧ Module.Finite A (F.X n)) ∧
        ∀ (i : ℤ) (z : U), derivedFiberBetti X E i z =
          Module.finrank (e z).asIdeal.ResidueField
            ((((ModuleCat.extendScalars
              (algebraMap A (e z).asIdeal.ResidueField)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj F).homology i) := by
  classical
  obtain ⟨U, hxU, P, hb, hf, ⟨eP⟩⟩ := hE x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := U) hxU
  let F := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
  let G := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let PV := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hbV : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (PV.X i) := by
    obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun i hi ↦ F.map_isZero (hN i hi)⟩
  have hfV (i : ℤ) : ∃ r : ℕ, Nonempty (PV.X i ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by
    obtain ⟨r, ⟨e⟩⟩ := hf i
    let ef : F.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))) ≅
        SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r)) :=
      (asIso (CategoryTheory.Limits.sigmaComparison F (fun _ : ULift.{u} (Fin r) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
          CategoryTheory.Limits.Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso
            (R := moduleRings X.toRingedSpace) (homOfLE hVU))
    exact ⟨r, ⟨F.mapIso e ≪≫ ef⟩⟩
  have : CategoryTheory.Limits.PreservesFiniteLimits (G ⋙ F) :=
    CategoryTheory.Limits.comp_preservesFiniteLimits _ _
  have : CategoryTheory.Limits.PreservesFiniteColimits (G ⋙ F) :=
    CategoryTheory.Limits.comp_preservesFiniteColimits _ _
  let eV : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj PV :=
    (Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u}
        (moduleRings X.toRingedSpace) (homOfLE hVU))).symm.app E ≪≫
      (Functor.mapDerivedCategoryCompIso G F).app E ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
        F.mapDerivedCategoryFactors.app P
  obtain ⟨M, b, hMb, hMf, ⟨eM⟩⟩ := affine_local_finiteFree_model X V hV PV hbV hfV
  let eVM := eV ≪≫ (DerivedCategory.Q.mapIso eM).symm
  refine ⟨V, hxV, X.presheaf.obj (.op V), inferInstance, hV.isoSpec.hom.homeomorph,
    M, b, hMb, hMf, ?_⟩
  intro i z
  exact affine_boundedAbove_fiberBetti_eq X E V hV M b hMb (fun n ↦ (hMf n).1) ⟨eVM⟩ i z

end AlgebraicGeometry.Scheme
