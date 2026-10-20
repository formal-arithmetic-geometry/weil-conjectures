/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteReductionSystem
import Sheaf.Paper.FiniteReductionRestrictTensor
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModelReduction
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.ConstructibleSheaf.SpecializationCriterion
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! Bounded constructibility under finite scalar extension at finite Tor amplitude. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.FiniteReduction

private theorem old_boundedConstructible (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hK : Etale.DerivedCategory.isBoundedConstructible A T K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  obtain ⟨hc, a, b, hab, hv⟩ := hK
  refine ⟨⟨⟨a, (DerivedCategory.isGE_iff _ a).mpr (fun i hi ↦ hv i (Or.inl hi))⟩,
    ⟨b, (DerivedCategory.isLE_iff _ b).mpr (fun i hi ↦ hv i (Or.inr hi))⟩⟩, ?_⟩
  intro i
  exact (Etale.constructibleSheaf_iff _ _ _).mpr
    ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i))

/-- Finite coefficient extension preserves bounded constructibility on complexes of
finite Tor amplitude, with the specified universal derived extension.
Source: Stacks Tags 094H and 08G1; blueprint sk-lem-sp-reduction, first paragraph
(blueprint: lem-pur-finite-reduction-etale-constructibility).

Proof: let U be exact restriction of scalars. The sheafified tensor identity identifies
ordinary extension followed by U with tensoring by the constant sheaf B. On a K-flat
resolution it identifies U(E(K)) with K tensor-derived B. The constant sheaf B is finite
locally constant as an A-module since both rings are finite. Apply boundedConstructible_tensor
with the finite-Tor-amplitude factor K, using the tensor braiding. Its conclusion says
that U(E(K)) has bounded constructible cohomology. Exactness of U identifies each of
these sheaves with U(H^i(E(K))). Constructibility reflects through scalar restriction
between finite rings, by coefficient devissage. Conservativity of U reflects zero
cohomology outside the same bounded interval. Together these give the claimed property.
The zero ring is harmless: all its sheaves are zero. No Noetherian scheme is required. -/
theorem boundedConstructible_extend (T : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (E : DerivedExtension T.smallEtaleTopology f)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : Etale.DerivedCategory.isBoundedConstructible A T K)
    (a b : ℤ) (_hab : a ≤ b)
    (hTor : Etale.DerivedCategory.hasTorAmplitudeIn A T a b K) :
    Etale.DerivedCategory.isBoundedConstructible B T (E.functor.obj K) := by
  obtain ⟨P, hge, hle, hflat, ⟨eP⟩⟩ :=
    (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).mp
      ((Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
        (Λ := A) (K := K)).mp hTor)
  let := hge
  let := hle
  have hk := CochainComplex.kFlat_of_bounded_of_flat P a b hflat
  have : IsIso (E.counit.app P) := E.computation P hk
  let U := Sheaf.restrictScalars T.smallEtaleTopology f
  let M := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))
  let em : E.functor.obj K ≅ DerivedCategory.Q.obj
      (((extend T.smallEtaleTopology f).mapHomologicalComplex (.up ℤ)).obj P) :=
    E.functor.mapIso eP.symm ≪≫ asIso (E.counit.app P)
  let ei : U.mapDerivedCategory.obj (E.functor.obj K) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) :=
    U.mapDerivedCategory.mapIso em ≪≫ U.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (extend_restrict_tensor T.smallEtaleTopology f)
        (.up ℤ)).app P) ≪≫
    (Etale.derivedTensorQObjSingleFunctorObjIso (a := a) (b := b) P hflat M).symm ≪≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).mapIso eP).app
        ((DerivedCategory.singleFunctor _ 0).obj M)
  have : Finite ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) :=
    inferInstanceAs (Finite B)
  have : Module.Finite A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) :=
    Module.Finite.of_finite
  have hM : Scheme.IsConstructibleSheaf M :=
    Scheme.isConstructibleSheaf_constantSheaf _
  let := hM
  have hsingle := Etale.DerivedCategory.boundedConstructible_singleFunctor_obj M 0
  have hbc := Etale.boundedConstructible_tensor A T hsingle (old_boundedConstructible T hK)
    ⟨a, b, (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
      (Λ := A) (K := K)).mp hTor⟩
  obtain ⟨braid⟩ := Etale.nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} A) T
  have hU : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T
      (U.mapDerivedCategory.obj (E.functor.obj K)) :=
    (Etale.DerivedCategory.boundedConstructible _ T).prop_of_iso
      ((braid.app ((DerivedCategory.singleFunctor _ 0).obj M)).app K ≪≫ ei.symm) hbc
  refine ⟨fun i ↦ ?_, ?_⟩
  · apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    apply (Scheme.isConstructibleSheaf_restrictScalars_iff_of_finite f _).mp
    have hH := (Etale.constructibleSheaf_iff _ _ _).mp (hU.2 i)
    exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
      ((U.mapDerivedCategoryHomologyFunctorIso i).app (E.functor.obj K)).symm hH
  · obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hU.1
    refine ⟨min c d, max c d, min_le_max, fun i hi ↦ ?_⟩
    have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (U.mapDerivedCategory.obj (E.functor.obj K))) := by
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff _ c).mp hc i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff _ d).mp hd i (lt_of_le_of_lt (le_max_right _ _) hi)
    have hz' := hz.of_iso ((U.mapDerivedCategoryHomologyFunctorIso i).app (E.functor.obj K))
    apply (IsZero.iff_id_eq_zero _).mpr
    apply U.map_injective
    rw [U.map_id, U.map_zero]
    exact (IsZero.iff_id_eq_zero _).mp hz'

end AlgebraicGeometry.FiniteReduction
