/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import Sheaf.Paper.FiniteConstructibleComplexHeartPresentations
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import Sheaf.Topology.ContinuousMapCondensedRing
import Sheaf.Paper.FiniteDiscreteSerreIndConstructible
import Sheaf.Paper.ConstructibleFiniteHeart
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels

/-! # The finite-coefficient weak Serre hull lies in the ind-finite-heart class -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Lifting a finite discrete coefficient carrier preserves its condensed ring object. -/
private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩

/-- Finite discrete coefficients admit ind-finite-heart presentations on any qcqs base.
Source: Stacks Tags 03SA(3), 099Y, followed by scalar-isomorphism transport.
(blueprint: lem-sfb-finite-coefficient-serre-ind-heart)
Proof: lift the finite coefficient carrier to the scheme universe. Restriction of
scalars along its ring isomorphism is an exact equivalence and transports finite
constant scalar models. The finite discrete comparison gives a filtered presentation
by constructible modules. Transport this cocone back along inverse restriction.
A constructible module is the heart of its degree-zero complex, so the same cocone
is a presentation by finite constructible complex hearts. Empty bases and the zero
coefficient ring require no exceptional argument. -/
theorem finiteCoefficient_serre_is_indFiniteHeart
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M) :
    indFiniteConstructibleComplexHearts Λ X M := by
  classical
  let B := ULift.{u} A
  let Λ' := FiniteDiscreteOrdinary.coefficient B
  let j : Mon.mk Λ ≅ Mon.mk Λ' := e ≪≫ (finiteCoefficientLiftIso A).some
  have : IsIso j.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map j.inv))
  have : IsIso j.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map j.hom))
  let φ := (upperStarFromPoint X).map j.inv.hom
  let E := Mod.comapEquivalenceOfIsIso φ
  let F := E.functor
  have : F.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  have : F.Additive := inferInstanceAs (Mod.comap φ).Additive
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  let P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :=
    IsConstantModelConstructible Λ' X
  let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1} P
  have hf : Q (F.obj M) := by
    apply hM (Q.inverseImage F) ?_ inferInstance inferInstance inferInstance inferInstance
      (fun _ ↦ inferInstance)
    intro N hN
    exact P.le_weakSerreCoproductClosure _
      (constructible_comap j.inv.hom X N hN)
  obtain ⟨I, hI, hfilter, pres, hpres⟩ :=
    FiniteDiscreteOrdinary.finiteDiscrete_serre_is_indConstructible B X (F.obj M) hf
  let := hI
  let := hfilter
  let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
    Mod.comap ((upperStarFromPoint X).map j.hom.hom)
  have hg : G.IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso
      ((upperStarFromPoint X).map j.hom.hom)).functor.IsEquivalence)
  let k : (upperStarFromPoint X).map j.hom.hom ≫ φ = 𝟙 _ := by
    dsimp [φ]
    rw [← Functor.map_comp]
    change (upperStarFromPoint X).map ((Mon.forget _).map (j.hom ≫ j.inv)) = _
    simp only [Iso.hom_inv_id, Mon.forget_map, Mon.id_hom']
    exact (upperStarFromPoint X).map_id _
  let η : F ⋙ G ≅ 𝟭 _ :=
    (Mod.comapComp ((upperStarFromPoint X).map j.hom.hom) φ).symm ≪≫
      Mod.comapCongr k ≪≫ Mod.comapId _
  let l := η.app M
  refine ⟨I, hI, hfilter,
    ⟨pres.diag ⋙ G, (G.mapCocone (Cocone.mk (F.obj M) pres.ι)).ι ≫
      (Functor.const I).map l.hom, ?_⟩, ?_⟩
  · exact (isColimitOfPreserves G pres.isColimit).ofIsoColimit (Cocone.ext l)
  · intro i
    exact constructible_le_finiteConstructibleComplexHearts Λ X _
      (constructible_comap j.hom.hom X _ (hpres i))

end AlgebraicGeometry.ProEtale
