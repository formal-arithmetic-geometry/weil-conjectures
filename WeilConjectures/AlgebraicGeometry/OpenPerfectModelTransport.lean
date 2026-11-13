/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex

/-! # Transport of perfect models from an open subscheme

## References

* Stacks Project, Definition 08CM, Definition 08C4 and restriction in Tag 08DW.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A perfect model on an open subscheme is an ambient local perfect model.
(Stacks, Definition 08CM, Definition 08C4 and Tag 08DW) -/
theorem local_perfect_of_openRestriction_iso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (R : schemeDerivedCategory X)
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (e : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ F) :
    ∀ x : X, x ∈ U → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K) := by
  intro x hx
  obtain ⟨V, hxV, K, hK, ⟨hmodel⟩⟩ := hF ⟨x, hx⟩
  let O := U.ι ''ᵁ V
  let s := U.ι.isoImage V
  let EV := Modules.overEquiv V
  let EO := Modules.overEquiv O
  let ES := CategoryTheory.Equivalence.mk
    (Modules.restrictFunctor s.inv) (Modules.restrictFunctor s.hom)
    ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
      Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId).symm
    ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
      Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId)
  let A := (EV.trans ES).trans EO.symm
  have : A.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : A.functor.Additive := Functor.additive_of_preserves_binary_products _
  let K' := (A.functor.mapHomologicalComplex (.up ℤ)).obj K
  have unitIso : A.functor.obj
      (SheafOfModules.unit ((moduleRings U.toScheme.toRingedSpace).over V)) ≅
      SheafOfModules.unit ((moduleRings X.toRingedSpace).over O) :=
    EO.inverse.mapIso ((Modules.restrictFunctor s.inv).mapIso
      (V.sheafOfModulesEquivOverUnit (moduleRings U.toScheme.toRingedSpace)) ≪≫
      Modules.restrictUnitIso s.inv) ≪≫
        O.sheafOfModulesEquivOverInverseUnit (moduleRings X.toRingedSpace)
  have hK' : IsStrictlyPerfect X O K' := by
    obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
    constructor
    · exact ⟨a, b, fun n hn ↦ A.functor.map_isZero (hb n hn)⟩
    · intro n
      obtain ⟨m, i, p, hip⟩ := hp n
      let c : A.functor.obj (SheafOfModules.free
          (R := (moduleRings U.toScheme.toRingedSpace).over V) (ULift.{u} (Fin m))) ≅
          SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over O) (ULift.{u} (Fin m)) :=
        (asIso (sigmaComparison A.functor (fun _ : ULift.{u} (Fin m) ↦
          SheafOfModules.unit ((moduleRings U.toScheme.toRingedSpace).over V)))).symm ≪≫
          Sigma.mapIso (fun _ ↦ unitIso)
      refine ⟨m, A.functor.map i ≫ c.hom, c.inv ≫ A.functor.map p, ?_⟩
      change (A.functor.map i ≫ c.hom) ≫ c.inv ≫ A.functor.map p =
        𝟙 (A.functor.obj (K.X n))
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hip]
      exact A.functor.map_id _
  refine ⟨O, ?_, K', hK', ?_⟩
  · exact ⟨⟨x, hx⟩, hxV, rfl⟩
  · let G : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      (Modules.overEquiv U).functor
    let H := SheafOfModules.overFunctor.{u} (moduleRings U.toScheme.toRingedSpace) V
    let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) O
    have : (Modules.overEquiv U).functor.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_full _
    have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
      (Modules.overEquiv U).functor
    have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
    have : G.Additive := Functor.additive_of_preserves_binary_products _
    have fac : s.inv ≫ V.ι ≫ U.ι = O.ι := by
      rw [← Category.assoc, U.isoImage_ι_inv_ι V]
      exact X.homOfLE_ι _
    let c0 : (G ⋙ H) ⋙ (EV.functor ⋙ ES.functor) ≅ L ⋙ EO.functor :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft G ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Modules.overFunctorEquiv V) ES.functor) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerRight (Modules.overFunctorEquiv U) _) _ ≪≫
        Functor.isoWhiskerRight (Modules.restrictFunctorComp V.ι U.ι).symm ES.functor ≪≫
        (Modules.restrictFunctorComp s.inv (V.ι ≫ U.ι)).symm ≪≫
        Modules.restrictFunctorCongr fac ≪≫ (Modules.overFunctorEquiv O).symm
    let c : (G ⋙ H) ⋙ A.functor ≅ L :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c0 EO.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L EO.unitIso.symm ≪≫
        Functor.rightUnitor L
    set_option backward.isDefEq.respectTransparency true in
    let model : (G ⋙ H).mapDerivedCategory.obj R ≅ DerivedCategory.Q.obj K :=
      (Functor.mapDerivedCategoryCompIso G H).symm.app R ≪≫
        H.mapDerivedCategory.mapIso e ≪≫ hmodel
    set_option backward.isDefEq.respectTransparency true in
    exact ⟨(Functor.mapDerivedCategoryNatIso c).symm.app R ≪≫
      (Functor.mapDerivedCategoryCompIso (G ⋙ H) A.functor).symm.app R ≪≫
      A.functor.mapDerivedCategory.mapIso model ≪≫ A.functor.mapDerivedCategoryFactors.app K⟩

end AlgebraicGeometry.Scheme
