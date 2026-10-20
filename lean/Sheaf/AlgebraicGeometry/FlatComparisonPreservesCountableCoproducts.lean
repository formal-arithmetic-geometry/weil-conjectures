/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSumsCofan
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-! # Countable coproduct preservation for the two flat comparison functors

Source: step 3 of lem-sc-flat-telescope-sum-comparison-is-iso; Stacks Tags
07D9 and 079W. (blueprint: lem-sc-flat-comparison-preserves-countable-coproducts).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private noncomputable def quotient_coproduct_cofan
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C] (K : I → CochainComplex C ℤ) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj (∐ K))
      (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).map (Sigma.ι K i))) := by
  classical
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hu (X : HomotopyCategory C (.up ℤ)) (a : ∀ i, q.obj (K i) ⟶ X) :
      ∃! d : q.obj (∐ K) ⟶ X, ∀ i, q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    choose f hf using fun i ↦ q.map_surjective (a i)
    refine ⟨q.map (Sigma.desc f), ?_, ?_⟩
    · intro i
      rw [← Functor.map_comp, Sigma.ι_desc, hf]
    · intro m hm
      obtain ⟨g, rfl⟩ := q.map_surjective m
      have h (i : I) : Homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f) :=
        HomotopyCategory.homotopyOfEq _ _ (by
          rw [Sigma.ι_desc, Functor.map_comp, hm, hf])
      exact HomotopyCategory.eq_of_homotopy _ _
        (CategoryTheory.coproduct_homotopy K g (Sigma.desc f) h).some
  exact Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt t.inj).choose)
    (fun t i ↦ (hu t.pt t.inj).choose_spec.1 i)
    (fun t m hm ↦ (hu t.pt t.inj).choose_spec.2 m hm)

private theorem homotopy_preserves_coproducts_of_composite
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C]
    {D : Type*} [Category D] (F : HomotopyCategory C (.up ℤ) ⥤ D)
    [PreservesColimitsOfShape (Discrete I) (HomotopyCategory.quotient C (.up ℤ) ⋙ F)] :
    PreservesColimitsOfShape (Discrete I) F := by
  classical
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hp (X : I → HomotopyCategory C (.up ℤ)) :
      PreservesColimit (Discrete.functor X) F := by
    choose K hK using fun i ↦ HomotopyCategory.quotient_obj_surjective (X i)
    have hc := quotient_coproduct_cofan K
    have hm := isColimitCofanMkObjOfIsColimit (q ⋙ F) K _ (coproductIsCoproduct K)
    have : PreservesColimit (Discrete.functor (fun i ↦ q.obj (K i))) F :=
      preservesColimit_of_preserves_colimit_cocone hc
        ((Cofan.isColimitMapCoconeEquiv F _ _).symm hm)
    let e : Discrete.functor (fun i ↦ q.obj (K i)) ≅ Discrete.functor X :=
      Discrete.natIso (fun i ↦ eqToIso (hK i.as))
    exact preservesColimit_of_iso_diagram F e
  exact preservesColimitsOfShape_of_discrete F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_Q_preserves_coproducts (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))) := by
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  have hp (K : I → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
      PreservesColimit (Discrete.functor K) Q := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    refine (Cofan.isColimitMapCoconeEquiv Q K _).symm ?_
    change IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ DerivedCategory.Q.map (Sigma.ι K i)))
    have hc := (derivedAmbientDirectSumsCofan Y I (fun i ↦ Q.obj (K i)) K
      (fun i ↦ Iso.refl _)).some
    exact IsColimit.ofIsoColimit hc (Cofan.ext (Iso.refl _) (fun i ↦ by
      change (𝟙 _ ≫ DerivedCategory.Q.map (Sigma.ι K i)) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id, cofan_mk_inj]))
  exact preservesColimitsOfShape_of_discrete Q

/-- Both sides of the flat comparison preserve countable homotopy coproducts.

Source: step 3 of lem-sc-flat-telescope-sum-comparison-is-iso; Stacks Tags
07D9 and 079W, and the module pullback adjunction (Tag 0096).

Proof. Represent every homotopy object by a complex. The homotopy coproduct is
represented by their termwise coproduct: maps and homotopies out of it assemble
independently on each summand. The derived ambient direct-sums cofan theorem
identifies its image under Qh as the derived coproduct, since module sheaves have
exact coproducts. Reindex by ULift to use that theorem in the scheme universe,
then transport back along the discrete equivalence. Derived pullback is a left
adjoint by the derived ringed-space adjunction and hence preserves this coproduct.
For the other functor the tensor pullback is left adjoint to module pushforward.
It preserves termwise coproducts, and its additive homotopy functor transports
the same cofan. Apply the derived ambient direct-sums cofan theorem on Z to
finish. Transport from the representative coproduct cofan to any colimit cofan
by uniqueness of colimits. This argument uses no flatness or boundedness,
no comparison family, and no properness; it also applies to zero summands.
(blueprint: lem-sc-flat-comparison-preserves-countable-coproducts). -/
theorem flat_comparison_preserves_countable_coproducts
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(Scheme.Modules.tensorPullback f).Additive] :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.Qh ⋙ derivedPullback f) ∧
      PreservesColimitsOfShape (Discrete ℕ)
        ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let qA := HomotopyCategory.quotient A (.up ℤ)
  let qB := HomotopyCategory.quotient B (.up ℤ)
  let QY := DerivedCategory.Q (C := A)
  let QZ := DerivedCategory.Q (C := B)
  let L := DerivedCategory.Qh ⋙ derivedPullback f
  let H : A ⥤ B := Scheme.Modules.tensorPullback f
  let G := H.mapHomotopyCategory (.up ℤ) ⋙ (DerivedCategory.Qh (C := B))
  let I := ULift.{u} ℕ
  have : PreservesColimitsOfShape (Discrete I) QY := derived_Q_preserves_coproducts Y I
  have : PreservesColimitsOfShape (Discrete I) QZ := derived_Q_preserves_coproducts Z I
  obtain ⟨adj⟩ := nonempty_derivedPullbackAdjunction f
  have : (derivedPullback f).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesColimitsOfShape (Discrete I) (QY ⋙ derivedPullback f) := inferInstance
  have : PreservesColimitsOfShape (Discrete I) (qA ⋙ L) :=
    preservesColimitsOfShape_of_natIso
      ((Functor.associator qA DerivedCategory.Qh (derivedPullback f)).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) (derivedPullback f)).symm
  have hL : PreservesColimitsOfShape (Discrete I) L :=
    homotopy_preserves_coproducts_of_composite L
  obtain ⟨adjH, _⟩ := Scheme.Modules.exists_tensorPullbackAdjunction f
  have : H.IsLeftAdjoint := ⟨_, ⟨adjH⟩⟩
  have : PreservesColimitsOfShape (Discrete I) (H.mapHomologicalComplex (.up ℤ) ⋙ QZ) :=
    inferInstance
  have : PreservesColimitsOfShape (Discrete I) (qA ⋙ G) :=
    preservesColimitsOfShape_of_natIso
      ((Functor.associator qA (H.mapHomotopyCategory (.up ℤ))
        (DerivedCategory.Qh (C := B))).symm ≪≫
        Functor.isoWhiskerRight (H.mapHomotopyCategoryFactors (.up ℤ))
          (DerivedCategory.Qh (C := B)) ≪≫
        Functor.associator (H.mapHomologicalComplex (.up ℤ)) qB
          (DerivedCategory.Qh (C := B)) ≪≫
        Functor.isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.quotientCompQhIso B)).symm
  have hG : PreservesColimitsOfShape (Discrete I) G :=
    homotopy_preserves_coproducts_of_composite (C := A) G
  exact ⟨preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) L,
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) G⟩

end AlgebraicGeometry
