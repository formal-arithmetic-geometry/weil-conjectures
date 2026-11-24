/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.TensorPullbackStalkComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Pullback preserves K-flat complexes

The pulled-back complex has terms given by the topological module inverse image
followed by sheafified sectionwise change of rings along the adjoint structure map.
Its differentials are inverse images of the original differentials followed by
`changeOfRingsHom`. No comparison with an abstract module pullback is used.

## References

* Stacks Project, Tags 0095 and 06YC (Cohomology, Lemma 20.26.8)
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CochainComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{w}} (f : X ⟶ Y)
    (OX : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w})
    (OY : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{w})
    (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous CommRingCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)

/-- The ring map `f⁻¹ OY → OX` adjoint to the structure-sheaf map. -/
def tensorPullbackRingMap : TopCat.Sheaf.inverseImageRing f OY ⟶ OX :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) CommRingCat.{w} _ _).homEquiv OY OX).symm φ

private theorem inverseImageModuleMap_zero
    (M N : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) :
    TopCat.Sheaf.inverseImageModuleMap f OY M (0 : M ⟶ N) = 0 := by
  let F := TopCat.Sheaf.inverseImageConstruction f AddCommGrpCat.{w}
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{w}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  have : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : F.PreservesZeroMorphisms := inferInstance
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk, F]
  rfl

private theorem changeOfRingsHom_zero
    (M N : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (TopCat.Sheaf.inverseImageRing f OY))) :
    SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      M (0 : M ⟶ N) = 0 := by
  let p :
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap f OX OY φ) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap f OX OY φ) N :=
    { app := fun U ↦ (ModuleCat.extendScalars _).map ((0 : M ⟶ N).val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality _ M 0 }
  have hp : p = 0 := by
    apply PresheafOfModules.hom_ext
    intro U
    have hz : (0 : M ⟶ N).val.app U = 0 := rfl
    change (ModuleCat.extendScalars
      ((tensorPullbackRingMap f OX OY φ).hom.app U).hom).map _ = 0
    rw [hz]
    exact Functor.map_zero _ _ _
  change (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OX).obj)).map p = 0
  rw [hp, Functor.map_zero]

private theorem inverseImageModuleMap_comp
    {M N P : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)} (a : M ⟶ N) (b : N ⟶ P) :
    TopCat.Sheaf.inverseImageModuleMap f OY M (a ≫ b) =
      TopCat.Sheaf.inverseImageModuleMap f OY M a ≫
        TopCat.Sheaf.inverseImageModuleMap f OY N b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
  rfl

private theorem changeOfRingsHom_comp
    {M N P : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (TopCat.Sheaf.inverseImageRing f OY))} (a : M ⟶ N) (b : N ⟶ P) :
    SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      M (a ≫ b) =
    SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ) M a ≫
      SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ) N b := by
  unfold SheafOfModules.changeOfRingsHom
  rw [← Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  change (ModuleCat.extendScalars
    ((tensorPullbackRingMap f OX OY φ).hom.app U).hom).map (a.val.app U ≫ b.val.app U) = _
  exact Functor.map_comp _ _ _

variable (K : CochainComplex (SheafOfModules.{w}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) ℤ)

/-- The differential obtained by inverse image and the sectionwise tensor map. -/
def tensorPullbackDifferential (i j : ℤ) :
    SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      (TopCat.Sheaf.inverseImageModule f OY (K.X i)) ⟶
    SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      (TopCat.Sheaf.inverseImageModule f OY (K.X j)) :=
  SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ)
    (TopCat.Sheaf.inverseImageModule f OY (K.X i))
    (TopCat.Sheaf.inverseImageModuleMap f OY (K.X i) (K.d i j))

/-- The tensor pullback differential has cochain shape. -/
theorem tensorPullbackDifferential_shape (i j : ℤ)
    (h : ¬ (ComplexShape.up ℤ).Rel i j) :
    tensorPullbackDifferential f OX OY φ K i j = 0 := by
  unfold tensorPullbackDifferential
  rw [K.shape i j h, inverseImageModuleMap_zero, changeOfRingsHom_zero]

/-- Consecutive tensor pullback differentials compose to zero. -/
theorem tensorPullbackDifferential_comp (i j k : ℤ) :
    tensorPullbackDifferential f OX OY φ K i j ≫
      tensorPullbackDifferential f OX OY φ K j k = 0 := by
  unfold tensorPullbackDifferential
  rw [← changeOfRingsHom_comp, ← inverseImageModuleMap_comp, K.d_comp_d,
    inverseImageModuleMap_zero, changeOfRingsHom_zero]

/-- The termwise formula `f⁻¹ K ⊗_{f⁻¹ OY} OX`, including its differentials. -/
def tensorPullbackComplex : CochainComplex (SheafOfModules.{w}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OX)) ℤ where
  X i := SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
    (TopCat.Sheaf.inverseImageModule f OY (K.X i))
  d := tensorPullbackDifferential f OX OY φ K
  shape := tensorPullbackDifferential_shape f OX OY φ K
  d_comp_d' i j k _ _ := tensorPullbackDifferential_comp f OX OY φ K i j k

set_option backward.isDefEq.respectTransparency true in
/-- Pullback along a morphism of ringed spaces preserves K-flatness. -/
theorem isKFlat_pullback
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    (OX : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w})
    (OY : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{w})
    (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous CommRingCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) ℤ)
    (hK : K.IsKFlatTensor) :
    IsKFlatTensor (R := OX) (tensorPullbackComplex f OX OY φ K) := by
  let RX : AlgebraicGeometry.RingedSpace.{w} :=
    { carrier := X, presheaf := OX.obj, IsSheaf := OX.property }
  let RY : AlgebraicGeometry.RingedSpace.{w} :=
    { carrier := Y, presheaf := OY.obj, IsSheaf := OY.property }
  have hstalk :=
    (AlgebraicGeometry.RingedSpace.isKFlat_iff_stalk_isKFlat RY K).mp hK
  apply (AlgebraicGeometry.RingedSpace.isKFlat_iff_stalk_isKFlat RX
    (tensorPullbackComplex f OX OY φ K)).mpr
  intro x L hL
  let ρ := AlgebraicGeometry.RingedSpace.tensorPullbackStalkRingHom RX RY f
    (tensorPullbackRingMap f OX OY φ) x
  let e := tensorPullbackStalkComplexIso RX RY f
    (tensorPullbackRingMap f OX OY φ) K (tensorPullbackComplex f OX OY φ K)
    (fun i ↦ Iso.refl _)
    (by
      intro i j
      exact (Category.comp_id _).trans (Category.id_comp _).symm) x
  have : (AlgebraicGeometry.RingedSpace.moduleStalkFunctor RY (f x)).PreservesZeroMorphisms :=
    AlgebraicGeometry.RingedSpace.moduleStalkFunctor_preservesZeroMorphisms RY (f x)
  have ht := acyclic_mapBifunctor_extendScalars_of_kFlat ρ
    (((AlgebraicGeometry.RingedSpace.moduleStalkFunctor RY (f x)).mapHomologicalComplex
      (.up ℤ)).obj K)
    (by intro F hF; exact hstalk (f x) F hF) L hL
  let T := ((MonoidalCategory.curriedTensor
    (ModuleCat.{w} (RX.presheaf.stalk x))).map₂CochainComplex).obj L
  intro i
  exact (ht i).of_iso (T.mapIso e)

end
end CochainComplex
