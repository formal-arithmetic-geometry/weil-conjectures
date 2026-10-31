/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections

/-! # The section-ring map induced by component inverse image
Source: Hemo--Richarz--Scholbach, Construction (4.1), Remark 3.2 and Proposition 4.3(3).
(blueprint: def-zl-component-section-map).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]

/-- Pull a global section back by the specified monoidal inverse image, then apply α.
The section/global-section equivalence is proved independently of all geometric claims.
Thus this is a constructed ring map, including when either section ring is the zero ring.
Source: HRS Construction (4.1), Proposition 4.3(1), equation (4.2)
(blueprint: def-zl-component-section-map). -/
def componentSectionMap
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T)) :
    Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ.X (affineComponentSpace T))
        (Over.mk (𝟙 (affineComponentSpace T))) →+*
      Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
        (Scheme.ProEt.mk (𝟙 T)) := by
  letI := Functor.additive_of_preserves_binary_products (componentInverse T)
  let e := InternalAbelianSheafModule.sectionGlobalEquiv
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (profiniteCoefficient Λ.X (affineComponentSpace T))
    (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal
  let q := MonObj.Γ.mapFunctor (componentInverse T)
    (R := profiniteCoefficient Λ.X (affineComponentSpace T))
  let p := MonObj.Γ.map α.hom.hom
  let v := InternalAbelianSheafModule.sectionGlobalEval (Scheme.ProEt.topology T)
    (condensedRingObj Λ.X T) (Scheme.ProEt.mk (𝟙 T))
  exact v.comp (p.comp (q.comp e.symm.toRingHom))

/-- Full faithfulness of inverse image makes the constructed section map bijective.
Source: HRS Proposition 4.3(1), terminal-section specialization
(blueprint: lem-zl-component-section-map-bijective). -/
theorem componentSectionMap_bijective
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T))
    (h : (componentInverse T).FullyFaithful) :
    Function.Bijective (componentSectionMap Λ T α) := by
  let := Functor.additive_of_preserves_binary_products (componentInverse T)
  let e := InternalAbelianSheafModule.sectionGlobalEquiv
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (profiniteCoefficient Λ.X (affineComponentSpace T))
    (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal
  have hp : Function.Bijective (MonObj.Γ.map α.hom.hom) := by
    constructor
    · intro x y he
      apply MonObj.Γ.ext
      apply (cancel_mono α.hom.hom).mp
      exact congrArg MonObj.Γ.hom he
    · intro y
      refine ⟨MonObj.Γ.ofHom (y.hom ≫ α.inv.hom), ?_⟩
      apply MonObj.Γ.ext
      change (y.hom ≫ α.inv.hom) ≫ α.hom.hom = y.hom
      rw [Category.assoc, show α.inv.hom ≫ α.hom.hom = 𝟙 _ from
        congrArg Mon.Hom.hom α.inv_hom_id, Category.comp_id]
  exact (InternalAbelianSheafModule.sectionGlobalEval_bijective
    (Scheme.ProEt.topology T) (condensedRingObj Λ.X T) (Scheme.ProEt.mk (𝟙 T))
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T)).comp
      (hp.comp ((InternalAbelianSheafModule.globalMapFunctor_bijective
        (componentInverse T) h _).comp e.symm.bijective))

end AlgebraicGeometry.ProEtale.CondensedRing
