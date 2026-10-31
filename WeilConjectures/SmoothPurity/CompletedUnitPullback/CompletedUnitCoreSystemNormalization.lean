/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitTensorSystemData
import WeilConjectures.SmoothPurity.CompletedUnitPullback.Reduction.CompletedUnitReductionUnique
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitCanonicalRegularModel
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularModelRigidity

/-! # Reduction of the normalized regular coefficient pullback map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

attribute [local implicit_reducible] calculus pullbackTensorCalculus

private theorem transport_reduction
    {C S T : Type*} [Category C] [Category S] [Category T]
    (R : C ⥤ S) (L : S ⥤ C) (adj : R ⊣ L)
    (H G : T ⥤ S) (h : H = G) (A B : T) (a : A ⟶ B)
    (W : S) (s : G.obj B ⟶ W) (t : H.obj B ⟶ W)
    (hs : eqToHom (congrArg (fun F ↦ F.obj B) h) ≫ s = t)
    (U V : C) (v : U ⟶ V) (d : R.obj V ⟶ W)
    (m : U ⟶ L.obj (H.obj A))
    (hv : R.map v ≫ d =
      R.map (m ≫ L.map (eqToHom (congrArg (fun F ↦ F.obj A) h))) ≫
        adj.counit.app (G.obj A) ≫ G.map a ≫ s) :
    R.map v ≫ d = R.map m ≫ adj.counit.app (H.obj A) ≫ H.map a ≫ t := by
  subst G
  simp only [eqToHom_refl, Category.id_comp] at hs
  subst t
  simpa only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id] using hv

/-- The normalized completed regular-unit arrow reduces to ordinary ring multiplication.

Source: Stacks 0941 and 07A4; Bhatt--Scholze Sections 3.5 and 6.5;
Steps 2--3 of lem-pur-completed-unit-common-tensor-unitor.
(blueprint: lem-pur-completed-unit-core-system-normalization).

Proof: first identify the ring map in PrimitiveCounit with the sequence-ring
map: their components are the same constant-section ring maps at every level,
and their transitions are the quotient maps. Uniqueness of left adjoints,
with its unit equation, identifies their inverse-image functors and the
adjoints of the unit-to-pushforward-unit maps. Thus systemMap becomes the
single-complex image of tensorSystemRegularPullback. The two pullback Roos
models are normalized on the same K-flat resolutions and projections; their
comparison cancels with the coherent counit by the adjunction triangle.
Substitute Core.coherent_reduction and the augmentation equations. The two
strict regular reductions agree: their maps on finite regular sections are
the identity; degree-zero full faithfulness and the strict quotient-system
identification give equality of these whole-system maps. This permits using
reductionX on both sides, even for an endomorphism with distinct proof fields
for source and target. Finally compose with tensorSystemUnit.inv and use
functoriality. This is an equality in the whole system derived category;
no faithfulness of arbitrary finite derived evaluation is asserted. The
same computation includes the empty scheme and the identity endomorphism. -/
theorem completedUnit_core_tensorSystemReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (f : X ⟶ X) (c : Core l E f) :
    let K := integralObject l E X c.admissibleX.1.1
    let d := regularTensorSystemComparison l E X c.reductionX
    (pullbackTensorCalculus l E X).reduction.map c.unit.hom ≫ d.hom =
      (pullbackTensorIntegralReductionPullback l E f K).hom ≫
        (pullbackTensorSequenceDerived l E f).map d.hom ≫
          (tensorSystemPullbackUnit l E f).hom := by
  dsimp only
  have hr : regularPullbackModel l E f c.roos c.realization :=
    c.realization_model (constantWeilIntegralGood l E X)
  have hreal := regularPullbackModel_rigid l E f c.roos c.realization
    (tensorPrimitiveRealization l E f) hr
    (tensorPrimitiveRealization_regularModel l E f c.roos)
  have hred := Reduction.comparison_eq l E X (calculus l E X) c.reductionY c.reductionX
  have hcore := c.coherent_reduction
  rw [hreal, tensorPrimitiveRealization_hom] at hcore
  have h := transport_reduction
    (calculus l E X).reduction (coefficientSequenceLimit l E X)
    (calculus l E X).adjunction
    (pullbackTensorSequenceDerived l E f) (PrimitiveCounit.pull l E f)
    (systemPullback_eq l E f) _ _ c.reductionY.comparison.hom _
    (systemMap l E f) (tensorSystemRegularPullback l E f).hom
    (systemPullback_regular l E f) _ _ c.unit.hom c.reductionX.comparison.hom
    ((pullbackTensorIntegralPullbackModel l E f).hom.app
      (integralConstantCoefficientObject l E X)) hcore
  rw [hred] at h
  dsimp only [regularTensorSystemComparison, tensorSystemPullbackUnit,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (pullbackTensorSequenceDerived l E f).map_comp_assoc
    (tensorSystemUnit l E X).inv (tensorSystemUnit l E X).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [pullbackTensorIntegralReductionPullback, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, asIso_hom, Category.assoc,
    calculus, pullbackTensorCalculus, integralObject] using
      congrArg (fun k ↦ k ≫ (tensorSystemUnit l E X).inv) h

end WeilConjectures.CompletedUnitPullback
