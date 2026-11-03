/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientLeftUnitCoherence
import WeilConjectures.CategoryTheory.SmoothPurity.CompositeLeftUnitCoherence
import WeilConjectures.CategoryTheory.Tensor.TensorIsoUnitCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.QuotientScalarTensorComposition

/-! # Composition of the transported scalar units

Source: smooth-purity reduction compatibilities, part (3).
(blueprint: lem-pur-finite-smooth-zero-twist-composition).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem tensor_naturality_left
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    (d : Functor.uncurry.obj (curriedTensor C) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor D))
    {P Q : C} (a : P ⟶ Q) (M : C) :
    S.map (a ▷ M) ≫ d.hom.app (Q, M) =
      d.hom.app (P, M) ≫ S.map a ▷ S.obj M := by
  have h := d.hom.naturality (show (P, M) ⟶ (Q, M) from (a, 𝟙 M))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  change S.map (a ▷ M ≫ Q ◁ 𝟙 M) ≫ d.hom.app (Q, M) = _ at h
  simp only [whiskerLeft_id, Category.comp_id] at h
  change S.map (a ▷ M) ≫ d.hom.app (Q, M) =
    d.hom.app (P, M) ≫ S.map a ▷ S.obj M ≫ S.obj Q ◁ S.map (𝟙 M) at h
  rw [S.map_id, whiskerLeft_id, Category.comp_id] at h
  exact h

private theorem quotient_unit_comp
    (T : Scheme.{u}) (ell : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    (ordinaryScalar (FiniteReduction.quotient ell hnm) T).map
        (ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell hmr) T).hom ≫
      (ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell hnm) T).hom =
    (ordinaryAssociator T ell hmr hnm).hom.app
        (𝟙_ (DerivedCategoryModule (coefficient ell r) T)) ≫
      (ExceptionalCoefficients.unitIso
        (FiniteReduction.quotient ell (hnm.trans hmr)) T).hom := by
  let F := ordinaryScalar (FiniteReduction.quotient ell hmr) T
  let G := ordinaryScalar (FiniteReduction.quotient ell hnm) T
  let H := ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T
  let dF := ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hmr) T
  let dG := ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hnm) T
  let dH := ExceptionalCoefficients.tensorIso
    (FiniteReduction.quotient ell (hnm.trans hmr)) T
  let eF := ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell hmr) T
  let eG := ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell hnm) T
  let eH := ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell (hnm.trans hmr)) T
  symm
  apply tensorIso_preserves_unit (F ⋙ G) H (ordinaryAssociator T ell hmr hnm)
    (fun P Q ↦ G.mapIso (dF.app (P, Q)) ≪≫ dG.app (F.obj P, F.obj Q))
    (fun P Q ↦ dH.app (P, Q)) (G.mapIso eF ≪≫ eG) eH
  · intro P
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    apply composite_left_unit F G (fun P Q ↦ dF.app (P, Q))
      (fun P Q ↦ dG.app (P, Q)) _ eF eG
      (ExceptionalCoefficients.tensorIso_left_unit _ T)
      (ExceptionalCoefficients.tensorIso_left_unit _ T) P
    intro P Q a M
    exact tensor_naturality_left G dG a M
  · exact ExceptionalCoefficients.tensorIso_left_unit _ T
  · intro P Q
    simpa only [F, G, H, dF, dG, dH, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, derivedTensor, curriedTensor_obj_obj, curriedTensor_obj_map,
      curriedTensor_map_app, MonoidalCategory.tensorHom_def, Functor.comp_obj,
      Functor.uncurry_obj_obj, Functor.prod_obj, Category.assoc]
      using (quotientScalarTensorComp T ell hmr hnm P Q).symm

private theorem unit_transport_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (α : F ⋙ G ≅ H)
    {A I : C} {B J : D} {P K : E}
    (u : A ≅ I) (v : B ≅ J) (w : P ≅ K)
    (e : F.obj I ≅ J) (f : G.obj J ≅ K) (g : H.obj I ≅ K)
    (h : G.map e.hom ≫ f.hom = α.hom.app I ≫ g.hom) :
    G.map (F.mapIso u ≪≫ e ≪≫ v.symm).hom ≫
        (G.mapIso v ≪≫ f ≪≫ w.symm).hom =
      α.hom.app A ≫ (H.mapIso u ≪≫ g ≪≫ w.symm).hom := by
  have hv : G.map v.inv ≫ G.map v.hom = 𝟙 _ := by
    rw [← G.map_comp, v.inv_hom_id, G.map_id]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hv, reassoc_of% h]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (· ≫ g.hom ≫ w.inv) (α.hom.naturality u.hom)

/-- The scalar unit comparisons transported to tensor-power zero compose canonically.
Source: smooth-purity reduction compatibilities (3), scalar units and tensor powers.
(blueprint: lem-pur-finite-smooth-zero-twist-composition).
Proof: binary scalar tensor compatibility and the left-unit laws force compatibility
of the unit maps, by tensorIso_preserves_unit. The composite left-unit law follows
by naturality of the second tensor comparison. Transport the unit equation along
the single/unit isomorphisms; their middle inverse pairs cancel, and naturality
of the scalar associator gives the displayed equality. -/
theorem ordinaryZeroTwistComp
    (T : Scheme.{u}) (ell : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    (ordinaryScalar (FiniteReduction.quotient ell hnm) T).map
        (scalarZeroLineIso (FiniteReduction.quotient ell hmr)
          (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T).hom ≫
      (scalarZeroLineIso (FiniteReduction.quotient ell hnm)
        (ell ^ m) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T).hom =
    (ordinaryAssociator T ell hmr hnm).hom.app
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) T 0) ≫
      (scalarZeroLineIso (FiniteReduction.quotient ell (hnm.trans hmr))
        (ell ^ r) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T).hom := by
  exact unit_transport_comp
    (ordinaryScalar (FiniteReduction.quotient ell hmr) T)
    (ordinaryScalar (FiniteReduction.quotient ell hnm) T)
    (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T)
    (ordinaryAssociator T ell hmr hnm)
    (singleFunctorObjUnitIso (ModuleCat (coefficient ell r)) T)
    (singleFunctorObjUnitIso (ModuleCat (coefficient ell m)) T)
    (singleFunctorObjUnitIso (ModuleCat (coefficient ell n)) T)
    (ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell hmr) T)
    (ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell hnm) T)
    (ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell (hnm.trans hmr)) T)
    (quotient_unit_comp T ell hmr hnm)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
