/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorNativeModels
import all WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationModel
import all WeilConjectures.Algebra.Homology.ScalarTensorExactRepresentative
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.AlgebraicGeometry.DerivedScalarTensorOrdinary

/-! # The scalar balancing map on coefficient-unit resolutions

Source: Stacks Project, Tags 03EK, 07A4 and 07A6.
(blueprint: lem-sp-open-scalar-balancing-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor
attribute [local instance] ScalarDerivedPair.extension_additive

private def ordinaryScalars (m : Models.{u}) (T : Scheme.{u}) :
    ScalarOrdinaryEvaluation.Scalars.{u + 1, u, u + 1} (J := Scheme.ProEt.topology T) where
  E := fun a ↦ ((m T).scalar a).extension
  additive := fun a ↦ ((m T).scalar a).extension_additive
  obj_eq := fun a ↦ ((m T).scalar a).extension_obj
  map_eq := fun a ↦ ((m T).scalar a).extension_map
  adj := fun a ↦ ((m T).scalar a).ordinaryAdjunction
  unit_pure := fun a ↦ ((m T).scalar a).ordinaryUnit

private def coefficientTensorSingleComparison
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (proEtaleConstantRing T A)).obj (P,
        ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (proEtaleConstantRingMap (T := T) φ)).mapHomologicalComplex (.up ℤ)).obj
          (ringedTensorUnitComplex.{u + 1, u, u + 1}
            (Scheme.ProEt.topology T) (proEtaleConstantRing T B))) ≅
      (StrictScalarHom.tensor.{u + 1, u, u + 1}
        (proEtaleConstantRingMap (T := T) φ)).obj P := by
  let J := Scheme.ProEt.topology T
  let RA := proEtaleConstantRing T A
  let RB := proEtaleConstantRing T B
  let a := proEtaleConstantRingMap (T := T) φ
  let rr := SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a
  let e := (HomologicalComplex.singleMapHomologicalComplex rr (.up ℤ) (0 : ℤ)).app
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RB))
  letI := SheafOfModules.cochainModulesMonoidal RA
  letI := SheafOfModules.cochainModulesSymmetric RA
  let b : tensorRight (DerivedScalarMate.coefficient a) ≅
      tensorLeft (DerivedScalarMate.coefficient a) :=
    NatIso.ofComponents (fun N ↦ β_ N (DerivedScalarMate.coefficient a)) (by
      intro N M f
      exact BraidedCategory.braiding_naturality_left f (DerivedScalarMate.coefficient a))
  exact (coefficientTotalTensor.{u + 1, u + 1, u} J RA).mapIso ((Iso.refl P).prod e) ≪≫
    CochainComplex.mapBifunctorSingle₂Iso (proEtaleOrdinaryTensor T RA)
      (DerivedScalarMate.coefficient a) P ≪≫ (NatIso.mapHomologicalComplex b (.up ℤ)).app P

private theorem tensorSingle_inv_pure (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (N : proEtaleRingModules T R)
    (P : CochainComplex (proEtaleRingModules T R) ℤ)
    (n : ℤ) (V : T.ProEtᵒᵖ) (x : (P.X n).val.obj V) (y : N.val.obj V) :
    (((CochainComplex.mapBifunctorSingle₂Iso (proEtaleOrdinaryTensor T R) N P).inv.f n).val.app V)
      (ScalarHomOrdinary.pure R (P.X n) N V x y) =
    coefficientTensorGenerator.{u + 1, u + 1, u} (Scheme.ProEt.topology T) R P
      ((HomologicalComplex.single (proEtaleRingModules T R) (.up ℤ) (0 : ℤ)).obj N)
      n 0 n (add_zero n) V x
      ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) N).inv.val.app V y) := by
  let := SheafOfModules.cochainModulesMonoidal R
  rw [CochainComplex.mapBifunctorSingle₂Iso_inv_f]
  change _ = (HomologicalComplex.ιMapBifunctor P _ (proEtaleOrdinaryTensor T R)
    (.up ℤ) n 0 n (add_zero n)).val.app V _
  change (HomologicalComplex.ιMapBifunctor P _ (proEtaleOrdinaryTensor T R)
    (.up ℤ) n 0 n (add_zero n)).val.app V _ = _
  congr 1
  have h := ScalarHomOrdinary.pure_map R (𝟙 (P.X n))
    (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) N).inv V x y
  convert h using 1 <;> simp only [id_tensorHom, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply, ScalarHomOrdinary.pure,
    proEtaleOrdinaryTensor, curriedTensor, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  all_goals rfl



set_option maxHeartbeats 2000000 in
-- The pointwise single-complex tensor and braiding comparisons have dependent carriers.
private theorem coefficientTensorSingleComparison_inv_pure
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (n : ℤ) (V : T.ProEtᵒᵖ) (b : (proEtaleConstantRing T B).obj.obj V)
    (x : (P.X n).val.obj V) :
    (((coefficientTensorSingleComparison φ T P).inv.f n).val.app V)
      (StrictScalarHom.tensorSection.{u + 1, u, u + 1}
        (proEtaleConstantRingMap (T := T) φ) P n V b x) =
    coefficientTensorGenerator.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (proEtaleConstantRing T A) P _ n 0 n (add_zero n) V x
      (ringedTensorUnitSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (proEtaleConstantRing T B) V b) := by
  let J := Scheme.ProEt.topology T
  let RA := proEtaleConstantRing T A
  let RB := proEtaleConstantRing T B
  let a := proEtaleConstantRingMap (T := T) φ
  let b' : (DerivedScalarMate.coefficient a).val.obj V := b
  let := SheafOfModules.cochainModulesMonoidal RA
  let := SheafOfModules.cochainModulesSymmetric RA
  let rr := SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a
  let e := (HomologicalComplex.singleMapHomologicalComplex rr (.up ℤ) (0 : ℤ)).app
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RB))
  change (((coefficientTotalTensor.{u + 1, u + 1, u} J RA).map
    (Prod.mkHom (𝟙 P) e.inv)).f n).val.app V
      (((CochainComplex.mapBifunctorSingle₂Iso (proEtaleOrdinaryTensor T RA)
        (DerivedScalarMate.coefficient a) P).inv.f n).val.app V
        ((β_ (P.X n) (DerivedScalarMate.coefficient a)).inv.val.app V
          (CochainPullback.moduleTmul (J := J) (R := RA) _ _ V b' x))) = _
  erw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  erw [CochainPullback.moduleTmul_braiding (J := J) (R := RA)
    (DerivedScalarMate.coefficient a) (P.X n) V b' x]
  rw [show CochainPullback.moduleTmul (J := J) (R := RA) (P.X n)
      (DerivedScalarMate.coefficient a) V x b' =
      ScalarHomOrdinary.pure RA (P.X n) (DerivedScalarMate.coefficient a) V x b' from rfl]
  rw [tensorSingle_inv_pure]
  have hm := ScalarHomTensor.tensor_generator_map.{u + 1, u, u + 1}
    (J := J) (R := RA) (𝟙 P) e.inv n 0 n (add_zero n) V x
    ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (DerivedScalarMate.coefficient a)).inv.val.app V b')
  erw [hm]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  congr 1


set_option maxHeartbeats 2000000 in
-- Evaluate scalar unit, total tensor and right-unit comparisons on pure sections.
private theorem scalar_balancing_base_isIso
    (m : Models.{u}) (T : Scheme.{u})
    (μ : ∀ {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
      (a : R ⟶ S), ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2}
        (J := Scheme.ProEt.topology T) (m T) a)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (r : (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (proEtaleConstantRing T B)).obj
      ((scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
        (scalarPair m φ T).extension_additive).obj P,
        ringedTensorUnitComplex.{u + 1, u, u + 1}
          (Scheme.ProEt.topology T) (proEtaleConstantRing T B)) ≅
      (scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
        (scalarPair m φ T).extension_additive).obj P)
    (hr : ∀ (n : ℤ) (h : n + 0 = n) (V : T.ProEtᵒᵖ)
      (b : (proEtaleConstantRing T B).obj.obj V)
      (x : (((scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
        (scalarPair m φ T).extension_additive).obj P).X n).val.obj V),
      (r.hom.f n).val.app V
        (coefficientTensorGenerator.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
          (proEtaleConstantRing T B) _ _ n 0 n h V x
          (ringedTensorUnitSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            (proEtaleConstantRing T B) V b)) = b • x) :
    let a := proEtaleConstantRingMap (T := T) φ
    let E := scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
      (scalarPair m φ T).extension_additive
    let O := ringedTensorUnitComplex.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (proEtaleConstantRing T B)
    let C := ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex
      (.up ℤ)).obj O
    let adj := ScalarHomTensor.chainAdj (J := Scheme.ProEt.topology T) (m T) a
    let t := (adj.homEquiv C O).symm (𝟙 C)
    IsIso ((adj.homEquiv _ _) (((μ a).complexIso P C).hom ≫
      (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
        (proEtaleConstantRing T B)).map (Prod.mkHom (𝟙 (E.obj P)) t) ≫ r.hom)) := by
  let J := Scheme.ProEt.topology T
  let RA := proEtaleConstantRing T A
  let RB := proEtaleConstantRing T B
  let a := proEtaleConstantRingMap (T := T) φ
  let E := scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
      (scalarPair m φ T).extension_additive
  let O := ringedTensorUnitComplex.{u + 1, u, u + 1} J RB
  let C := ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex
      (.up ℤ)).obj O
  let adj := ScalarHomTensor.chainAdj (J := J) (m T) a
  let t := (adj.homEquiv C O).symm (𝟙 C)
  let TS := coefficientTotalTensor.{u + 1, u + 1, u} J RB
  let l := ((μ a).complexIso P C).hom ≫ TS.map (Prod.mkHom (𝟙 (E.obj P)) t) ≫ r.hom
  let k := (adj.homEquiv _ _) l
  let ν := ScalarOrdinaryEvaluation.normalizedNu (ordinaryScalars m T) a
  have he : (coefficientTensorSingleComparison φ T P).inv ≫ k = ν.hom.app P := by
    ext n : 1
    apply ScalarHomOrdinary.pure_hom_ext RA _ _ _
    intro V b x
    change (k.f n).val.app V
      (((coefficientTensorSingleComparison φ T P).inv.f n).val.app V
        (StrictScalarHom.tensorSection a P n V b x)) = _
    rw [coefficientTensorSingleComparison_inv_pure]
    have ht := congrArg (fun z ↦ (z.f 0).val.app V
      (ringedTensorUnitSection.{u + 1, u, u + 1} J RB V b))
      ((adj.homEquiv C O).apply_symm_apply (𝟙 C))
    rw [Adjunction.homEquiv_unit] at ht
    change (t.f 0).val.app V
      (scalarHomUnitSection (m T) a (C.X 0) V
        (ringedTensorUnitSection.{u + 1, u, u + 1} J RB V b)) =
      ringedTensorUnitSection.{u + 1, u, u + 1} J RB V b at ht
    have hg := (μ a).generators P C n 0 n (add_zero n) V x
      (ringedTensorUnitSection.{u + 1, u, u + 1} J RB V b)
    change (r.hom.f n).val.app V (((TS.map (Prod.mkHom (𝟙 (E.obj P)) t)).f n).val.app V
      ((((μ a).complexIso P C).hom.f n).val.app V
        (scalarHomUnitSection (m T) a _ V
          (coefficientTensorGenerator.{u + 1, u + 1, u} J RA P C n 0 n
            (add_zero n) V x (ringedTensorUnitSection.{u + 1, u, u + 1} J RB V b))))) = _
    have hm := ScalarHomTensor.tensor_generator_map.{u + 1, u, u + 1}
      (J := J) (R := RB) (𝟙 (E.obj P)) t n 0 n (add_zero n) V
      (show ((E.obj P).X n).val.obj V from scalarHomUnitSection (m T) a (P.X n) V x)
      (show ((E.obj C).X 0).val.obj V from scalarHomUnitSection (m T) a (C.X 0) V
        (ringedTensorUnitSection.{u + 1, u, u + 1} J RB V b))
    dsimp only [E, scalarComplex] at hg ht hm hr ⊢
    erw [hg, hm, ht]
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply]
    erw [hr n (add_zero n) V b
      (show ((E.obj P).X n).val.obj V from scalarHomUnitSection (m T) a (P.X n) V x)]
    exact (ScalarOrdinaryEvaluation.normalizedNu_pure (ordinaryScalars m T) a
      P n V b x).symm
  change IsIso k
  have hi : IsIso ((coefficientTensorSingleComparison φ T P).inv ≫ k) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (coefficientTensorSingleComparison φ T P).inv k


set_option maxHeartbeats 2000000 in
-- Naturality compares dependent scalar-complex presentations before localization.
/-- The balanced chain adjunct is a quasi-isomorphism when the first complex is
K-flat and the second resolves the restricted coefficient tensor unit.
Source: Stacks Project, Tags 03EK, 07A4 and 07A6
(blueprint: lem-sp-open-scalar-balancing-chain).

Proof: tensoring a complex with the restricted coefficient unit identifies with
its degreewise ordinary coefficient tensor. The single-complex tensor comparison,
termwise restriction comparison and braiding give this identification; its inverse
sends b tensor x to the total generator x tensor b in bidegree (n,0). First take
the coefficient resolution map to be the identity. Evaluate the adjoint on these
generators: scalar unit followed by the transposed identity is the identity,
the normalized scalar tensor comparison preserves total generators, and the
right-unitor formula multiplies b into the scalar unit of x. This is precisely
the normalized ordinary balancing isomorphism. For a general resolution map g,
naturality of the scalar tensor comparison and the adjunction expresses the
adjunct as tensor(id,g) followed by that isomorphism. K-flatness of the first
complex makes tensor(id,g) a quasi-isomorphism, proving the assertion. -/
theorem scalar_balancing_chain_quasiIso
    (m : Models.{u}) (T : Scheme.{u})
    (μ : ∀ {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
      (a : R ⟶ S), ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2}
        (J := Scheme.ProEt.topology T) (m T) a)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (g : Q ⟶ ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (proEtaleConstantRingMap (T := T) φ)).mapHomologicalComplex (.up ℤ)).obj
        (ringedTensorUnitComplex.{u + 1, u, u + 1}
          (Scheme.ProEt.topology T) (proEtaleConstantRing T B))) (hg : QuasiIso g)
    (r : (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (proEtaleConstantRing T B)).obj
      ((scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
        (scalarPair m φ T).extension_additive).obj P,
        ringedTensorUnitComplex.{u + 1, u, u + 1}
          (Scheme.ProEt.topology T) (proEtaleConstantRing T B)) ≅
      (scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
        (scalarPair m φ T).extension_additive).obj P)
    (hr : ∀ (n : ℤ) (h : n + 0 = n) (V : T.ProEtᵒᵖ)
      (b : (proEtaleConstantRing T B).obj.obj V)
      (x : (((scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
        (scalarPair m φ T).extension_additive).obj P).X n).val.obj V),
      (r.hom.f n).val.app V
        (coefficientTensorGenerator.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
          (proEtaleConstantRing T B) _ _ n 0 n h V x
          (ringedTensorUnitSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            (proEtaleConstantRing T B) V b)) = b • x) :
    let a := proEtaleConstantRingMap (T := T) φ
    let E := scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
      (scalarPair m φ T).extension_additive
    let O := ringedTensorUnitComplex.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (proEtaleConstantRing T B)
    let adj := ((m T).scalar a).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)
    let t := (adj.homEquiv Q O).symm g
    QuasiIso ((adj.homEquiv _ _) (((μ a).complexIso P Q).hom ≫
      (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
        (proEtaleConstantRing T B)).map (Prod.mkHom (𝟙 (E.obj P)) t) ≫ r.hom)) := by
  let J := Scheme.ProEt.topology T
  let RA := proEtaleConstantRing T A
  let RB := proEtaleConstantRing T B
  let a := proEtaleConstantRingMap (T := T) φ
  let E := scalarComplex.{u + 1, u, u + 1}
    (scalarPair m φ T).extension (scalarPair m φ T).extension_additive
  let O := ringedTensorUnitComplex.{u + 1, u, u + 1} J RB
  let C := ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex
      (.up ℤ)).obj O
  let adj := ScalarHomTensor.chainAdj (J := J) (m T) a
  let t := (adj.homEquiv Q O).symm g
  let t₀ := (adj.homEquiv C O).symm (𝟙 C)
  let TS := coefficientTotalTensor.{u + 1, u + 1, u} J RB
  let TT := coefficientTotalTensor.{u + 1, u + 1, u} J RA
  let l := ((μ a).complexIso P Q).hom ≫ TS.map (Prod.mkHom (𝟙 (E.obj P)) t) ≫ r.hom
  let l₀ := ((μ a).complexIso P C).hom ≫ TS.map (Prod.mkHom (𝟙 (E.obj P)) t₀) ≫ r.hom
  have ht : E.map g ≫ t₀ = t := by
    dsimp only [t, t₀]
    rw [adj.homEquiv_counit, adj.homEquiv_counit, E.map_id, Category.id_comp]
  have hn := ScalarTensorRepresentative.complexIso_natural (J := J) (m T) μ a (𝟙 P) g
  erw [E.map_id] at hn
  have hl : l = E.map (TT.map (Prod.mkHom (𝟙 P) g)) ≫ l₀ := by
    dsimp only [l, l₀]
    erw [reassoc_of% hn, ← TS.map_comp_assoc]
    have hp : Prod.mkHom (𝟙 (E.obj P)) (E.map g) ≫
        Prod.mkHom (𝟙 (E.obj P)) t₀ = Prod.mkHom (𝟙 (E.obj P)) t := by
      apply Prod.ext
      · simp
      · exact ht
    rw [hp]
  change QuasiIso ((adj.homEquiv _ _) l)
  rw [hl, adj.homEquiv_naturality_left]
  have his : IsIso ((adj.homEquiv _ _) l₀) := scalar_balancing_base_isIso m T μ φ P r hr
  let := SheafOfModules.cochainModulesMonoidal RA
  let := SheafOfModules.cochainModulesSymmetric RA
  let := SheafOfModules.cochainModulesPreadditive RA
  let : MonoidalClosed (proEtaleRingModules T RA) :=
    RingedDerivedNative.moduleClosed.{u + 1, u, u + 1} J RA
  let := instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
    (proEtaleRingModules T RA)
  have hflat := (HomotopyCategory.kFlat_quotient_obj_iff P).1
    (RingedDerivedNative.kFlat.{u + 1, u, u + 1} J RA P hP)
  have hq : QuasiIso (TT.map (Prod.mkHom (𝟙 P) g)) := by
    have heq : TT.map (Prod.mkHom (𝟙 P) g) = P ◁ g := by
      dsimp only [TT, coefficientTotalTensor, Functor.uncurry_obj_map]
      erw [CategoryTheory.Functor.map_id]
      simp only [NatTrans.id_app, Category.id_comp]
      rfl
    rw [heq]
    exact hflat.1 g hg
  infer_instance

end AlgebraicGeometry.ProEtale.OpenScalarTensor
