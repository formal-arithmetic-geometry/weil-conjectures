/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.ExternalRHomConePairing
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # Lifted external evaluation chain models with a common shifted target

Source: Stacks Project, sites-cohomology.tex, Tags 0A90, 0A8X and 08J7;
agent refinement of the external RHom cone pairing, old proof steps 4 and 7
(blueprint: lem-pur-lifted-external-evaluation-chain-model).

The existing `ExternalRHom` interfaces express the ordinary module-valued sheaf
encoding, normalized Hom models, direct-sum tensor, and the canonical Koszul
interchange. This file adds no second realization, tensor, Hom, or evaluation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.Etale.ExternalRHom

variable (A : Type (u + 1)) [CommRing A]

private lemma sheaf_add_hom {X : Scheme.{u}} {M N : Modules A X}
    (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

private lemma sheaf_neg_hom {X : Scheme.{u}} {M N : Modules A X}
    (f : M ⟶ N) : (-f).hom = -f.hom := rfl

private lemma sheaf_smul_hom {X : Scheme.{u}} {M N : Modules A X}
    (a : A) (f : M ⟶ N) : (a • f).hom = a • f.hom := rfl

private lemma sheaf_sign_hom {X : Scheme.{u}} {M N : Modules A X}
    (a : ℤˣ) (f : M ⟶ N) : (a • f).hom = a • f.hom := by
  change (((a : ℤ) • f)).hom = (a : ℤ) • f.hom
  rfl

private noncomputable def tensorSheafifyIso (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (E : Modules A X) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj P ⊗ E ≅
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (P ⊗ E.obj) :=
  whiskerLeftIso _
      (asIso ((sheafificationAdjunction X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).counit.app E)).symm ≪≫
    Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) P E.obj

private lemma tensorSheafifyIso_unit (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (E : Modules A X) :
    (toSheafify X.smallEtaleTopology P ▷ E.obj) ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} A)) _ E ≫ (tensorSheafifyIso A X P E).hom.hom =
      toSheafify X.smallEtaleTopology (P ⊗ E.obj) := by
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let G := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
  have hu := NatTrans.IsMonoidal.tensor (τ := adj.unit) P E.obj
  simp only [Functor.LaxMonoidal.id_μ, Category.id_comp,
    Functor.LaxMonoidal.comp_μ] at hu
  change _ = adj.unit.app (P ⊗ E.obj)
  rw [hu]
  dsimp only [tensorSheafifyIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, asIso_inv, ObjectProperty.FullSubcategory.comp_hom]
  change (adj.unit.app P ▷ E.obj) ≫ Functor.LaxMonoidal.μ G _ E ≫
      G.map (_ ◁ inv (adj.counit.app E)) ≫ G.map (Functor.LaxMonoidal.μ L P E.obj) = _
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.map_inv, adj.inv_counit_map, MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

private lemma tensorSheafify_hom_ext (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (E I : Modules A X)
    (f g : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj P ⊗ E ⟶ I)
    (h : (toSheafify X.smallEtaleTopology P ▷ E.obj) ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} A)) _ E ≫ f.hom =
      (toSheafify X.smallEtaleTopology P ▷ E.obj) ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} A)) _ E ≫ g.hom) : f = g := by
  let e := tensorSheafifyIso A X P E
  apply (cancel_epi e.inv).1
  apply ((sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ I).injective
  change toSheafify X.smallEtaleTopology (P ⊗ E.obj) ≫ (e.inv ≫ f).hom =
    toSheafify X.smallEtaleTopology (P ⊗ E.obj) ≫ (e.inv ≫ g).hom
  rw [← tensorSheafifyIso_unit A X P E]
  simpa only [e, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.hom_inv_id_assoc] using h

private noncomputable def evaluationPresheaf (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (r q n : ℤ) (h : q + r = n) :
    (Functor.const X.Etaleᵒᵖ).obj (U.X r) ⊗ (E.X q).obj ⟶ (I.X n).obj where
  app W := ModuleCat.MonoidalCategory.tensorLift
    (fun w e ↦ (((((α.f r).hom w).v q n h).hom.app W) e))
    (by
      intro w w' e
      rw [map_add]
      change ((((((α.f r).hom w).v q n h) + (((α.f r).hom w').v q n h)).hom.app W) e) = _
      rw [sheaf_add_hom]
      rfl)
    (by
      intro a w e
      rw [map_smul]
      change (((a • (((α.f r).hom w).v q n h)).hom.app W) e) = _
      rw [sheaf_smul_hom]
      rfl)
    (by intros; simp)
    (by intros; simp)
  naturality {W W'} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro w e
    exact ConcreteCategory.congr_hom
      ((((α.f r).hom w).v q n h).hom.naturality f) e

private noncomputable def evaluationTerm (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (r q n : ℤ) (h : q + r = n) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      ((Functor.const X.Etaleᵒᵖ).obj (U.X r)) ⊗ E.X q ⟶ I.X n :=
  (tensorSheafifyIso A X ((Functor.const X.Etaleᵒᵖ).obj (U.X r)) (E.X q)).hom ≫
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
      _ (I.X n)).symm (evaluationPresheaf A X E I U α r q n h)

private lemma evaluationTerm_restrict (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (r q n : ℤ) (h : q + r = n) :
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (U.X r)) ▷
        (E.X q).obj) ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) _ (E.X q) ≫
      (evaluationTerm A X E I U α r q n h).hom =
      evaluationPresheaf A X E I U α r q n h := by
  let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let ev := evaluationPresheaf A X E I U α r q n h
  change (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (U.X r)) ▷
      (E.X q).obj) ≫ Functor.LaxMonoidal.μ
        (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ (E.X q) ≫
      ((tensorSheafifyIso A X _ (E.X q)).hom ≫ (adj.homEquiv _ (I.X n)).symm ev).hom = ev
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  calc
    _ = toSheafify X.smallEtaleTopology
        (((Functor.const X.Etaleᵒᵖ).obj (U.X r)) ⊗ (E.X q).obj) ≫
          ((adj.homEquiv _ (I.X n)).symm ev).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ ((adj.homEquiv _ (I.X n)).symm ev).hom)
        (tensorSheafifyIso_unit A X ((Functor.const X.Etaleᵒᵖ).obj (U.X r)) (E.X q))
    _ = ev := (adj.homEquiv _ (I.X n)).apply_symm_apply ev

private noncomputable def evaluationDegree (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (n : ℤ) : (((constantComplex A X).obj U) ⊗ E).X n ⟶ I.X n :=
  HomologicalComplex.mapBifunctorDesc (fun r q h ↦
    evaluationTerm A X E I U α r q n (by change r + q = n at h; omega))

private lemma evaluationDegree_ι (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (r q n : ℤ) (h : r + q = n) :
    HomologicalComplex.ιTensorObj ((constantComplex A X).obj U) E r q n h ≫
      evaluationDegree A X E I U α n =
      evaluationTerm A X E I U α r q n (by omega) := by
  exact HomologicalComplex.ι_mapBifunctorDesc _ r q h


private lemma evaluationTerm_section (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (r q n : ℤ) (h : q + r = n) (W : X.Etaleᵒᵖ) (w : U.X r)
    (e : (E.X q).obj.obj W) :
    ((evaluationTerm A X E I U α r q n h).hom.app W)
        (tensorSection A _ _ W (constantSection A X (U.X r) W w) e) =
      (((((α.f r).hom w).v q n h).hom.app W) e) := by
  dsimp only [homComplex] at α
  have h' := ConcreteCategory.congr_hom
    (NatTrans.congr_app (evaluationTerm_restrict A X E I U α r q n h) W)
    (TensorProduct.tmul A w e)
  exact h'

private lemma tensorSection_map {X : Scheme.{u}} {M N M' N' : Modules A X}
    (f : M ⟶ M') (g : N ⟶ N') (W : X.Etaleᵒᵖ)
    (m : M.obj.obj W) (n : N.obj.obj W) :
    (((f ⊗ₘ g).hom.app W) (tensorSection A M N W m n)) =
      tensorSection A M' N' W ((f.hom.app W) m) ((g.hom.app W) n) := by
  have h := NatTrans.congr_app
    (Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) f g) W
  exact (ConcreteCategory.congr_hom h (TensorProduct.tmul A m n)).symm

private lemma tensorSection_whiskerLeft {X : Scheme.{u}} {M N N' : Modules A X}
    (g : N ⟶ N') (W : X.Etaleᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) :
    (((M ◁ g).hom.app W) (tensorSection A M N W m n)) =
      tensorSection A M N' W m ((g.hom.app W) n) := by
  simpa only [id_tensorHom, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] using
    tensorSection_map A (𝟙 M) g W m n

private lemma tensorSection_whiskerRight {X : Scheme.{u}} {M M' N : Modules A X}
    (f : M ⟶ M') (W : X.Etaleᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) :
    (((f ▷ N).hom.app W) (tensorSection A M N W m n)) =
      tensorSection A M' N W ((f.hom.app W) m) n := by
  simpa only [tensorHom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] using
    tensorSection_map A f (𝟙 N) W m n

private lemma constantSection_map (X : Scheme.{u}) {M N : ModuleCat.{u + 1} A}
    (f : M ⟶ N) (W : X.Etaleᵒᵖ) (m : M) :
    ((((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map f).hom.app W)
        (constantSection A X M W m)) = constantSection A X N W (f m) := by
  have h := NatTrans.congr_app
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.naturality
      ((Functor.const X.Etaleᵒᵖ).map f)) W
  exact (ConcreteCategory.congr_hom h m).symm

private lemma evaluation_cochain_d (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (r q n m : ℤ) (h : q + r = n) (hnm : n + 1 = m)
    (W : X.Etaleᵒᵖ) (w : U.X r) (e : (E.X q).obj.obj W) :
    ((I.d n m).hom.app W) (((((α.f r).hom w).v q n h).hom.app W) e) =
      (((((α.f (r + 1)).hom ((U.d r (r + 1)).hom w)).v q m (by omega)).hom.app W) e) +
        r.negOnePow • (((((α.f r).hom w).v (q + 1) m (by omega)).hom.app W)
          (((E.d q (q + 1)).hom.app W) e)) := by
  dsimp only [homComplex] at α
  have hc := ConcreteCategory.congr_hom (α.comm r (r + 1)) w
  change CochainComplex.HomComplex.δ r (r + 1) ((α.f r).hom w) =
    (α.f (r + 1)).hom ((U.d r (r + 1)).hom w) at hc
  have hv := CochainComplex.HomComplex.Cochain.congr_v hc q m (by omega)
  rw [CochainComplex.HomComplex.δ_v r (r + 1) rfl _ q m
    (by omega) n (q + 1) (by omega) rfl] at hv
  have hs := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg InducedCategory.Hom.hom hv) W) e
  simp only [sheaf_add_hom, sheaf_neg_hom, ObjectProperty.FullSubcategory.comp_hom,
    sheaf_sign_hom, NatTrans.comp_app, NatTrans.app_neg, ModuleCat.hom_neg,
    LinearMap.neg_apply,
    NatTrans.app_add, NatTrans.app_units_zsmul, ModuleCat.hom_add, ModuleCat.hom_smul,
    ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Int.negOnePow_add, Int.negOnePow_one, mul_smul,
    Units.neg_smul, one_smul, smul_neg] at hs
  rw [← sub_eq_add_neg] at hs
  exact sub_eq_iff_eq_add.mp hs

private lemma evaluationTerm_d (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I)
    (r q n m : ℤ) (h : q + r = n) (hnm : n + 1 = m) :
    evaluationTerm A X E I U α r q n h ≫ I.d n m =
      ((constantComplex A X).obj U).d r (r + 1) ▷ E.X q ≫
          evaluationTerm A X E I U α (r + 1) q m (by omega) +
        r.negOnePow • (((constantComplex A X).obj U).X r ◁ E.d q (q + 1) ≫
          evaluationTerm A X E I U α r (q + 1) m (by omega)) := by
  dsimp only [homComplex] at α
  apply tensorSheafify_hom_ext A X
    ((Functor.const X.Etaleᵒᵖ).obj (U.X r)) (E.X q) (I.X m)
  apply NatTrans.ext
  funext W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro w e
  change ((evaluationTerm A X E I U α r q n h ≫ I.d n m).hom.app W)
      (tensorSection A _ _ W (constantSection A X (U.X r) W w) e) = _
  simp only [ObjectProperty.FullSubcategory.comp_hom, sheaf_add_hom, sheaf_sign_hom,
    NatTrans.comp_app,
    NatTrans.app_add, NatTrans.app_units_zsmul, ModuleCat.hom_add,
    ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  change ((I.d n m).hom.app W)
      (((evaluationTerm A X E I U α r q n h).hom.app W)
        (tensorSection A _ _ W (constantSection A X (U.X r) W w) e)) =
    ((evaluationTerm A X E I U α (r + 1) q m _).hom.app W)
      (((((constantComplex A X).obj U).d r (r + 1) ▷ E.X q).hom.app W)
        (tensorSection A _ _ W (constantSection A X (U.X r) W w) e)) +
      r.negOnePow • ((evaluationTerm A X E I U α r (q + 1) m _).hom.app W)
        (((((constantComplex A X).obj U).X r ◁ E.d q (q + 1)).hom.app W)
          (tensorSection A _ _ W (constantSection A X (U.X r) W w) e))
  rw [evaluationTerm_section, tensorSection_whiskerRight, tensorSection_whiskerLeft]
  change _ = ((evaluationTerm A X E I U α (r + 1) q m _).hom.app W)
      (tensorSection A _ _ W
        ((((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
          (U.d r (r + 1))).hom.app W) (constantSection A X (U.X r) W w)) e) + _
  rw [constantSection_map, evaluationTerm_section]
  change _ = _ + r.negOnePow • ((evaluationTerm A X E I U α r (q + 1) m _).hom.app W)
    (tensorSection A
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        ((Functor.const X.Etaleᵒᵖ).obj (U.X r))) (E.X (q + 1)) W
      (constantSection A X (U.X r) W w) (((E.d q (q + 1)).hom.app W) e))
  rw [evaluationTerm_section]
  exact evaluation_cochain_d A X E I U α r q n m h hnm W w e

private noncomputable def evaluationChain (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I) :
    ((constantComplex A X).obj U) ⊗ E ⟶ I where
  f n := evaluationDegree A X E I U α n
  comm' n m hnm := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro r q h
    change r + q = n at h
    change n + 1 = m at hnm
    change HomologicalComplex.ιTensorObj ((constantComplex A X).obj U) E r q n h ≫
        evaluationDegree A X E I U α n ≫ I.d n m =
      (HomologicalComplex.ιTensorObj ((constantComplex A X).obj U) E r q n h ≫
        (((constantComplex A X).obj U) ⊗ E).d n m) ≫
          evaluationDegree A X E I U α m
    rw [← Category.assoc, evaluationDegree_ι, evaluationTerm_d A X E I U α r q n m
      (by omega) hnm]
    rw [CochainComplex.ιTensorObj_d _ _ r q n m h hnm]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
      evaluationDegree_ι]

/-- The formula t(w tensor e) = alpha(w)(e) defines an ordinary chain map.
Source: Stacks 0A8X and 0A90
(blueprint: lem-pur-lifted-external-evaluation-chain-model).

Proof: evaluate each homogeneous cochain alpha(w) on local sections of E. This is
bilinear and compatible with restriction, so it descends to the sheaf tensor and
extends over the direct-sum totalization. Since alpha is a chain map, the Hom
identity d(alpha(w)) = alpha(dw) gives
 d_I(alpha(w)(e)) = alpha(dw)(e) + (-1)^|w| alpha(w)(d_E e),
which is exactly the tensor chain-map equation. -/
theorem lifted_external_evaluation_chain_evaluation
    (X : Scheme.{u}) (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (α : U ⟶ homComplex A E I) :
    ∃ t : chainEvaluationSource A X U E ⟶ I, IsChainEvaluation A E I U α t := by
  refine ⟨evaluationChain A X E I U α, ?_⟩
  intro r q W w e
  have hι := evaluationDegree_ι A X E I U α r q (q + r) (add_comm r q)
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg InducedCategory.Hom.hom hι) W)
    (tensorSection A _ _ W (constantSection A X (U.X r) W w) e)
  exact hv.trans (evaluationTerm_section A X E I U α r q (q + r) rfl W w e)

/-- Every lifted external evaluation represents the canonical derived transpose, and
its K-flat external target represents the derived external tensor.

Source: Stacks 0A90, 08J9, 07A2 and 0A96
(blueprint: lem-pur-lifted-external-evaluation-chain-model).

Proof: apply `lem-pur-global-hom-evaluation-flat-lift` on X and Y to identify the
normalized Hom complexes and evaluations. The given homotopies identify the localized
lifts with those evaluations. The tensor-pullback comparison preserves K-flatness and
flat terms; `lem-pur-kflat-total-tensor-model` identifies the ordinary external tensor
of N and M with the derived external tensor. Its comparison, together with the two
inverse quasi-isomorphisms, is `targetModel` with identity final map. For every
K-injective resolution i, postcompose this comparison with Q(i). Interchange the
second global Hom factor with the first coefficient factor; the cochain braiding gives
(-1)^(s*q). Compose the pulled-back lifts and i. Currying this honest chain map gives
p, since d_J p(x)(y) = p(dx)(y) + (-1)^|x| p(x)(dy). Apply the K-flat chain-transpose
normalization and resolving-derived-adjunction normalization to identify its
localization with `pairing`. The target Hom model follows from the same global Hom
lemma on P. This construction works for every representative, homotopy lift and i;
`HasChainNormalization` quantifies over them all and identifies every result with the
same `pairing`, which has no such choices. -/
theorem lifted_external_evaluation_chain_model
    {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y)
    (I : Complexes A X) (I' : Complexes A Y) [I.IsKInjective] [I'.IsKInjective]
    (hE : IsBoundedFlat A E) (hH : IsBoundedFlat A H)
    (hK : IsPlus A ((siteQ A X).obj I)) (hL : IsPlus A ((siteQ A Y).obj I'))
    (hF : IsPlus A (external A a b ((siteQ A X).obj I) ((siteQ A Y).obj I'))) :
    Nonempty (HomModel A E I) ∧ Nonempty (HomModel A H I') ∧
    HasChainNormalization A a b E H I I' ∧
    ∀ (N : Complexes A X) (M : Complexes A Y)
      (c : N ⟶ I) (c' : M ⟶ I') [QuasiIso c] [QuasiIso c'],
      CochainComplex.IsKFlatIndependentCoefficients
        (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
        ((ringedComplex A X).obj N) →
      CochainComplex.IsKFlatIndependentCoefficients
        (J := Y.smallEtaleTopology) (R := realizationRing Y.smallEtaleTopology A)
        ((ringedComplex A Y).obj M) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite
        (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
        ((ringedRealization A X).obj (N.X n))) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite
        (J := Y.smallEtaleTopology) (R := realizationRing Y.smallEtaleTopology A)
        ((ringedRealization A Y).obj (M.X n))) →
      IsIso (targetModel A a b N I M I' (externalComplex A a b N M) c c' (𝟙 _)) ∧
      ∀ (J : Complexes A P) (i : externalComplex A a b N M ⟶ J)
        [QuasiIso i] [J.IsKInjective],
        IsIso (targetModel A a b N I M I' J c c' i) ∧
        Nonempty (HomModel A (externalComplex A a b E H) J) := by
  sorry

/-- The source total tensor of the two given flat-term K-flat coefficient complexes
represents the derived tensor of their localized objects, by the canonical comparison.
Source: Stacks 07A2 and 07A4
(blueprint: lem-pur-lifted-external-evaluation-chain-model).

Proof: apply the total K-flat tensor model to U,V realized as modules on the one-point
site. The canonical exact tensor realization identifies this with their ordinary
A-module total tensor. The localization tensor constraint is the counit comparison
on K-flat representatives, so it is an isomorphism. Composing with the two
quasi-isomorphisms alpha,gamma and their normalized Hom models gives precisely the
source identification used in the lifted external normalization equation. -/
theorem lifted_external_evaluation_source_model
    (U V : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hU : CochainComplex.IsKFlatIndependentCoefficients
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointComplex A).obj U))
    (hV : CochainComplex.IsKFlatIndependentCoefficients
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointComplex A).obj V))
    (hUf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointRealization A).obj (U.X n)))
    (hVf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointRealization A).obj (V.X n))) :
    IsIso (Functor.LaxMonoidal.μ (moduleQ A) U V) := by
  sorry

/-- The signed first-variable Hom shift on every K-injective cochain target, including
unbounded source complexes. Its component normalization is Mathlib's `leftUnshift`:
for a shift by one it is exactly (-1)^n f^(p-1).

Source: Stacks 0A8X and 08J7
(blueprint: lem-pur-lifted-external-evaluation-chain-model).

Proof: the degree-n component has degree n-1 in the unshifted Hom complex. Expand the
Hom and shift differentials. Both composites on B^p are
(-1)^(n+1) d_I f^(p-1) - f^p d_B. The inverse sends g to the family
f^q = (-1)^n g^(q+1), giving both inverse identities componentwise. Restriction
commutes with this formula. Thus the global and sheaf Hom maps are chain
isomorphisms. Computing derived Hom with the same K-injective I identifies their
localizations with the first-variable derived Hom shift, without boundedness of B. -/
theorem lifted_external_evaluation_hom_shift
    (X : Scheme.{u}) (B I : Complexes A X) [I.IsKInjective] :
    ∃ θ : homComplex A (B⟦(1 : ℤ)⟧) I ≅ (homComplex A B I)⟦(-1 : ℤ)⟧,
      ∀ (n : ℤ) (f : (homComplex A (B⟦(1 : ℤ)⟧) I).X n),
        ((homComplex A B I).shiftFunctorObjXIso (-1) n (n + -1) rfl).hom
          (θ.hom.f n f) = f.leftUnshift (n + -1) (by omega) := by
  classical
  let e (n : ℤ) : (homComplex A (B⟦(1 : ℤ)⟧) I).X n ≅
      ((homComplex A B I)⟦(-1 : ℤ)⟧).X n :=
    ((CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv A B I
      (n + -1) 1 n (by omega)).symm.toModuleIso) ≪≫
      ((homComplex A B I).shiftFunctorObjXIso (-1) n (n + -1) rfl).symm
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_, ?_⟩
  · intro n m h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (-1 : ℤ).negOnePow •
        CochainComplex.HomComplex.δ (n + -1) (m + -1)
          (f.leftUnshift (n + -1) (by omega)) =
      (CochainComplex.HomComplex.δ n m f).leftUnshift (m + -1) (by omega)
    rw [CochainComplex.HomComplex.Cochain.δ_leftUnshift f
      (n + -1) (by omega) (m + -1) m (by omega)]
    simp
  · intro n f
    rfl

/-- Simultaneously shifting the Hom resolution down and its coefficient up preserves
chain evaluation, with the sign (-1)^r, and preserves its given homotopy factorization
through exactly the same N and c. The theorem applies on X and on Y, so their external
tensor T, and any chosen K-injective resolution i : T to J, remain the same.

Source: Stacks 0A8X, 08J7 and the elementary shift calculation
(blueprint: lem-pur-lifted-external-evaluation-chain-model).

Proof: use the signed Hom isomorphism of the previous clause. On the tensor summand
U[-1]^r tensor E[1]^q define eta by (-1)^r times the identifications with
U^(r-1) tensor E^(q+1). The source differential followed by eta is
(-1)^r dw tensor e - w tensor de, the same as d eta. The same formula is its inverse.
The shifted alpha is alpha[-1] followed by theta inverse. It evaluates w on e as
(-1)^r alpha(w)(e), so its evaluation is t eta. Shifting preserves quasi-isomorphisms,
flat terms and K-flatness. Precompose the original homotopy with eta to obtain the
homotopy from (u eta)c to t eta. No change to N or c occurs; applying this on either
or both sites therefore leaves T and its resolution i unchanged. -/
theorem lifted_external_evaluation_shifted_lift
    (X : Scheme.{u}) (E I : Complexes A X) [I.IsKInjective]
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (α : U ⟶ homComplex A E I) [QuasiIso α]
    (t : chainEvaluationSource A X U E ⟶ I) (ht : IsChainEvaluation A E I U α t)
    (N : Complexes A X) (c : N ⟶ I)
    (u : chainEvaluationSource A X U E ⟶ N) (hu : Nonempty (Homotopy (u ≫ c) t)) :
    ∃ (θ : homComplex A (E⟦(1 : ℤ)⟧) I ≅ (homComplex A E I)⟦(-1 : ℤ)⟧)
      (η : chainEvaluationSource A X (U⟦(-1 : ℤ)⟧) (E⟦(1 : ℤ)⟧) ≅
        chainEvaluationSource A X U E),
      (∀ (n : ℤ) (f : (homComplex A (E⟦(1 : ℤ)⟧) I).X n),
        ((homComplex A E I).shiftFunctorObjXIso (-1) n (n + -1) rfl).hom
          (θ.hom.f n f) = f.leftUnshift (n + -1) (by omega)) ∧
      (∀ (r q : ℤ) (W : X.Etaleᵒᵖ)
        (w : (U⟦(-1 : ℤ)⟧).X r) (e : ((E⟦(1 : ℤ)⟧).X q).obj.obj W),
        ((η.hom.f (r + q)).hom.app W)
          (tensorComplexSection A ((constantComplex A X).obj (U⟦(-1 : ℤ)⟧))
            (E⟦(1 : ℤ)⟧) r q (r + q) rfl W
            (constantSection A X ((U⟦(-1 : ℤ)⟧).X r) W w) e) =
        r.negOnePow • tensorComplexSection A ((constantComplex A X).obj U) E
          (r + -1) (q + 1) (r + q) (by omega) W
          (constantSection A X (U.X (r + -1)) W
            ((U.shiftFunctorObjXIso (-1) r (r + -1) rfl).hom w))
          (((E.shiftFunctorObjXIso 1 q (q + 1) rfl).hom.hom.app W) e)) ∧
      (CochainComplex.IsKFlatIndependentCoefficients
        (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
        (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
        ((pointComplex A).obj U) →
        CochainComplex.IsKFlatIndependentCoefficients
          (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
          (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
          ((pointComplex A).obj (U⟦(-1 : ℤ)⟧))) ∧
      ((∀ n : ℤ, SheafOfModules.IsFlatOnSite
        (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
        (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
        ((pointRealization A).obj (U.X n))) →
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite
          (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
          (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
          ((pointRealization A).obj ((U⟦(-1 : ℤ)⟧).X n))) ∧
      (IsBoundedFlat A E → IsBoundedFlat A (E⟦(1 : ℤ)⟧)) ∧
      QuasiIso (α⟦(-1 : ℤ)⟧' ≫ θ.inv) ∧
      IsChainEvaluation A (E⟦(1 : ℤ)⟧) I (U⟦(-1 : ℤ)⟧)
        (α⟦(-1 : ℤ)⟧' ≫ θ.inv) (η.hom ≫ t) ∧
      Nonempty (Homotopy ((η.hom ≫ u) ≫ c) (η.hom ≫ t)) := by
  sorry

/-- The chain Hom shift realizes the derived first-variable Hom shift under the
canonical evaluation-normalized Hom models, naturally in the coefficient target.
Source: Stacks 0A8X, 08J7 and 08JC
(blueprint: lem-pur-lifted-external-evaluation-chain-model).

Proof: use the signed component isomorphism above on each K-injective representative.
Its compatibility with every chain evaluation follows by substitution in the formula
for the transpose. Evaluation normalization of Hom models therefore identifies its
localization with the derived first-variable shift. Componentwise pre- and
post-composition commute with the signed index change, so the resulting comparison
is natural in the source and every target morphism. Localization and the universal
property of K-injective replacements descend this comparison to derived objects,
yielding the shift-commuting functor structures with the displayed normalization. -/
theorem lifted_external_evaluation_derived_hom_shift :
    ∃ S : ∀ (X : Scheme.{u}) (K : DerivedCategoryModule A X),
      (homFirst A X K).CommShift ℤ,
      HasSignedHomShift (homShift := S) A ∧
      ∀ (X : Scheme.{u}) (B I : Complexes A X) [I.IsKInjective],
        ∃ (m : HomModel A B I) (m' : HomModel A (B⟦(1 : ℤ)⟧) I)
          (θ : homComplex A (B⟦(1 : ℤ)⟧) I ≅ (homComplex A B I)⟦(-1 : ℤ)⟧),
          (∀ (n : ℤ) (f : (homComplex A (B⟦(1 : ℤ)⟧) I).X n),
            ((homComplex A B I).shiftFunctorObjXIso (-1) n (n + -1) rfl).hom
              (θ.hom.f n f) = f.leftUnshift (n + -1) (by omega)) ∧
          m'.iso.hom ≫
              homMap A ((((siteQ A X).commShiftIso (1 : ℤ)).app B).inv) (𝟙 _) ≫
              (@negativeHomShiftIsoOf
                (DerivedCategoryModule A X) inferInstance inferInstance
                (DerivedCategory (ModuleCat.{u + 1} A)) inferInstance inferInstance
                (homFirst A X ((siteQ A X).obj I)) (S X ((siteQ A X).obj I))
                ((siteQ A X).obj B)).hom =
            (moduleQ A).map θ.hom ≫
              (((moduleQ A).commShiftIso (-1 : ℤ)).app (homComplex A B I)).hom ≫
              m.iso.hom⟦(-1 : ℤ)⟧' := by
  sorry

end AlgebraicGeometry.Etale.ExternalRHom
