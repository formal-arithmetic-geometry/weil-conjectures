/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q45 and M9
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.ProEtaleScalarMateIdentifications
public import Sheaf.SecSmoothPurity.DirectImageScalarOperations
public import Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Sheaf.Paper.PulledReductionNormalizationComparison

/-! # Unbounded coefficient comparison on flat-term K-flat pullback models

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 06YT, 06YY, 0G7D;
sites-modules.tex, Tag 03EL; blueprint thm-exc-explicit-preservation, proof paragraph 2.
(blueprint: lem-exc-unbounded-coefficient-pullback-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private def liftLinearHom
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (a : R ⟶ S)
    (M N : SheafOfModules.{u + 1} S)
    (h : (SheafOfModules.restrictScalars a).obj M ⟶
      (SheafOfModules.restrictScalars a).obj N)
    (hb : ∀ W (b : S.obj.obj W) (x : M.val.obj W),
      h.val.app W (b • x) = b • (show N.val.obj W from h.val.app W x)) : M ⟶ N where
  val := {
    app := fun W ↦ ModuleCat.ofHom {
      toFun := h.val.app W
      map_add' := by intros; apply map_add
      map_smul' := hb W }
    naturality := by
      intro U W a
      ext x
      exact PresheafOfModules.naturality_apply h.val a x }

private def balancingIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (t : scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V) :
    (proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
      proEtaleConstantRingPullback B f) ⋙ scalarMateRestriction φ V ≅
    (proEtaleConstantRingPullback A f ⋙
      proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ)) ⋙
        scalarMateRestriction φ V :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ))
      (scalarBalancingBeta φ f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarMateOrdinaryTensorIso φ X) _ ≪≫ t ≪≫
    Functor.isoWhiskerLeft _ (scalarMateOrdinaryTensorIso φ V).symm ≪≫
    (Functor.associator _ _ _).symm

private theorem balancingLift
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (t : scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V)
    (hb : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : V.ProEtᵒᵖ)
      (b : (proEtaleConstantRing V B).obj.obj W)
      (x : ((proEtaleConstantRingPullback B f).obj
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M)).val.obj W),
      (scalarBalancingMap φ f t M).val.app W (b • x) =
        b • (show ((proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ)).obj
          ((proEtaleConstantRingPullback A f).obj M)).val.obj W from
            (scalarBalancingMap φ f t M).val.app W x)) :
    ∃ s : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
        proEtaleConstantRingPullback B f ≅
      proEtaleConstantRingPullback A f ⋙
        proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ),
      ∀ M, (scalarMateRestriction φ V).map (s.hom.app M) =
        scalarBalancingMap φ f t M := by
  let e := balancingIso φ f t
  let h : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
        proEtaleConstantRingPullback B f ⟶
      proEtaleConstantRingPullback A f ⋙
        proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ) :=
    { app := fun M ↦ liftLinearHom _ _ _ (scalarBalancingMap φ f t M) (hb M)
      naturality := by
        intro M N a
        ext W x
        exact congrArg (fun k ↦ k.val.app W x) (e.hom.naturality a) }
  have hh (M) : (scalarMateRestriction φ V).map (h.app M) = e.hom.app M := by
    ext W x
    rfl
  have hr : (scalarMateRestriction φ V).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (proEtaleConstantRingMap (T := V) φ)).2.2
  have hi (M) : IsIso (h.app M) := by
    have : IsIso ((scalarMateRestriction φ V).map (h.app M)) := by
      rw [hh]
      infer_instance
    exact isIso_of_reflects_iso _ (scalarMateRestriction φ V)
  have : IsIso h := NatIso.isIso_of_isIso_app h
  refine ⟨asIso h, ?_⟩
  intro M
  simpa only [asIso_hom, e, balancingIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, scalarBalancingMap, Iso.symm_hom,
            Functor.associator_hom_app, Functor.associator_inv_app,
            Category.id_comp, Category.comp_id, Category.assoc] using hh M

private theorem tensorIso_section
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
    (b : (proEtaleConstantRing X B).obj.obj U) (x : M.val.obj U) :
    ((scalarMateOrdinaryTensorIso φ X).hom.app M).val.app U
      (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M U b x) =
        proEtaleTensorPair X (proEtaleConstantRing X A) M
          (scalarMateCoefficient φ X) U x b := by
  have h := (scalarMateOrdinaryTensorIso_existsUnique φ X).exists.choose_spec M U b x
  with_unfolding_all exact h

private theorem balancingLift_one
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (t : scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V)
    (ht : IsScalarBalancing φ f t)
    (hβ : ∀ (N : proEtaleRingModules X (proEtaleConstantRing X B)) (U : X.ProEt)
      (x : N.val.obj (Opposite.op U)),
      ((scalarBalancingBeta φ f).inv.app N).val.app
          (Opposite.op ((proEtaleBaseChange f).obj U))
          (((proEtaleConstantRingAdjunction A f).unit.app
            ((scalarMateRestriction φ X).obj N)).val.app (Opposite.op U) x) =
        ((proEtaleConstantRingAdjunction B f).unit.app N).val.app (Opposite.op U) x)
    (s : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
        proEtaleConstantRingPullback B f ≅
      proEtaleConstantRingPullback A f ⋙
        proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ))
    (hs : ∀ M, (scalarMateRestriction φ V).map (s.hom.app M) =
      scalarBalancingMap φ f t M)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) :
    (s.hom.app M).val.app ((proEtaleBaseChange f).op.obj U)
      (((proEtaleConstantRingAdjunction B f).unit.app
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M)).val.app U
          (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M U 1 x)) =
      reductionTensorSection V (proEtaleConstantRingMap (T := V) φ)
        ((proEtaleConstantRingPullback A f).obj M) ((proEtaleBaseChange f).op.obj U) 1
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app U x) := by
  let N := (proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj M
  let z := reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M U 1 x
  let W := (proEtaleBaseChange f).op.obj U
  let v := (scalarMateOrdinaryTensorIso φ V).app
    ((proEtaleConstantRingPullback A f).obj M)
  apply (Iso.toLinearEquiv ((SheafOfModules.evaluation _ W).mapIso v)).injective
  have he := congrArg (fun a ↦ a ≫ v.hom) (hs M)
  dsimp only [v] at he
  simp only [scalarBalancingMap, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app,
    ] at he
  have he' := congrArg (fun a ↦ a.val.app W
    (((proEtaleConstantRingAdjunction B f).unit.app N).val.app U z)) he
  have hβ' := hβ N U.unop z
  have hinv := congrArg (fun a ↦ a.val.app W
    (((proEtaleConstantRingAdjunction A f).unit.app
      ((scalarMateRestriction φ X).obj N)).val.app U z))
    ((scalarBalancingBeta φ f).inv_hom_id_app N)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at hinv
  erw [hβ'] at hinv
  have hn := congrArg (fun a ↦ a.val.app U z)
    ((proEtaleConstantRingAdjunction A f).unit.naturality
      ((scalarMateOrdinaryTensorIso φ X).hom.app M)).symm
  change ((proEtaleConstantRingPullback A f).map
      ((scalarMateOrdinaryTensorIso φ X).hom.app M)).val.app W
      (((proEtaleConstantRingAdjunction A f).unit.app
        ((scalarMateRestriction φ X).obj N)).val.app U z) =
    ((proEtaleConstantRingAdjunction A f).unit.app
      ((scalarMateOrdinaryTensor φ X).obj M)).val.app U
      (((scalarMateOrdinaryTensorIso φ X).hom.app M).val.app U z) at hn
  dsimp only [z] at hn
  rw [tensorIso_section] at hn
  have ht' := ht M U.unop x 1
  simp only [map_one] at ht'
  change v.hom.val.app W ((s.hom.app M).val.app W
    (((proEtaleConstantRingAdjunction B f).unit.app N).val.app U z)) = _
  change v.hom.val.app W ((s.hom.app M).val.app W
    (((proEtaleConstantRingAdjunction B f).unit.app N).val.app U z)) =
    (t.hom.app M).val.app W
      (((proEtaleConstantRingPullback A f).map
        ((scalarMateOrdinaryTensorIso φ X).hom.app M)).val.app W
        (((scalarBalancingBeta φ f).hom.app N).val.app W
          (((proEtaleConstantRingAdjunction B f).unit.app N).val.app U z))) at he'
  rw [he', hinv, hn]
  exact ht'.trans (tensorIso_section φ V _ W 1 _).symm

private theorem balancingLift_eq_mate
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (t : scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V)
    (ht : IsScalarBalancing φ f t)
    (hβ : ∀ (N : proEtaleRingModules X (proEtaleConstantRing X B)) (U : X.ProEt)
      (x : N.val.obj (Opposite.op U)),
      ((scalarBalancingBeta φ f).inv.app N).val.app
          (Opposite.op ((proEtaleBaseChange f).obj U))
          (((proEtaleConstantRingAdjunction A f).unit.app
            ((scalarMateRestriction φ X).obj N)).val.app (Opposite.op U) x) =
        ((proEtaleConstantRingAdjunction B f).unit.app N).val.app (Opposite.op U) x)
    (s : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
        proEtaleConstantRingPullback B f ≅
      proEtaleConstantRingPullback A f ⋙
        proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ))
    (hs : ∀ M, (scalarMateRestriction φ V).map (s.hom.app M) =
      scalarBalancingMap φ f t M) :
    s = (PulledNormalization.ordinaryMate f
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRing V A) (proEtaleConstantRing V B)
      (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift φ))).symm).symm := by
  let m := PulledNormalization.ordinaryMate f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing V A) (proEtaleConstantRing V B)
    (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (m.hom.app M)).1
  change m.hom.app M ≫ s.hom.app M = m.hom.app M ≫ m.inv.app M
  rw [Iso.hom_inv_id_app]
  apply ((pbcScalarAdjunction (proEtaleConstantRingMap (T := V) φ)).homEquiv _ _).injective
  apply ((proEtaleConstantRingAdjunction A f).homEquiv _ _).injective
  ext U x
  simp only [Adjunction.homEquiv_unit]
  change (s.hom.app M).val.app ((proEtaleBaseChange f).op.obj U)
      ((m.hom.app M).val.app ((proEtaleBaseChange f).op.obj U)
        (((pbcScalarAdjunction (proEtaleConstantRingMap (T := V) φ)).unit.app
          ((proEtaleConstantRingPullback A f).obj M)).val.app
            ((proEtaleBaseChange f).op.obj U)
            (((proEtaleConstantRingAdjunction A f).unit.app M).val.app U x))) =
    ((pbcScalarAdjunction (proEtaleConstantRingMap (T := V) φ)).unit.app
      ((proEtaleConstantRingPullback A f).obj M)).val.app
        ((proEtaleBaseChange f).op.obj U)
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app U x)
  rw [PulledNormalization.scalar_unit_formula]
  rw [PulledNormalization.ordinaryMate_one]
  exact balancingLift_one φ f t ht hβ s hs M U x

/-- Compute coefficient extension after exact pullback using a supplied representative.
This is the pullback factorization followed by the existing universal scalar counit.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excPullbackThenCoefficientComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (directImageScalarExtension φ V).map
    ((proEtaleConstantRingDerivedPullback A f).map i.inv ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
    reductionScalarComplexCounit V (proEtaleConstantRingMap (T := V) φ)
      (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)

/-- Compute pullback after coefficient extension using the same representative.
This applies exact B-pullback to the existing scalar counit, then its factorization.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excCoefficientThenPullbackComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (proEtaleConstantRingDerivedPullback B f).map
    ((directImageScalarExtension φ X).map i.inv ≫
      reductionScalarComplexCounit X (proEtaleConstantRingMap (T := X) φ) P) ≫
    (proEtaleConstantRingPullback B f).mapDerivedCategoryFactors.hom.app
      (((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
        (.up ℤ)).obj P)

/-- The canonical B-linear coefficient comparison, computed on every flat-term K-flat
model, for arbitrary unbounded derived objects and arbitrary finite-ring homomorphisms.
The A-linear normalization uses the published pure-tensor predicate; the equality
with scalarBalancingMap retains the B-action before passing to complexes.
Source: Stacks 0G7E, 06YT, 06YY, 0G7D, 03EL
(blueprint: lem-exc-unbounded-coefficient-pullback-model).

Proof:
Lift the B-linear map supplied by the scalar balancing chain to a natural isomorphism s.
Its inverse gives T degreewise. The two adjunction bijections and the unit tensor formula
identify this inverse with the ordinary coefficient/pullback mate. The general derived
mate comparison computes the canonical derived mate on every cochain representative,
using the published scalar counits and exact-pullback factorization. Naturality along
the supplied isomorphism [P] ≅ K gives the displayed computation equation.
The ringed-topos K-flat pullback theorem supplies flatness and K-flatness of the pulled
model; exactness preserves quasi-isomorphisms. The scalar counits on these K-flat models
are invertible, so both named computation morphisms are isomorphisms. This proof uses
the supplied model and the existing derived comparison, without a new localization. -/
theorem unboundedCoefficientPullbackModel
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X) :
    ∃ t : scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
        proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V,
      IsScalarBalancing φ f t ∧
      ∃ s : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
          proEtaleConstantRingPullback B f ≅
        proEtaleConstantRingPullback A f ⋙
          proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ),
        (∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
          (scalarMateRestriction φ V).map (s.hom.app M) = scalarBalancingMap φ f t M) ∧
        ∃ T : (proEtaleConstantRingPullback A f ⋙
              proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ)).mapHomologicalComplex
                (.up ℤ) ≅
            (proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
              proEtaleConstantRingPullback B f).mapHomologicalComplex (.up ℤ),
          (∀ (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
            (n : ℤ), (T.hom.app P).f n = s.inv.app (P.X n) ∧
              (T.inv.app P).f n = s.hom.app (P.X n)) ∧
          (∀ P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ,
            CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing X A) P →
            (∀ n : ℤ, SheafOfModules.IsFlatOnSite
              (J := ProEt.topology X) (R := proEtaleConstantRing X A) (P.X n)) →
            CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing V A)
                (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P) ∧
            (∀ n : ℤ, SheafOfModules.IsFlatOnSite
              (J := ProEt.topology V) (R := proEtaleConstantRing V A)
              ((((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P).X n)) ∧
            (∀ (G : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
              (q : P ⟶ G), QuasiIso q →
                QuasiIso (((proEtaleConstantRingPullback A f).mapHomologicalComplex
                  (.up ℤ)).map q)) ∧
            ∀ (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K),
              IsIso (excPullbackThenCoefficientComputation φ f P K i) ∧
              IsIso (excCoefficientThenPullbackComputation φ f P K i) ∧
              (directImageScalarPullbackIso φ f).inv.app K ≫
                  excCoefficientThenPullbackComputation φ f P K i =
                excPullbackThenCoefficientComputation φ f P K i ≫
                  DerivedCategory.Q.map (T.hom.app P)) := by
  obtain ⟨_, hβ, t, ht, _, hb, _⟩ := proEtaleScalarBalancingChain φ f
  obtain ⟨s, hs⟩ := balancingLift φ f t hb
  let T := NatIso.mapHomologicalComplex s.symm (.up ℤ)
  refine ⟨t, ht, s, hs, T, ?_, ?_⟩
  · intro P n
    exact ⟨rfl, rfl⟩
  · intro P hp hf
    obtain ⟨hpf, hff⟩ := PulledNormalization.pullback_good f
      (proEtaleConstantRing X A) (proEtaleConstantRing V A)
      (proEtaleConstantRingComparison f A) P hp hf
    refine ⟨hpf, hff, ?_, ?_⟩
    · intro G q hq
      have : QuasiIso q := hq
      infer_instance
    · intro K i
      have hcX := scalarCounit_isIso X
        (proEtaleConstantRingMap (T := X) φ) P hp
      have hcV := scalarCounit_isIso V
        (proEtaleConstantRingMap (T := V) φ)
        (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P) hpf
      refine ⟨?_, ?_, ?_⟩
      · unfold excPullbackThenCoefficientComputation
        infer_instance
      · unfold excCoefficientThenPullbackComputation
        infer_instance
      · have he := balancingLift_eq_mate φ f t ht hβ s hs
        have hm := PulledNormalization.derivedMate_rep f
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRing V A) (proEtaleConstantRing V B)
          (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm P
        have hT : T.hom.app P = (NatIso.mapHomologicalComplex
            (PulledNormalization.ordinaryMate f
              (proEtaleConstantRing X A) (proEtaleConstantRing X B)
              (proEtaleConstantRing V A) (proEtaleConstantRing V B)
              (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
              (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
              (proEtaleConstantInverseImageMap_naturality f
                (CommRingCat.ofHom (RingHom.ulift φ))).symm) (.up ℤ)).hom.app P := by
          simp only [T, he]
          rfl
        rw [hT]
        simp only [excCoefficientThenPullbackComputation,
          excPullbackThenCoefficientComputation, Functor.map_comp, Category.assoc]
        have hn := ((directImageScalarPullbackIso φ f).inv.naturality i.inv).symm
        change (directImageScalarPullbackIso φ f).inv.app K ≫
            (proEtaleConstantRingDerivedPullback B f).map
              ((directImageScalarExtension φ X).map i.inv) =
          (directImageScalarExtension φ V).map
            ((proEtaleConstantRingDerivedPullback A f).map i.inv) ≫
              (directImageScalarPullbackIso φ f).inv.app (DerivedCategory.Q.obj P) at hn
        rw [reassoc_of% hn]
        exact congrArg (fun z ↦ (directImageScalarExtension φ V).map
          ((proEtaleConstantRingDerivedPullback A f).map i.inv) ≫ z) hm

end AlgebraicGeometry.ProEtale
