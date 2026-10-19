/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.Paper.RefinementCoefficientRealization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The ambient pro-etale closed-support triangle for a finite ring

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-localization,
order 1866 (blueprint: lem-exc-proetale-support-triangle).

The categories are the recorded left-module categories over the sheafified
continuous-function coefficient rings. No commutativity is assumed. The exact
closed direct image and open inverse image are specified by their termwise
localization isomorphisms. These characterize their descents uniquely up to natural
isomorphism. Their right adjoints are therefore the ordinary ambient exceptional
inverse image and derived open direct image. The triangle uses their counit and unit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

/-- Sectionwise direct image sends the zero module map to the zero map.
This supplies the structural zero-map data for its termwise complex functor.
Source: blueprint lem-exc-proetale-support-triangle, proof steps 2 and 6
(blueprint: lem-exc-proetale-support-triangle). -/
instance closedSupportPushforward_preservesZeroMorphisms
    {S T : Scheme.{u}} (f : S ⟶ T) (A : Type (u + 1)) [Ring A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    (SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange f)
      (J := Scheme.ProEt.topology T) (K := Scheme.ProEt.topology S)
      (finiteCoefficientDirectImageMap f A)).PreservesZeroMorphisms where
  map_zero _ _ := rfl


section

open Opposite

universe uC vC

private noncomputable def constantModuleDiagram {C : Type uC} [Category.{vC} C]
    (A : Type (u + 1)) [Ring A] :
    PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{u + 1} A) where
  obj M :=
    { obj W := M.obj W
      map f := ModuleCat.ofHom (M.map f).hom
      map_id W := by ext x; exact ConcreteCategory.congr_hom (M.map_id W) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (M.map_comp f g) x }
  map f :=
    { app W := f.app W
      naturality W W' a := by
        ext x
        exact ConcreteCategory.congr_hom (f.naturality a) x }
  map_id M := by ext W x; rfl
  map_comp f g := by ext W x; rfl

private noncomputable def finiteCoefficientRestriction (T : Scheme.{u}) (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    FiniteCoefficientModules T A ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) where
  obj M :=
    ⟨(constantModuleDiagram A).obj
        ((PresheafOfModules.restrictScalars (finiteCoefficientScalarMap T A)).obj M.val),
      Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := ⟨(constantModuleDiagram A).map
    ((PresheafOfModules.restrictScalars (finiteCoefficientScalarMap T A)).map f.val)⟩
  map_id M := by ext W x; rfl
  map_comp f g := by ext W x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteCoefficientRealizationAdjunction (T : Scheme.{u})
    (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    finiteCoefficientRealization T A ⊣ finiteCoefficientRestriction T A :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        (PresheafOfModules.sheafificationHomEquiv.{u + 1} (finiteCoefficientScalarMap T A)).trans
          { toFun f := ⟨(constantModuleDiagram A).map f⟩
            invFun f :=
              { app W := f.hom.app W
                naturality a := f.hom.naturality a }
            left_inv f := rfl
            right_inv f := rfl }
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        change (PresheafOfModules.sheafificationHomEquiv.{u + 1}
          (finiteCoefficientScalarMap T A)).symm _ = _
        apply ((PresheafOfModules.sheafificationAdjunction.{u + 1}
          (finiteCoefficientScalarMap T A)).homEquiv _ _).injective
        rw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
          Equiv.apply_symm_apply]
        change _ = (PresheafOfModules.sheafificationAdjunction.{u + 1}
          (finiteCoefficientScalarMap T A)).homEquiv _ _
            ((PresheafOfModules.sheafification.{u + 1} (finiteCoefficientScalarMap T A)).map
              ((finiteCoefficientModulePresheaf T.ProEt A).map f.hom) ≫ _)
        rw [Adjunction.homEquiv_naturality_left,
          PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
        simp only [Equiv.symm_trans_apply]
        erw [Equiv.apply_symm_apply]
        rfl
      homEquiv_naturality_right := by
        intro M N N' f g
        apply Sheaf.hom_ext
        change (constantModuleDiagram A).map
          ((PresheafOfModules.sheafificationAdjunction.{u + 1}
            (finiteCoefficientScalarMap T A)).homEquiv _ _ (f ≫ g)) = _
        rw [Adjunction.homEquiv_naturality_right]
        rfl }

private theorem finiteCoefficientRestriction_isEquivalence (T : Scheme.{u}) (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteCoefficientRestriction T A).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (Adjunction.rightAdjointUniq (finiteCoefficientRealization T A).asEquivalence.toAdjunction
      (finiteCoefficientRealizationAdjunction T A))

attribute [local instance] finiteCoefficientRestriction_isEquivalence

private theorem finiteCoefficientRestriction_additive (T : Scheme.{u}) (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteCoefficientRestriction T A).Additive :=
  (finiteCoefficientRealizationAdjunction T A).right_adjoint_additive

attribute [local instance] finiteCoefficientRestriction_additive

private lemma finiteCoefficientDirectImageMap_scalar {S T : Scheme.{u}} (f : S ⟶ T)
    (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    finiteCoefficientScalarMap T A ≫ (finiteCoefficientDirectImageMap f A).hom =
      Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op (finiteCoefficientScalarMap S A) := by
  have h := (sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv
    (finiteCoefficientPresheaf T A)
    ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj (finiteCoefficientRingSheaf S A))
    |>.apply_symm_apply (finiteCoefficientDirectImagePresheafMap f A)
  change toSheafify _ _ ≫ (finiteCoefficientDirectImageMap f A).hom = _ at h
  rw [finiteCoefficientScalarMap, Category.assoc, h]
  ext W a
  rfl

private noncomputable def finiteCoefficientRestriction_pushforward {S T : Scheme.{u}} (f : S ⟶ T)
    (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    finiteModulePushforward f A ⋙ finiteCoefficientRestriction T A ≅
      finiteCoefficientRestriction S A ⋙ lowerStar (ModuleCat.{u + 1} A) f := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun W ↦ ?_) ?_)
    · let e :
          ((finiteModulePushforward f A ⋙ finiteCoefficientRestriction T A).obj M).obj.obj W ≅
          ((finiteCoefficientRestriction S A ⋙
            lowerStar (ModuleCat.{u + 1} A) f).obj M).obj.obj W :=
        { hom := ModuleCat.ofHom
            (X := ((finiteModulePushforward f A ⋙
              finiteCoefficientRestriction T A).obj M).obj.obj W)
            (Y := ((finiteCoefficientRestriction S A ⋙
              lowerStar (ModuleCat.{u + 1} A) f).obj M).obj.obj W)
            { toFun := id
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a m ↦ by
                change (show (finiteCoefficientRingSheaf S A).obj.obj
                  ((Scheme.proEtaleBaseChange f).op.obj W) from
                  (finiteCoefficientDirectImageMap f A).hom.app W
                  ((finiteCoefficientScalarMap T A).app W a)) • (show M.val.obj
                    ((Scheme.proEtaleBaseChange f).op.obj W) from m) =
                  ((finiteCoefficientScalarMap S A).app
                    ((Scheme.proEtaleBaseChange f).op.obj W) a) • (show M.val.obj
                    ((Scheme.proEtaleBaseChange f).op.obj W) from m)
                rw [← NatTrans.comp_app_apply,
                  finiteCoefficientDirectImageMap_scalar]
                rfl }
          inv := ModuleCat.ofHom
            (X := ((finiteCoefficientRestriction S A ⋙
              lowerStar (ModuleCat.{u + 1} A) f).obj M).obj.obj W)
            (Y := ((finiteModulePushforward f A ⋙
              finiteCoefficientRestriction T A).obj M).obj.obj W)
            { toFun := id
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a m ↦ by
                change ((finiteCoefficientScalarMap S A).app
                  ((Scheme.proEtaleBaseChange f).op.obj W) a) • (show M.val.obj
                    ((Scheme.proEtaleBaseChange f).op.obj W) from m) =
                  ((finiteCoefficientDirectImageMap f A).hom.app W
                    ((finiteCoefficientScalarMap T A).app W a)) • (show M.val.obj
                    ((Scheme.proEtaleBaseChange f).op.obj W) from m)
                rw [← NatTrans.comp_app_apply,
                  finiteCoefficientDirectImageMap_scalar]
                rfl } }
      exact e
    · intro W W' g
      ext m
      rfl
  · intro M M' g
    ext W m
    rfl

private noncomputable def coefficientTransportAdjunction {S T : Scheme.{u}} (f : S ⟶ T)
    (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteCoefficientRestriction T A ⋙ upperStar (ModuleCat.{u + 1} A) f) ⋙
        finiteCoefficientRealization S A ⊣
      finiteCoefficientRestriction S A ⋙
        (lowerStar (ModuleCat.{u + 1} A) f ⋙ finiteCoefficientRealization T A) :=
  (((finiteCoefficientRealizationAdjunction T A).toEquivalence.symm.toAdjunction).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)).comp
      (finiteCoefficientRealizationAdjunction S A)

private noncomputable def coefficientTransportPushforward {S T : Scheme.{u}} (f : S ⟶ T)
    (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    finiteModulePushforward f A ≅ finiteCoefficientRestriction S A ⋙
        (lowerStar (ModuleCat.{u + 1} A) f ⋙ finiteCoefficientRealization T A) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (asIso (finiteCoefficientRealizationAdjunction T A).counit).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteCoefficientRestriction_pushforward f A)
      (finiteCoefficientRealization T A) ≪≫ Functor.associator _ _ _

private noncomputable def finiteCoefficientRestriction_pullback {S T : Scheme.{u}} (f : S ⟶ T)
    (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    finiteCoefficientModulePullback f A ⋙ finiteCoefficientRestriction S A ≅
      finiteCoefficientRestriction T A ⋙ upperStar (ModuleCat.{u + 1} A) f :=
  Functor.isoWhiskerRight
    (Adjunction.leftAdjointUniq (finiteModuleAdjunction f A)
      ((coefficientTransportAdjunction f A).ofNatIsoRight
        (coefficientTransportPushforward f A).symm)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (finiteCoefficientRealizationAdjunction S A).unit).symm ≪≫
    Functor.rightUnitor _




variable {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
  (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))
  (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]

include hij in
private lemma finiteClosed_exact : PreservesFiniteColimits (finiteModulePushforward i A) := by
  have := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  have : PreservesFiniteColimits
      (finiteModulePushforward i A ⋙ finiteCoefficientRestriction T A) :=
    preservesFiniteColimits_of_natIso (finiteCoefficientRestriction_pushforward i A).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (finiteCoefficientRestriction T A)

private lemma finitePush_full {S : Scheme.{u}} (f : S ⟶ T)
    [(lowerStar (ModuleCat.{u + 1} A) f).Full] : (finiteModulePushforward f A).Full :=
  Functor.Full.of_comp_faithful_iso (finiteCoefficientRestriction_pushforward f A)

private lemma finitePush_faithful {S : Scheme.{u}} (f : S ⟶ T)
    [(lowerStar (ModuleCat.{u + 1} A) f).Faithful] : (finiteModulePushforward f A).Faithful :=
  Functor.Faithful.of_comp_iso (finiteCoefficientRestriction_pushforward f A)

include hij in
omit [IsClosedImmersion i] [QuasiCompact j] in
private lemma finite_zero (M : FiniteCoefficientModules Z A) :
    IsZero ((finiteCoefficientModulePullback j A).obj ((finiteModulePushforward i A).obj M)) := by
  apply IsZero.of_full_of_faithful_of_isZero (finiteCoefficientRestriction U A)
  exact (isZero_upperStar_lowerStar_of_disjoint (ModuleCat.{u + 1} A) i j hij.disjoint
    ((finiteCoefficientRestriction Z A).obj M)).of_iso
      ((finiteCoefficientRestriction_pullback j A).app _ ≪≫
        (upperStar (ModuleCat.{u + 1} A) j).mapIso
          ((finiteCoefficientRestriction_pushforward i A).app M))

include hij in
omit [IsOpenImmersion j] in
private lemma finite_joint_zero (M : FiniteCoefficientModules T A)
    (hi : IsZero ((finiteCoefficientModulePullback i A).obj M))
    (hj : IsZero ((finiteCoefficientModulePullback j A).obj M)) : IsZero M := by
  apply IsZero.of_full_of_faithful_of_isZero (finiteCoefficientRestriction T A)
  exact isZero_of_isZero_upperStar_of_isCompl i j hij _
    (((finiteCoefficientRestriction Z A).map_isZero hi).of_iso
      ((finiteCoefficientRestriction_pullback i A).app M).symm)
    (((finiteCoefficientRestriction U A).map_isZero hj).of_iso
      ((finiteCoefficientRestriction_pullback j A).app M).symm)



private theorem finiteModulesGroth (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (FiniteCoefficientModules S A) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
    (Scheme.ProEt.topology S)
    (finiteCoefficientRingSheaf S A)

attribute [local instance] finiteModulesGroth

private theorem finitePull_limits {S V : Scheme.{u}} (f : S ⟶ V) :
    PreservesFiniteLimits (finiteCoefficientModulePullback f A) :=
  (finiteCoefficientModulePullback_exact f A).1

attribute [local instance] finitePull_limits

private theorem finitePull_colimits {S V : Scheme.{u}} (f : S ⟶ V) :
    PreservesFiniteColimits (finiteCoefficientModulePullback f A) :=
  (finiteCoefficientModulePullback_exact f A).2.1

attribute [local instance] finitePull_colimits

private theorem finitePush_limits {S V : Scheme.{u}} (f : S ⟶ V) :
    PreservesFiniteLimits (finiteModulePushforward f A) := by
  have := (finiteModuleAdjunction f A).isRightAdjoint
  infer_instance

attribute [local instance] finitePush_limits

include hij in
private lemma finite_derived_triangle
    [PreservesFiniteColimits (finiteModulePushforward i A)] :
    ∃ (H : FiniteCoefficientDerivedCategory T A ⥤ FiniteCoefficientDerivedCategory Z A)
      (G : FiniteCoefficientDerivedCategory U A ⥤ FiniteCoefficientDerivedCategory T A)
      (ai : (finiteModulePushforward i A).mapDerivedCategory ⊣ H)
      (aj : (finiteCoefficientModulePullback j A).mapDerivedCategory ⊣ G),
      ∀ K, ∃ w, Triangle.mk (ai.counit.app K) (aj.unit.app K) w ∈
        distTriang (FiniteCoefficientDerivedCategory T A) := by
  have := finiteClosed_exact i j hij A
  have := finitePush_full A i
  have := finitePush_faithful A i
  have : (lowerStar (ModuleCat.{u + 1} A) j).Full :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).fullyFaithfulROfIsIsoCounit.full
  have : (lowerStar (ModuleCat.{u + 1} A) j).Faithful :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).fullyFaithfulROfIsIsoCounit.faithful
  have := finitePush_full A j
  have := finitePush_faithful A j
  have : (finiteModulePushforward i A).PreservesKInjectiveComplexes :=
    (finiteModuleAdjunction i A).preservesKInjectiveComplexes
  have : (finiteModulePushforward j A).PreservesKInjectiveComplexes :=
    (finiteModuleAdjunction j A).preservesKInjectiveComplexes
  let L := (finiteModulePushforward i A).mapDerivedCategory
  let J := (finiteCoefficientModulePullback j A).mapDerivedCategory
  let aj := (finiteModuleAdjunction j A).mapDerivedCategoryRightDerivedAdjunction
  have : IsIso aj.counit := aj.counit_isIso_of_R_fully_faithful
  have : L.Full := Functor.Full.of_iso
    (finiteModulePushforward i A).rightDerivedFunctorIsoMapDerivedCategory
  have : L.Faithful := Functor.Faithful.of_iso
    (finiteModulePushforward i A).rightDerivedFunctorIsoMapDerivedCategory
  have hzero (M : FiniteCoefficientDerivedCategory Z A) : IsZero (J.obj (L.obj M)) := by
    exact (Functor.isZero_mapDerivedCategory_obj (finiteModulePushforward i A ⋙
      finiteCoefficientModulePullback j A) M (fun _ ↦ finite_zero i j hij A _)).of_iso
        (((finiteModulePushforward i A).mapDerivedCategoryCompIso _).symm.app M)
  have hjoint (M : FiniteCoefficientDerivedCategory T A)
      (hi : IsZero ((finiteCoefficientModulePullback i A).mapDerivedCategory.obj M))
      (hj : IsZero (J.obj M)) : IsZero M := by
    rw [DerivedCategory.isZero_iff]
    intro n
    exact finite_joint_zero i j hij A _
      (((DerivedCategory.homologyFunctor _ n).map_isZero hi).of_iso
        (((finiteCoefficientModulePullback i A).mapDerivedCategoryHomologyFunctorIso n).app M))
      (((DerivedCategory.homologyFunctor _ n).map_isZero hj).of_iso
        (((finiteCoefficientModulePullback j A).mapDerivedCategoryHomologyFunctorIso n).app M))
  have hess (M : FiniteCoefficientDerivedCategory T A) (hM : IsZero (J.obj M)) :
      L.essImage M := by
    let ai := ((finiteModuleAdjunction i A).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
      (finiteModulePushforward i A).rightDerivedFunctorIsoMapDerivedCategory
    have : IsIso (finiteModuleAdjunction i A).counit :=
      (finiteModuleAdjunction i A).counit_isIso_of_R_fully_faithful
    have : IsIso ai.counit := ai.counit_isIso_of_R_fully_faithful
    obtain ⟨W, v, w, hW⟩ := distinguished_cocone_triangle (ai.unit.app M)
    have hiu : IsIso ((finiteCoefficientModulePullback i A).mapDerivedCategory.map
        (ai.unit.app M)) :=
      have := IsIso.id ((finiteCoefficientModulePullback i A).mapDerivedCategory.obj M)
      IsIso.of_isIso_fac_right (ai.left_triangle_components M)
    have hju : IsIso (J.map (ai.unit.app M)) :=
      isIso_of_source_target_iso_zero _ hM.isoZero (hzero _).isoZero
    have hz : IsZero W := hjoint W
      ((Triangle.isZero₃_iff_isIso₁ _
        ((finiteCoefficientModulePullback i A).mapDerivedCategory.map_distinguished _ hW)).2 hiu)
      ((Triangle.isZero₃_iff_isIso₁ _ (J.map_distinguished _ hW)).2 hju)
    have : IsIso (ai.unit.app M) := (Triangle.isZero₃_iff_isIso₁ _ hW).1 hz
    exact ⟨_, ⟨(asIso (ai.unit.app M)).symm⟩⟩
  have : L.IsLeftAdjoint := Recollement.isLeftAdjoint aj
    (Functor.FullyFaithful.ofFullyFaithful L) hzero hess
  let ai := Adjunction.ofIsLeftAdjoint L
  refine ⟨L.rightAdjoint, _, ai, aj, fun K ↦ ?_⟩
  exact Recollement.exists_distTriang_counit_unit aj ai
    (Functor.FullyFaithful.ofFullyFaithful L) hzero hess K


/-- The closed-support triangle, with its actual adjunction arrows, in the entire
unbounded ordinary derived category of finite-ring pro-etale module sheaves.
The localization isomorphisms specify i_* and j^* on all complexes and all maps;
the right adjoints specify Ri^! and Rj_* uniquely up to their adjunction isomorphisms.
There is no boundedness, constructibility, completeness, or commutativity hypothesis.

Source: blueprint sec-smooth-purity/sk-prop-sf-localization,
lem-exc-proetale-support-triangle, order 1866
(blueprint: lem-exc-proetale-support-triangle).

Proof, following the six steps of the node:
1. Work on the small skeletons and in the common sheaf universe of [def-weil-pbc-proetale-site].
For the finite ring $A$, use the sheaf of rings $A_S$ and left module sheaves of
[def-weil-pbc-proetale-modules], for $S=T,U,Z$; no commutativity of $A$ is needed. By
[lem-weil-pbc-ring-sheaves-grothendieck] these abelian categories are Grothendieck. Apply
[lem-pur-kinjective-degreewise-existence] to a complex representing $K$ to choose a
quasi-isomorphism $K\to I$ with $I$ K-injective and every $I^q$ injective. Use the exact inverse
images with transported coefficient actions of [prop-weil-pbc-proetale-constant-exact]. Define an
additive sheaf functor $H$ on left $A_T$-modules by $H(N)=i^*\ker(N\to j_*j^*N)$, using the open
adjunction unit, and on morphisms by the induced kernel map followed by $i^*$. Kernels here are
the sectionwise kernels of [def-weil-sheaf-of-modules-category]. Applying $H$ termwise preserves
shifts and mapping-cone matrices, so its composite with derived localization is exact on homotopy
categories. By [lem-weil-pbc-kinjective-total-derived], its total right derived functor $RH$
exists and $RH(K)$ is represented by $H(I)$. Step 6 proves that $RH$ is the right adjoint $Ri^!$
in the statement and identifies its counit. No adjunction for $H$ has been assumed here.

2. The geometric clause (1) of [lem-weil-proetale-weakly-etale-localization], applied with
auxiliary coefficient ring $\mathbf Z$, identifies $U_{\mathrm{proet}}$ with
$T_{\mathrm{proet}}/U$. On an object $W\to U$, the inverse-image indexing category of
[def-weil-proetale-inverse-image] has initial object $(W,W\to U\times_TW)$: the arrow from it to
$(V,\phi)$ is forced to be the second component of $\phi$. The opposite category therefore has a
final object, and the inverse-image colimit is $N(W)$. Restriction is already a sheaf, since
localized coverings are the same coverings. This calculation applies also to rings and their
actions. For the coefficient sheaves of [def-weil-pbc-proetale-modules], restriction to the
localized site gives the same presheaf $W\mapsto\operatorname{Cont}(\pi_0(|W|),A)$ before
sheafification. The canonical coefficient map of [prop-weil-pbc-proetale-constant-ring-map] is
thus the identity under this identification: both maps send a constant $a$ to $a$, and on each
open fibre of a locally constant function the two maps agree, hence agree after gluing and
sheafification. Consequently the module $j^*$ of [prop-weil-pbc-proetale-constant-exact] is
precisely restriction, including its action and its unit. It preserves quasi-isomorphisms by
exactness. By [lem-pur-kinjective-restrict-localized], $j^*I$ is K-injective, so it resolves
$j^*K$. Apply [lem-weil-pbc-kinjective-total-derived] to the termwise additive functor $j_*$
followed by derived localization: it preserves shifts and cone matrices (identities, differentials
and their negatives), hence defines an exact functor on homotopy categories. Thus $Rj_*j^*K$ is
represented by $j_*j^*I$. On an object $V\to T$, this complex has terms $I^q(V_U)$,
$V_U=V\times_TU$, and the unit is restriction $I^q(V)\to I^q(V_U)$ by the direct-image formula in
[def-weil-proetale-inverse-image]. For completeness, the derived unit is indeed this termwise
unit: because $j^*$ is exact and left adjoint to $j_*$,
[lem-weil-pbc-right-adjoint-preserves-kinjective] makes $j_*J$ K-injective whenever $J$ is
K-injective on $U$. For any complex $M$, [lem-weil-pbc-kinjective-hom-derived] and the termwise
adjunction, which respects differentials and homotopies, give
$\operatorname{Hom}_{D(U)}(j^*M,QJ)=
  \operatorname{Hom}_{K(U)}(j^*M,J)=
  \operatorname{Hom}_{K(T)}(M,j_*J)=
  \operatorname{Hom}_{D(T)}(QM,Qj_*J)$.
Here $Q$ denotes localization and $K(S)$ the homotopy category on $S$. With $M=I$ and $J=j^*I$,
the identity on $j^*I$ corresponds to precisely $I\to j_*j^*I$, so the represented map is the
derived open unit.

3. For an object $V$ of $T_{\mathrm{proet}}$, put $V_U=V\times_TU$ and let $a:V_U\to V$ be the
open inclusion. It is a monomorphism by clause (4) of
[lem-weil-proetale-weakly-etale-localization], again using auxiliary ring $\mathbf Z$ for the
geometric assertion. Let $P_V=A_T[h_V]$ be the free module presheaf of
[lem-weil-pbc-free-yoneda-presheaf-module] and $L_V=P_V^\#$ its module sheafification
[def-weil-presheaf-modules-sheafification]. The map $P_{V_U}\to P_V$ sends $e_b$ to $e_{ab}$ at an
object $W$. It commutes with restriction because both composites send $r e_b$ to $r|_c e_{abc}$.
Since $a$ is monic, the basis map $\operatorname{Hom}(W,V_U)\to\operatorname{Hom}(W,V)$ is
injective. A free-module element in its kernel has every coefficient zero, so the presheaf map is
componentwise injective, hence monic. Exact module sheafification
[lem-weil-pbc-ringed-site-module-sheafification-exact] gives a monomorphism $L_{V_U}\to L_V$.

4. The free-presheaf bijection [lem-weil-pbc-free-yoneda-presheaf-module] and the sheafification
adjunction [def-weil-presheaf-modules-sheafification] give $\operatorname{Hom}(L_V,N)=N(V)$.
Precomposing with $L_{V_U}\to L_V$ corresponds to restriction: the map associated to $x\in N(V)$
sends $e_b$ to $x|_b$, so on the identity generator of $V_U$ its precomposition has value $x|_a$.
For $y\in I^q(V_U)$ extend the corresponding $L_{V_U}\to I^q$ across the monomorphism of Step 3,
using injectivity in the precise sense of [def-sp-injective-resolutions]. The extension
corresponds to $x\in I^q(V)$ with $x|_a=y$. Hence $I^q\to j_*j^*I^q$ is sectionwise surjective for
every site object $V$. It is epic: two sheaf maps out of its target agreeing after it agree on
every section by such lifts, and hence are equal by [def-weil-sheaf-of-modules-category].

5. Put $F^q=\ker(\eta^q:I^q\to j_*j^*I^q)$; these kernels are sectionwise
[def-weil-sheaf-of-modules-category]. On an object $W\to U$, the restriction unit is the identity
under $W\times_TU=W$, so $F^q(W)=0$ and $j^*F^q=0$. The open complement is quasi-compact as a
morphism. Indeed, [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal] applied to complements
in $T$ of finite unions from an open cover of any open subset $O\subseteq T$ supplies a maximal
such finite union. Adjoining any further member cannot enlarge it, so it equals $O$. Thus every
open subset of $T$ is quasi-compact, in particular $U\cap V$ for every affine open $V\subseteq T$;
this is the required quasi-compactness of $j$. The current statement of
[lem-exc-proetale-closed-essential-image] is for commutative ring-sheaf coefficients, so apply it
after the following elementary restriction of scalars, rather than directly to $A_T$. Since $A$ is
finite, $1_A$ has a positive additive order $n$; put $B=\mathbf Z/n\mathbf Z$. Integer multiples
of $1_A$ give a central ring map $B\to A$ and therefore, on the continuous-function presheaves of
Step 1 and by sheafification, maps $B_S\to A_S$ for $S=T,Z,U$. The structure maps for $B$ and $A$
in [prop-weil-pbc-proetale-constant-ring-map] commute with these maps: both composites send each
constant integer residue to that multiple of $1_A$, and agreement on open fibres extends by gluing
and sheafification. By the transported-action formula of [prop-weil-pbc-proetale-constant-exact],
forgetting from $A_S$-modules to $B_S$-modules thus commutes with $i^*,j^*,i_*$ and their
underlying unit maps. In particular, for any $A_T$-module $N$ with $j^*N=0$, the cited
essential-image node applied to the commutative coefficient sheaf $B_T$ and its canonical
inverse-image identifications gives an invertible underlying unit $\eta_N:N\to i_*i^*N$. This is
the actual $A_T$-module unit: naturality of the inverse-image unit of
[def-weil-proetale-inverse-image] with respect to the action map gives
$\eta_N(rm)=\eta_{A_T}(r)\eta_N(m)$, and the direct-image coefficient action through
$\rho_A=i_*c_i\circ\eta_{A_T}$ turns the right side into $r\eta_N(m)$. Its inverse $h$ is also
$A_T$-linear, since $\eta_N(h(ry))=ry=\eta_N(rh(y))$ and $\eta_N$ is injective. The same
restriction of scalars shows $j^*i_*M=0$ for every $A_Z$-module $M$, by the other direction of the
essential-image node. No commutativity of $A$ was used. Apply this supported-unit conclusion to
$N=F^q$ to obtain the canonical $A_T$-linear unit isomorphism $F^q\to i_*i^*F^q=i_*HI^q$. Use its
inverse to obtain the kernel inclusion $i_*HI^q\to I^q$. Naturality of $\eta$ gives
$\eta^{q+1}d_I^q=(j_*j^*d_I^q)\eta^q$, so $d_I^q$ restricts to $F^q\to F^{q+1}$; its square is
zero by cancellation of the kernel inclusion. Naturality of the closed unit makes the displayed
identification of $F$ with $i_*HI$ an identification of complexes. The kernel inclusions and the
units are complex maps, and Step 4 makes the units epic. Therefore
[lem-weil-pbc-cochain-complexes-degreewise-exact] gives the short exact sequence of complexes
$$0\longrightarrow i_*HI\longrightarrow I\longrightarrow j_*j^*I\longrightarrow0.$$

6. The quasi-compact-complement condition verified in Step 5 allows
[lem-exc-proetale-closed-exact], so $i_*$ is exact for the given finite ring $A$. The supported
kernel construction of Step 5 is a sheaf right adjoint to $i_*$. Indeed $j^*i_*M=0$ for every left
$A_Z$-module $M$ by that step. Naturality of the open unit therefore makes every map $i_*M\to N$
factor uniquely through $F(N)=\ker(N\to j_*j^*N)$. The supported unit isomorphism
$F(N)\xrightarrow{\sim}i_*i^*F(N)=i_*H(N)$ and full faithfulness of $i_*$ from
[lem-exc-proetale-closed-fully-faithful] give natural bijections
$\operatorname{Hom}_T(i_*M,N)=\operatorname{Hom}_T(i_*M,F(N))=\operatorname{Hom}_Z(M,H(N))$. The
identity of $H(N)$ corresponds to the inverse supported-unit isomorphism followed by the kernel
inclusion into $N$. This is exactly the first map used in Step 5. The bijections are additive;
applied in every degree, their naturality identifies chain maps and homotopies. Since the left
adjoint $i_*$ is exact, [lem-weil-pbc-right-adjoint-preserves-kinjective] shows $H(I)$ is
K-injective. By [lem-weil-pbc-kinjective-hom-derived], for every complex $M$ on $Z$ there are
natural bijections
$$\operatorname{Hom}_{D(T)}(Qi_*M,QI)=
  \operatorname{Hom}_{K(T)}(i_*M,I)=
  \operatorname{Hom}_{K(Z)}(M,H(I))=
  \operatorname{Hom}_{D(Z)}(QM,QH(I)).$$
Together with the functorial K-injective replacements and total-derived computation of Step 1,
these identify $RH$ with the right adjoint $Ri^!$ on the entire unbounded derived categories.
Taking $M=H(I)$ shows that the derived counit is the localization of the supported kernel
inclusion of Step 5. Exactness of $i_*$ also means its termwise application computes the functor
on derived categories: exactness identifies its cohomology with $i_*$ of cohomology, so it
preserves quasi-isomorphisms. Thus $i_*H(I)$ represents $i_*Ri^!K$. Now apply
[lem-weil-pbc-complex-ses-triangle] to the short exact sequence of Step 5. The middle and third
terms represent $K$ and $Rj_*j^*K$ by Steps 1 and 2; its first two arrows have just been
identified as the exceptional counit and the open unit. It gives precisely
$$i_*Ri^!K\longrightarrow K\longrightarrow Rj_*j^*K\longrightarrow i_*Ri^!K[1].$$ No step assumes
constructibility or boundedness of $K$ or of $Ri^!K$. -/
theorem exists_proEtale_closedSupportTriangle
    {T Z U : Scheme.{u}} [IsLocallyNoetherian T] [CompactSpace T]
    (i : Z ⟶ T) [IsClosedImmersion i] (j : U ⟶ T) [IsOpenImmersion j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (A : Type (u + 1)) [Ring A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    ∃ (iPush : FiniteCoefficientDerivedCategory Z A ⥤ FiniteCoefficientDerivedCategory T A)
      (jPull : FiniteCoefficientDerivedCategory T A ⥤ FiniteCoefficientDerivedCategory U A),
      Nonempty
        ((SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange i)
          (J := Scheme.ProEt.topology T) (K := Scheme.ProEt.topology Z)
          (finiteCoefficientDirectImageMap i A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q ≅ DerivedCategory.Q ⋙ iPush) ∧
      Nonempty
        ((finiteCoefficientModulePullback j A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ≅ DerivedCategory.Q ⋙ jPull) ∧
      ∃ (iShriek : FiniteCoefficientDerivedCategory T A ⥤ FiniteCoefficientDerivedCategory Z A)
        (jPush : FiniteCoefficientDerivedCategory U A ⥤ FiniteCoefficientDerivedCategory T A)
        (closedAdj : iPush ⊣ iShriek) (openAdj : jPull ⊣ jPush),
        ∀ K : FiniteCoefficientDerivedCategory T A,
          ∃ δ : jPush.obj (jPull.obj K) ⟶ (iPush.obj (iShriek.obj K))⟦(1 : ℤ)⟧,
            Triangle.mk (closedAdj.counit.app K) (openAdj.unit.app K) δ ∈
              distTriang (FiniteCoefficientDerivedCategory T A) := by
  have : IsNoetherian T := {}
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := inferInstance
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hU]
    exact isCompl_compl
  have := finiteClosed_exact i j hij A
  let iPush := (finiteModulePushforward i A).mapDerivedCategory
  let jPull := (finiteCoefficientModulePullback j A).mapDerivedCategory
  refine ⟨iPush, jPull, ?_, ?_, ?_⟩
  · exact ⟨(Functor.mapDerivedCategoryFactors (finiteModulePushforward i A)).symm⟩
  · exact ⟨(Functor.mapDerivedCategoryFactors
      (finiteCoefficientModulePullback j A)).symm⟩
  · exact finite_derived_triangle i j hij A

end

end AlgebraicGeometry.ProEtale
