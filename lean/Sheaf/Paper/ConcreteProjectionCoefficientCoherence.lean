/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module
public import Sheaf.Paper.ConcreteProjectionReductionData
import Sheaf.SixFunctors.OpenScalarTensorData
import Mathlib.CategoryTheory.Limits.HasLimits
import all Sheaf.Algebra.Homology.ScalarHomTensorCoherence
import Sheaf.SixFunctors.OpenScalarCoefficientCoherence
import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition
/-! # Coefficient coherence of the normalized tensor, pullback and support maps
Source: Stacks Tags 07A4, 07A6, 0D6D, 0E47, and 0GL6.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConcreteProjectionReduction
open AlgebraicGeometry.ProEtale.OpenScalarTensor
local instance (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

variable (m : Models.{u}) (choices : Choices m)
attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses
  CoefficientClosedStructure.tensor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
attribute [local irreducible] Functor.mapHomologicalComplexUpToQuasiIso
  Functor.mapHomologicalComplexUpToQuasiIsoFactors reductionDerivedChange
attribute [local irreducible] pbcDerivedScalarAdjunction
attribute [local irreducible] scalarHomExtensionComp scalarHomExtensionId
  PurCompactSupport.tensorComposition
private theorem tensor_comp_eq (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (d : R ⟶ V) (h : a ≫ b = d)
    (ma : ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) a)
    (mb : ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) b)
    (md : ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) d)
    (K L : DerivedCategory.{u + 2} (scalarModules.{u + 1, u, u + 1} (ProEt.topology T) R)) :
    ((m T).scalar b).derived.map (ma.iso.hom.app (K, L)) ≫
      mb.iso.hom.app (((m T).scalar a).derived.obj K, ((m T).scalar a).derived.obj L) ≫
      ((m T).closed V).tensor.map (Prod.mkHom
        ((scalarHomExtensionComp.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) a b ≪≫
          eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h)).hom.app K)
        ((scalarHomExtensionComp.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) a b ≪≫
          eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h)).hom.app L)) =
    (scalarHomExtensionComp.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) a b ≪≫
      eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h)).hom.app
        (((m T).closed R).tensor.obj (K, L)) ≫ md.iso.hom.app (K, L) := by
  subst d
  simp only [eqToIso_refl, Iso.trans_refl]
  let F := ((m T).scalar a).derived
  let G := ((m T).scalar b).derived
  let H := ((m T).scalar (a ≫ b)).derived
  let cc := scalarHomExtensionComp.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) a b
  let lhs : ((m T).closed R).tensor ⋙ F ⋙ G ⟶
      H.prod H ⋙ ((m T).closed V).tensor :=
    Functor.whiskerRight ma.iso.hom G ≫
      Functor.whiskerLeft (F.prod F) mb.iso.hom ≫
      Functor.whiskerRight (NatTrans.prod cc.hom cc.hom) ((m T).closed V).tensor
  let rhs : ((m T).closed R).tensor ⋙ F ⋙ G ⟶
      H.prod H ⋙ ((m T).closed V).tensor :=
    Functor.whiskerLeft ((m T).closed R).tensor cc.hom ≫ md.iso.hom
  have he : lhs = rhs := CategoryTheory.ScalarHomTensor.representatives_ext.{u + 1, u, u + 1, u + 2}
    (J := ProEt.topology T) (m T) (R := R)
      (F := ((m T).closed R).tensor ⋙ F ⋙ G) (by
    intro P Q hp hq
    exact CategoryTheory.ScalarHomTensor.comp_on_representatives.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) a b ma mb md P Q hp hq)
  exact congrArg (fun z ↦ z.app (K, L)) he
private theorem tensor_id_eq (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : R ⟶ R) (h : a = 𝟙 R) (ma : ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) a)
    (K L : DerivedCategory.{u + 2} (scalarModules.{u + 1, u, u + 1} (ProEt.topology T) R)) :
    ma.iso.hom.app (K, L) ≫ ((m T).closed R).tensor.map (Prod.mkHom
      ((eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h) ≪≫
        scalarHomExtensionId.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) R).hom.app K)
      ((eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h) ≪≫
        scalarHomExtensionId.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) R).hom.app L)) =
    (eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h) ≪≫
      scalarHomExtensionId.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) R).hom.app (((m T).closed R).tensor.obj (K, L)) := by
  subst a
  simp only [eqToIso_refl, Iso.refl_trans]
  let F := ((m T).scalar (𝟙 R)).derived
  let ci := scalarHomExtensionId.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) (m T) R
  let lhs : ((m T).closed R).tensor ⟶ F.prod F ⋙ ((m T).closed R).tensor :=
    Functor.whiskerRight (NatTrans.prod ci.inv ci.inv) ((m T).closed R).tensor
  let rhs : ((m T).closed R).tensor ⟶ F.prod F ⋙ ((m T).closed R).tensor :=
    Functor.whiskerLeft ((m T).closed R).tensor ci.inv ≫ ma.iso.hom
  have he : lhs = rhs := CategoryTheory.ScalarHomTensor.representatives_ext.{u + 1, u, u + 1, u + 2}
    (J := ProEt.topology T) (m T) (R := R)
      (F := ((m T).closed R).tensor) (by
    intro P Q hp hq
    exact CategoryTheory.ScalarHomTensor.id_on_representatives.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) R ma P Q hp hq)
  have hh := congrArg (fun z ↦ z.app (K, L)) he
  change ((m T).closed R).tensor.map (Prod.mkHom (ci.inv.app K) (ci.inv.app L)) =
    ci.inv.app (((m T).closed R).tensor.obj (K, L)) ≫ ma.iso.hom.app (K, L) at hh
  apply (cancel_epi (ci.inv.app (((m T).closed R).tensor.obj (K, L)))).mp
  rw [← Category.assoc, ← hh]
  change ((m T).closed R).tensor.map (Prod.mkHom (ci.inv.app K) (ci.inv.app L)) ≫
      ((m T).closed R).tensor.map (Prod.mkHom (ci.hom.app K) (ci.hom.app L)) =
    ci.inv.app _ ≫ ci.hom.app _
  simp only [← Functor.map_comp, CategoryTheory.prod_comp, Iso.inv_hom_id_app]
  exact ((m T).closed R).tensor.map_id (K, L)
/-- The normalized scalar tensor comparison respects coefficient composition.
Proof: compare on flat K-flat representatives. Both routes split the same pure tensor
and associate scalar multiplication; resolving-class descent gives equality everywhere.
Source: Stacks Tags 07A4, 07A6, 0D6D and 0E47.
(blueprint: lem-sf-concrete-projection-coefficient-coherence). -/
theorem tensor_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u})
    (K L : proEtaleDerivedCategory T A) :
    (scalar m ψ T).map ((choices.scalarTensor φ T).iso.hom.app (K, L)) ≫
      (choices.scalarTensor ψ T).iso.hom.app
        ((scalar m φ T).obj K, (scalar m φ T).obj L) ≫
      (tensor m C T).map (Prod.mkHom ((scalarComp m φ ψ T).hom.app K)
        ((scalarComp m φ ψ T).hom.app L)) =
      (scalarComp m φ ψ T).hom.app ((tensor m A T).obj (K, L)) ≫
        (choices.scalarTensor (ψ.comp φ) T).iso.hom.app (K, L) := by
  exact tensor_comp_eq m T (proEtaleConstantRingMap φ) (proEtaleConstantRingMap ψ)
    (proEtaleConstantRingMap (ψ.comp φ))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp
      (CommRingCat.ofHom (RingHom.ulift φ)) (CommRingCat.ofHom (RingHom.ulift ψ))).symm
    (choices.scalarTensor φ T) (choices.scalarTensor ψ T)
    (choices.scalarTensor (ψ.comp φ) T) K L
/-- The normalized scalar tensor comparison respects the scalar identity unitor.
Proof: the identity comparison on flat K-flat representatives inserts and removes the
unit scalar. Descend this equation and cancel the inverse scalar unitor.
Source: Stacks Tags 07A4, 07A6, 0D6D and 0E47.
(blueprint: lem-sf-concrete-projection-coefficient-coherence). -/
theorem tensor_id (A : Type u) [CommRing A] (T : Scheme.{u})
    (K L : proEtaleDerivedCategory T A) :
    (choices.scalarTensor (RingHom.id A) T).iso.hom.app (K, L) ≫
      (tensor m A T).map (Prod.mkHom ((scalarId m A T).hom.app K)
        ((scalarId m A T).hom.app L)) =
      (scalarId m A T).hom.app ((tensor m A T).obj (K, L)) := by
  rw [scalarId_eq]
  exact tensor_id_eq m T (proEtaleConstantRing T A)
    (proEtaleConstantRingMap (RingHom.id A))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))
    (choices.scalarTensor (RingHom.id A) T) K L
attribute [local semireducible] scalarHomExtensionId
private theorem restriction_comp_eq (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ V) :
    pbcRestrictComp a b (a ≫ b) rfl =
      (scalarHomOrdinaryRestrictionComp.{u + 1, u, u + 1}
        (J := ProEt.topology T) a b).symm := by
  apply (pbcRestrictComp_exists a b (a ≫ b) rfl).unique
  · exact (pbcRestrictComp_exists a b (a ≫ b) rfl).exists.choose_spec
  · intro M U x
    rfl
private theorem derived_restriction_comp_eq (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ V) :
    pbcDerivedRestrictComp a b (a ≫ b) rfl =
      (scalarHomRestrictionComp.{u + 1, u, u + 1, u + 2}
        (J := ProEt.topology T) a b).symm := by
  simp only [pbcDerivedRestrictComp, restriction_comp_eq,
    scalarHomRestrictionComp, Iso.trans_symm, Functor.mapDerivedCategoryNatIso_symm]
  rfl
private theorem adjoint_comp_side
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {U : B ⥤ A} {G : B ⥤ C} {V : C ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (δ : W ≅ V ⋙ U) :
    ((a.comp b).ofNatIsoRight δ.symm).leftAdjointUniq c =
      (a.comp b).leftAdjointUniq (c.ofNatIsoRight δ) := by
  apply Iso.ext
  ext K
  apply ((a.comp b).homEquiv _ _).injective
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((a.comp b).ofNatIsoRight δ.symm) c K
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  change _ ≫ δ.inv.app (H.obj K) = _ at h
  apply (cancel_mono (δ.inv.app (H.obj K))).mp
  rw [h, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp [Adjunction.ofNatIsoRight_unit]
private theorem adjoint_comp_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F' : A ⥤ B} {U : B ⥤ A} {G G' : B ⥤ C} {V : C ⥤ B}
    {H H' : A ⥤ C} {W : C ⥤ A}
    (a : F ⊣ U) (a' : F' ⊣ U) (b : G ⊣ V) (b' : G' ⊣ V)
    (c : H ⊣ W) (c' : H' ⊣ W) (δ : V ⋙ U ≅ W) (K : A) :
    (((a.comp b).ofNatIsoRight δ).leftAdjointUniq c).hom.app K ≫
      (c.leftAdjointUniq c').hom.app K =
    (b.leftAdjointUniq b').hom.app (F.obj K) ≫
      G'.map ((a.leftAdjointUniq a').hom.app K) ≫
      (((a'.comp b').ofNatIsoRight δ).leftAdjointUniq c').hom.app K := by
  apply (((a.comp b).ofNatIsoRight δ).homEquiv _ _).injective
  rw [leftAdjointUniq_homEquiv_comp,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change c'.unit.app K = a.homEquiv _ _ (b.homEquiv _ _ _) ≫ _
  erw [leftAdjointUniq_homEquiv_comp b b' (F.obj K)]
  rw [b'.homEquiv_naturality_left]
  erw [leftAdjointUniq_homEquiv_comp a a' K]
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((a'.comp b').ofNatIsoRight δ) c' K
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  exact hh.symm
private theorem scalar_comp_transport_eq (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (d : R ⟶ V) (h : a ≫ b = d)
    (K : DerivedCategory.{u + 2} (scalarModules.{u + 1, u, u + 1} (ProEt.topology T) R)) :
    (scalarHomExtensionComp.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) a b ≪≫
      eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h)).hom.app K ≫
        (((m T).scalar d).adjunction.leftAdjointUniq
          (pbcDerivedScalarAdjunction d)).hom.app K =
    (((m T).scalar b).adjunction.leftAdjointUniq
      (pbcDerivedScalarAdjunction b)).hom.app (((m T).scalar a).derived.obj K) ≫
      (pbcDerivedExtend b).map
        ((((m T).scalar a).adjunction.leftAdjointUniq
          (pbcDerivedScalarAdjunction a)).hom.app K) ≫
      (PurCompactSupport.tensorComposition a b d h).hom.app K := by
  subst d
  simp only [eqToIso_refl, Iso.trans_refl]
  have hc : PurCompactSupport.tensorComposition a b (a ≫ b) rfl =
      ((pbcDerivedScalarAdjunction a).comp (pbcDerivedScalarAdjunction b)).leftAdjointUniq
        ((pbcDerivedScalarAdjunction (a ≫ b)).ofNatIsoRight
          (scalarHomRestrictionComp.{u + 1, u, u + 1, u + 2}
            (J := ProEt.topology T) a b)) := by
    unfold PurCompactSupport.tensorComposition
    rw [derived_restriction_comp_eq, adjoint_comp_side]
  have hs : scalarHomExtensionComp (m T) a b =
      (((m T).scalar a).adjunction.comp ((m T).scalar b).adjunction).leftAdjointUniq
        (((m T).scalar (a ≫ b)).adjunction.ofNatIsoRight
          (scalarHomRestrictionComp.{u + 1, u, u + 1, u + 2}
            (J := ProEt.topology T) a b)) := by
    unfold scalarHomExtensionComp
    rfl
  have he := adjoint_comp_transport
    ((m T).scalar a).adjunction (pbcDerivedScalarAdjunction a)
    ((m T).scalar b).adjunction (pbcDerivedScalarAdjunction b)
    ((m T).scalar (a ≫ b)).adjunction (pbcDerivedScalarAdjunction (a ≫ b))
    (scalarHomRestrictionComp.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) a b).symm K
  rw [adjoint_comp_side, adjoint_comp_side] at he
  have hh := congrArg (fun e ↦
      (((m T).scalar b).adjunction.leftAdjointUniq
        (pbcDerivedScalarAdjunction b)).hom.app (((m T).scalar a).derived.obj K) ≫
      (pbcDerivedExtend b).map
      ((((m T).scalar a).adjunction.leftAdjointUniq
        (pbcDerivedScalarAdjunction a)).hom.app K) ≫ e.hom.app K) hc
  rw [← hs] at he
  exact he.trans hh.symm
private theorem transport_comparison_comp
    {XA XB XC YA YB YC : Type*}
    [Category XA] [Category XB] [Category XC]
    [Category YA] [Category YB] [Category YC]
    (P : XA ⥤ YA) (Q : XB ⥤ YB) (R : XC ⥤ YC)
    {F F' : XA ⥤ XB} {G G' : XB ⥤ XC} {H H' : XA ⥤ XC}
    {U U' : YA ⥤ YB} {V V' : YB ⥤ YC} {W W' : YA ⥤ YC}
    (aF : F ≅ F') (aG : G ≅ G') (aH : H ≅ H')
    (aU : U ≅ U') (aV : V ≅ V') (aW : W ≅ W')
    (ca : P ⋙ U' ⟶ F' ⋙ Q) (cb : Q ⋙ V' ⟶ G' ⋙ R)
    (cc : P ⋙ W' ⟶ H' ⋙ R)
    (x : F ⋙ G ≅ H) (y : U ⋙ V ≅ W)
    (x' : F' ⋙ G' ≅ H') (y' : U' ⋙ V' ≅ W')
    (K : XA)
    (hx : x.hom.app K ≫ aH.hom.app K =
      aG.hom.app (F.obj K) ≫ G'.map (aF.hom.app K) ≫ x'.hom.app K)
    (hy : y.hom.app (P.obj K) ≫ aW.hom.app (P.obj K) =
      aV.hom.app (U.obj (P.obj K)) ≫ V'.map (aU.hom.app (P.obj K)) ≫
        y'.hom.app (P.obj K))
    (hc : V'.map (ca.app K) ≫ cb.app (F'.obj K) ≫ R.map (x'.hom.app K) =
      y'.hom.app (P.obj K) ≫ cc.app K) :
    V.map (aU.hom.app (P.obj K) ≫ ca.app K ≫ Q.map (aF.inv.app K)) ≫
      (aV.hom.app (Q.obj (F.obj K)) ≫ cb.app (F.obj K) ≫
        R.map (aG.inv.app (F.obj K))) ≫ R.map (x.hom.app K) =
    y.hom.app (P.obj K) ≫ aW.hom.app (P.obj K) ≫ cc.app K ≫
      R.map (aH.inv.app K) := by
  have hn := aV.hom.naturality
    (aU.hom.app (P.obj K) ≫ ca.app K ≫ Q.map (aF.inv.app K))
  simp only [Functor.map_comp, Category.assoc] at hn
  have hn' := cb.naturality (aF.inv.app K)
  dsimp only [Functor.comp_map] at hn'
  apply (cancel_mono (R.map (aH.hom.app K))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [reassoc_of% hn']
  simp only [← Functor.map_comp, Category.assoc]
  rw [hx]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc, Category.comp_id]
  rw [hc, reassoc_of% hy]
  erw [Category.comp_id]
/-- The specified support comparison respects coefficient composition.
Proof: transport the canonical proper/open comparison cocycle by the unique scalar
adjunction isomorphisms. Naturality and their composite-adjunction unit equations
cancel the middle presentation changes.
Source: Stacks Tags 07A4, 07A6, 0D6D and 0E47.
(blueprint: lem-sf-concrete-projection-coefficient-coherence). -/
theorem support_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A) :
    (scalar m ψ Y).map (supportComparison m φ c K) ≫
      supportComparison m ψ c ((scalar m φ X).obj K) ≫
      (support C c).map ((scalarComp m φ ψ X).hom.app K) =
    (scalarComp m φ ψ Y).hom.app ((support A c).obj K) ≫
      supportComparison m (ψ.comp φ) c K := by
  let ca := PurCompactSupport.comparison (coefficientChange φ) c
  let cb := PurCompactSupport.comparison (coefficientChange ψ) c
  let cc := PurCompactSupport.comparison (coefficientChange (ψ.comp φ)) c
  have hmap (T : Scheme.{u}) : (coefficientChange φ).map T ≫
      (coefficientChange ψ).map T = (coefficientChange (ψ.comp φ)).map T :=
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp
      (CommRingCat.ofHom (RingHom.ulift φ)) (CommRingCat.ofHom (RingHom.ulift ψ))).symm
  have hc := PurCompactSupport.comparison_composition (coefficientChange φ)
    (coefficientChange ψ) (coefficientChange (ψ.comp φ)) hmap c K
  have he (T : Scheme.{u}) (M : proEtaleDerivedCategory T A) :=
    scalar_comp_transport_eq m T (proEtaleConstantRingMap φ) (proEtaleConstantRingMap ψ)
      (proEtaleConstantRingMap (ψ.comp φ)) (hmap T) M
  simp only [supportComparison_eq]
  exact transport_comparison_comp
    (support A c) (support B c) (support C c)
    (scalarIso m φ X) (scalarIso m ψ X) (scalarIso m (ψ.comp φ) X)
    (scalarIso m φ Y) (scalarIso m ψ Y) (scalarIso m (ψ.comp φ) Y)
    ca cb cc (scalarComp m φ ψ X) (scalarComp m φ ψ Y)
    (PurCompactSupport.tensorComposition _ _ _ (hmap X))
    (PurCompactSupport.tensorComposition _ _ _ (hmap Y)) K
    (he X K) (he Y ((support A c).obj K)) hc
private theorem adjoint_right_transport
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R S : B ⥤ A} (a : F ⊣ R) (b : G ⊣ R) (δ : R ≅ S) :
    (a.ofNatIsoRight δ).leftAdjointUniq (b.ofNatIsoRight δ) =
      a.leftAdjointUniq b := by
  apply Iso.ext
  ext K
  apply ((a.ofNatIsoRight δ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl
private theorem adjoint_identity_conjugate
    {A : Type*} [Category A] {F R : A ⥤ A} (a : F ⊣ R) (δ : R ≅ 𝟭 A) :
    (a.ofNatIsoRight δ).leftAdjointUniq Adjunction.id =
      ((conjugateIsoEquiv a Adjunction.id).symm δ).symm := by
  apply Iso.ext
  ext K
  apply ((a.ofNatIsoRight δ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply]
  have he := (unit_conjugateEquiv_symm Adjunction.id a δ.inv K).symm
  have he' : a.homEquiv _ _
      (((conjugateIsoEquiv a Adjunction.id).symm δ).inv.app K) = δ.inv.app K := by
    rw [Adjunction.homEquiv_unit]
    change a.unit.app K ≫ R.map
      (((conjugateEquiv Adjunction.id a).symm δ.inv).app K) = δ.inv.app K
    simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj,
      Category.id_comp] using he
  change Adjunction.id.unit.app K =
    a.homEquiv _ _ (((conjugateIsoEquiv a Adjunction.id).symm δ).inv.app K) ≫ _
  rw [he']
  simp
attribute [local irreducible] scalarHomExtensionId PurCompactSupport.tensorIdentity
private theorem scalar_id_transport_eq (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (K : DerivedCategory.{u + 2} (scalarModules.{u + 1, u, u + 1} (ProEt.topology T) R)) :
    (scalarHomExtensionId.{u + 1, u, u + 1, u + 2}
      (J := ProEt.topology T) (m T) R).hom.app K =
    (((m T).scalar (𝟙 R)).adjunction.leftAdjointUniq
      (pbcDerivedScalarAdjunction (𝟙 R))).hom.app K ≫
        (PurCompactSupport.tensorIdentity R).hom.app K := by
  have hr : (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose =
      scalarHomOrdinaryRestrictionId.{u + 1, u, u + 1}
        (J := ProEt.topology T) R := by
    apply (PurCompactSupport.restrictIdentity_existsUnique R).unique
    · exact (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec
    · intro M U x
      rfl
  have hd : Functor.mapDerivedCategoryNatIso
      (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose ≪≫
        Functor.mapDerivedCategoryIdIso _ =
      scalarHomRestrictionId.{u + 1, u, u + 1, u + 2}
        (J := ProEt.topology T) R := by
    rw [hr]
    rfl
  have ht : PurCompactSupport.tensorIdentity R =
      ((conjugateIsoEquiv (pbcDerivedScalarAdjunction (𝟙 R))
        (Adjunction.id : (𝟭 (DerivedCategory (pbcModules T R))) ⊣ 𝟭 _)).symm
          (scalarHomRestrictionId.{u + 1, u, u + 1, u + 2}
            (J := ProEt.topology T) R)).symm := by
    unfold PurCompactSupport.tensorIdentity
    exact congrArg (fun δ ↦
      ((conjugateIsoEquiv (pbcDerivedScalarAdjunction (𝟙 R))
        (Adjunction.id : (𝟭 (DerivedCategory (pbcModules T R))) ⊣ 𝟭 _)).symm δ).symm) hd
  rw [← adjoint_identity_conjugate] at ht
  have he := Adjunction.leftAdjointUniq_trans_app
    (((m T).scalar (𝟙 R)).adjunction.ofNatIsoRight
      (scalarHomRestrictionId.{u + 1, u, u + 1, u + 2}
        (J := ProEt.topology T) R))
    ((pbcDerivedScalarAdjunction (𝟙 R)).ofNatIsoRight
      (scalarHomRestrictionId.{u + 1, u, u + 1, u + 2}
        (J := ProEt.topology T) R)) Adjunction.id K
  rw [adjoint_right_transport] at he
  have hid : scalarHomExtensionId (m T) R =
      ((((m T).scalar (𝟙 R)).adjunction.ofNatIsoRight
        (scalarHomRestrictionId.{u + 1, u, u + 1, u + 2}
          (J := ProEt.topology T) R)).leftAdjointUniq Adjunction.id) := by
    unfold scalarHomExtensionId
    rfl
  rw [← hid] at he
  rw [← ht] at he
  exact he.symm
/-- Shield the prescribed adjunction isomorphism from kernel reduction of localizations. -/
private theorem presentation_exists (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∃! e : ((m T).scalar a).derived ≅ pbcDerivedExtend a,
      e = ((m T).scalar a).adjunction.leftAdjointUniq
        (pbcDerivedScalarAdjunction a) := by
  exact ⟨_, rfl, fun _ h ↦ h⟩
private noncomputable def presentation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ((m T).scalar a).derived ≅ pbcDerivedExtend a :=
  (presentation_exists m T a).exists.choose
private theorem presentation_eq (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    presentation m T a = ((m T).scalar a).adjunction.leftAdjointUniq
      (pbcDerivedScalarAdjunction a) :=
  (presentation_exists m T a).exists.choose_spec
private theorem transport_identity
    {D I : Type*} [Category D] (F G : I → D ⥤ D)
    (c : ∀ i, F i ≅ G i) (i₀ : I) (s : F i₀ ≅ 𝟭 D) (t : G i₀ ≅ 𝟭 D)
    (hi : s = c i₀ ≪≫ t) {i : I} (h : i = i₀) :
    eqToIso (congrArg F h) ≪≫ s =
      c i ≪≫ eqToIso (congrArg G h) ≪≫ t := by
  subst i
  simpa only [eqToIso_refl, Iso.refl_trans] using hi
private theorem scalar_id_transport_eq' (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : R ⟶ R) (h : a = 𝟙 R) :
    eqToIso (congrArg (fun z ↦ ((m T).scalar z).derived) h) ≪≫
      scalarHomExtensionId.{u + 1, u, u + 1, u + 2}
        (J := ProEt.topology T) (m T) R =
    presentation m T a ≪≫ eqToIso (congrArg (fun z ↦ pbcDerivedExtend z) h) ≪≫
      PurCompactSupport.tensorIdentity R := by
  apply transport_identity (fun z ↦ ((m T).scalar z).derived)
    (fun z ↦ pbcDerivedExtend z) (presentation m T) (𝟙 R)
    (scalarHomExtensionId (m T) R) (PurCompactSupport.tensorIdentity R) _ h
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [presentation_eq]
  exact scalar_id_transport_eq m T R K
attribute [local irreducible] scalarIso scalarId
/-- The transported scalar identity, fixed by an equality specification so that the
kernel does not reduce the equality transport. Source: Stacks 03DA, 07A6. -/
private theorem transportedIdentity_existsUnique {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ R) (h : a = 𝟙 R) :
    ∃! e : pbcDerivedExtend a ≅ 𝟭 (DerivedCategory (pbcModules W R)),
      e = eqToIso (congrArg (fun z ↦ pbcDerivedExtend z) h) ≪≫
        PurCompactSupport.tensorIdentity R :=
  ⟨_, rfl, fun _ h ↦ h⟩
private noncomputable def transportedIdentity {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ R) (h : a = 𝟙 R) :
    pbcDerivedExtend a ≅ 𝟭 (DerivedCategory (pbcModules W R)) :=
  (transportedIdentity_existsUnique a h).exists.choose
private theorem transportedIdentity_eq {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ R) (h : a = 𝟙 R) :
    transportedIdentity a h =
      eqToIso (congrArg (fun z ↦ pbcDerivedExtend z) h) ≪≫
        PurCompactSupport.tensorIdentity R :=
  (transportedIdentity_existsUnique a h).exists.choose_spec
/-- `PurCompactSupport.comparison_identity`, restated with the specified transported identity. -/
private theorem comparison_identity_transported {R : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R R)
    (h : ∀ W : Scheme.{u}, a.map W = 𝟙 (R.ring W))
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (PurCompactSupport.comparison a c).app M ≫ (PurCompactSupport.image R c).map
        ((transportedIdentity (a.map X) (h X)).hom.app M) =
      (transportedIdentity (a.map Y) (h Y)).hom.app
        ((PurCompactSupport.image R c).obj M) := by
  rw [transportedIdentity_eq, transportedIdentity_eq]
  exact PurCompactSupport.comparison_identity a h c M
private theorem scalarIso_presentation (A : Type u) [CommRing A] (T : Scheme.{u}) :
    scalarIso m (RingHom.id A) T =
      presentation m T (proEtaleConstantRingMap (RingHom.id A)) := by
  unfold scalarIso
  exact (presentation_eq m T (proEtaleConstantRingMap (RingHom.id A))).symm
private theorem scalarId_presentation (A : Type u) [CommRing A] (T : Scheme.{u}) :
    scalarId m A T = scalarIso m (RingHom.id A) T ≪≫
      transportedIdentity (proEtaleConstantRingMap (RingHom.id A))
        ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id
          (CommRingCat.of (ULift.{u + 1, u} A))) := by
  have h := scalar_id_transport_eq' m T (proEtaleConstantRing T A)
    (proEtaleConstantRingMap (RingHom.id A))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))
  rw [← scalarIso_presentation m A T] at h
  rw [scalarId_eq, transportedIdentity_eq]
  exact h

private theorem identity_paste
    {A B : Type*} [Category A] [Category B] (P : A ⥤ B)
    {F F' : A ⥤ A} {G G' : B ⥤ B}
    (a : F ≅ F') (b : G ≅ G') (c : P ⋙ G' ⟶ F' ⋙ P)
    (s : F ≅ 𝟭 A) (t : G ≅ 𝟭 B)
    (s' : F' ≅ 𝟭 A) (t' : G' ≅ 𝟭 B)
    (hs : s = a ≪≫ s') (ht : t = b ≪≫ t')
    (K : A) (hc : c.app K ≫ P.map (s'.hom.app K) = t'.hom.app (P.obj K)) :
    (b.hom.app (P.obj K) ≫ c.app K ≫ P.map (a.inv.app K)) ≫
      P.map (s.hom.app K) = t.hom.app (P.obj K) := by
  rw [hs, ht]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← P.map_comp_assoc, Iso.inv_hom_id_app, P.map_id, Category.id_comp, hc]

/-- The specified support comparison respects the scalar identity unitor.
Proof: transport the canonical identity mate through the unique scalar adjunction
isomorphism. The conjugate of the identity restriction is the scalar unitor.
Source: Stacks Tags 07A4, 07A6, 0D6D and 0E47.
(blueprint: lem-sf-concrete-projection-coefficient-coherence). -/
theorem support_id (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    supportComparison m (RingHom.id A) c K ≫
      (support A c).map ((scalarId m A X).hom.app K) =
    (scalarId m A Y).hom.app ((support A c).obj K) := by
  rw [supportComparison_eq]
  let hm (T : Scheme.{u}) :=
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A))
  exact identity_paste (support A c)
    (scalarIso m (RingHom.id A) X) (scalarIso m (RingHom.id A) Y)
    (PurCompactSupport.comparison (coefficientChange (RingHom.id A)) c)
    (scalarId m A X) (scalarId m A Y)
    (transportedIdentity _ (hm X))
    (transportedIdentity _ (hm Y))
    (scalarId_presentation m A X) (scalarId_presentation m A Y) K
    (comparison_identity_transported (coefficientChange (RingHom.id A)) hm c K)

private theorem tensor_comparison_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (ta : TA ⋙ F ⟶ F.prod F ⋙ TB) (tb : TB ⋙ G ⟶ G.prod G ⋙ TC)
    (th : TA ⋙ H ⟶ H.prod H ⋙ TC) (x : F ⋙ G ⟶ H)
    (K P : A) (Q : B) (R : C) (a : F.obj P ⟶ Q) (b : G.obj Q ⟶ R)
    (d : H.obj P ⟶ R)
    (hc : G.map (ta.app (K, P)) ≫ tb.app (F.obj K, F.obj P) ≫
      TC.map (Prod.mkHom (x.app K) (x.app P)) = x.app (TA.obj (K, P)) ≫
        th.app (K, P))
    (hd : G.map a ≫ b = x.app P ≫ d) :
    G.map (ta.app (K, P) ≫ TB.map (Prod.mkHom (𝟙 (F.obj K)) a)) ≫
      tb.app (F.obj K, Q) ≫ TC.map (Prod.mkHom (x.app K) b) =
    x.app (TA.obj (K, P)) ≫ th.app (K, P) ≫
      TC.map (Prod.mkHom (𝟙 (H.obj K)) d) := by
  have hn := tb.naturality (Prod.mkHom (𝟙 (F.obj K)) a)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp, CategoryTheory.prod_comp, Functor.map_id,
    Category.id_comp, Category.assoc]
  rw [hd]
  rw [G.map_id, Category.id_comp]
  have hp : Prod.mkHom (x.app K) (x.app P ≫ d) =
      Prod.mkHom (x.app K) (x.app P) ≫ Prod.mkHom (𝟙 _) d := by simp
  rw [hp, Functor.map_comp, reassoc_of% hc]
/-- The tensor/pullback input comparison respects coefficient composition.
Proof: use naturality of the scalar tensor comparison, its coefficient composition
equation, and scalar/pullback coefficient coherence. Functoriality combines the
two tensor factors into the displayed pair of scalar compositors.
Source: Stacks Tags 07A4, 07A6, 0D6D and 0E47.
(blueprint: lem-sf-concrete-projection-coefficient-coherence). -/
theorem input_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (scalar m ψ X).map (inputComparison m choices φ f K L).hom ≫
      (inputComparison m choices ψ f ((scalar m φ X).obj K)
        ((scalar m φ Y).obj L)).hom ≫
      (tensor m C X).map (Prod.mkHom ((scalarComp m φ ψ X).hom.app K)
        ((constantPullback (A := C) f).map ((scalarComp m φ ψ Y).hom.app L))) =
      (scalarComp m φ ψ X).hom.app (input m A f K L) ≫
        (inputComparison m choices (ψ.comp φ) f K L).hom := by
  obtain ⟨coh⟩ := scalar_pullback_coefficient_coherence m
  have hl := coh.composition φ ψ f L
  have ht := tensor_comp m choices φ ψ X K ((constantPullback (A := A) f).obj L)
  have hh := tensor_comparison_comp
    (scalar m φ X) (scalar m ψ X) (scalar m (ψ.comp φ) X)
    (tensor m A X) (tensor m B X) (tensor m C X)
    (choices.scalarTensor φ X).iso.hom (choices.scalarTensor ψ X).iso.hom
    (choices.scalarTensor (ψ.comp φ) X).iso.hom (scalarComp m φ ψ X).hom
    K ((constantPullback (A := A) f).obj L)
    ((constantPullback (A := B) f).obj ((scalar m φ Y).obj L))
    ((constantPullback (A := C) f).obj ((scalar m (ψ.comp φ) Y).obj L))
    ((lambda m φ f).inv.app L)
    ((lambda m ψ f).inv.app ((scalar m φ Y).obj L) ≫
      (constantPullback (A := C) f).map ((scalarComp m φ ψ Y).hom.app L))
    ((lambda m (ψ.comp φ) f).inv.app L) ht hl
  simpa only [inputComparison, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, ← Functor.map_comp,
    CategoryTheory.prod_comp, Category.id_comp] using hh
/-- The tensor/pullback input comparison respects the scalar identity unitor.
Proof: expand the input comparison. Scalar/pullback identity coherence simplifies
the second tensor factor; the scalar tensor identity gives the result.
Source: Stacks Tags 07A4, 07A6, 0D6D and 0E47.
(blueprint: lem-sf-concrete-projection-coefficient-coherence). -/
theorem input_id (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (inputComparison m choices (RingHom.id A) f K L).hom ≫
      (tensor m A X).map (Prod.mkHom ((scalarId m A X).hom.app K)
        ((constantPullback (A := A) f).map ((scalarId m A Y).hom.app L))) =
      (scalarId m A X).hom.app (input m A f K L) := by
  obtain ⟨coh⟩ := scalar_pullback_coefficient_coherence m
  have hl := coh.identity A f L
  have ht := tensor_id m choices A X K ((constantPullback (A := A) f).obj L)
  simpa only [inputComparison, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.id_comp, hl] using ht
end WeilConjectures.ConcreteProjectionReduction
